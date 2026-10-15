import PolynomialEncryption

/-!
# Derived security of arbitrary length-bounded PRG prefixes

The output budget may be a rounded power stretch rather than an exact
trace-length sum. Prefix restriction is free wiring; its security follows
from the full-output PRG assumption with the same polynomial monitor budget.
-/

noncomputable section
namespace PRGRestriction
open TransformerAC0 Encryption

def restrict (generator : LocalGenerator seedLength outputLength locality) (bounded : required ≤ outputLength) :
    LocalGenerator seedLength required locality where
  generate seed wire := generator.generate seed (Fin.castLE bounded wire)
  dependency wire index := generator.dependency (Fin.castLE bounded wire) index
  locality_correct wire first second hagree := generator.locality_correct (Fin.castLE bounded wire) first second hagree

theorem uniformAcceptance_restrict {required outputLength : ℕ} (bounded : required ≤ outputLength)
    (monitor : Bits required → Bool) :
    uniformAcceptance (fun word : Bits outputLength => monitor (fun wire => word (Fin.castLE bounded wire))) = uniformAcceptance monitor := by
  generalize hsuffix : outputLength - required = suffix
  have heq : outputLength = required + suffix := by omega
  subst outputLength
  exact uniformAcceptance_take required suffix monitor

def family {seedLengths outputLengths required : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths) (bounded : ∀ n, required n ≤ outputLengths n) :
    NC0GeneratorFamily seedLengths required where
  locality := generator.locality
  generator n := restrict (generator.generator n) (bounded n)

def liftedMonitor {outputLengths required : ℕ → ℕ} (bounded : ∀ n, required n ≤ outputLengths n)
    (monitor : PolynomialMonitorFamily required) : PolynomialMonitorFamily outputLengths where
  circuit n := .seq (.wire (Fin.castLE (bounded n))) (monitor.circuit n)
  coefficient := monitor.coefficient
  exponent := monitor.exponent
  size_le n := by simpa only [Circuit.gateCount, Nat.zero_add] using monitor.size_le n

theorem advantage_restrict {seedLengths outputLengths required : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths) (bounded : ∀ n, required n ≤ outputLengths n)
    (monitor : PolynomialMonitorFamily required) (n : ℕ) :
    distinguishingAdvantage ((family generator bounded).generator n).generate (monitor.monitor n) =
      distinguishingAdvantage (generator.generator n).generate ((liftedMonitor bounded monitor).monitor n) := by
  change |uniformAcceptance (fun seed => monitor.monitor n (fun wire => (generator.generator n).generate seed (Fin.castLE (bounded n) wire))) -
      uniformAcceptance (monitor.monitor n)| =
    |uniformAcceptance (fun seed => monitor.monitor n (fun wire => (generator.generator n).generate seed (Fin.castLE (bounded n) wire))) -
      uniformAcceptance (fun word : Bits (outputLengths n) => monitor.monitor n (fun wire => word (Fin.castLE (bounded n) wire)))|
  rw [uniformAcceptance_restrict]

/-- Security of the original full stretch implies security of the exact
prefix used by the constructed encrypted matrix, with no new assumption. -/
theorem secure {seedLengths outputLengths required : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths) (secure : generator.IsPseudorandom)
    (bounded : ∀ n, required n ≤ outputLengths n) : (family generator bounded).IsPseudorandom := by
  intro monitor
  obtain ⟨error, hnegligible, hsecure⟩ := secure (liftedMonitor bounded monitor)
  refine ⟨error, hnegligible, ?_⟩
  intro n
  rw [advantage_restrict]
  exact hsecure n

end PRGRestriction
