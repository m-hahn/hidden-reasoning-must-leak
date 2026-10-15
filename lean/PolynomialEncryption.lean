import Encryption
import Autoregressive
import ConcreteReasoning
import Mathlib.Data.Finset.Max

/-!
# Privacy from the stated nonuniform PRG assumption

This file constructs the circuit reductions needed to use
`NC0GeneratorFamily.IsPseudorandom` directly.  Prefix restriction is wiring;
XOR with a fixed plaintext uses at most one NOT gate per trace bit.  A
maximizing plaintext at each length is nonuniform advice.  Security of that
single polynomial circuit family yields a uniform negligible error for all
plaintexts, hence the arbitrary-distribution prediction guarantee.
-/

noncomputable section
open scoped BigOperators

namespace PolynomialEncryption

open TransformerAC0 Encryption

def xorCircuit (message : Bits n) : Circuit n n :=
  .bundle fun index => if message index then
    .seq (.wire fun _ => index) .notGate
  else .wire fun _ => index

@[simp] theorem eval_xorCircuit (message input : Bits n) :
    Circuit.eval (xorCircuit message) input = bitXor message input := by
  funext index
  cases h : message index <;> simp [xorCircuit, Circuit.eval, bitXor, h]

theorem xorCircuit_gateCount_le (message : Bits n) :
    Circuit.gateCount (xorCircuit message) ≤ n := by
  unfold xorCircuit
  simp only [Circuit.gateCount]
  calc
    (∑ index : Fin n, Circuit.gateCount
        (if message index then .seq (.wire fun _ => index) .notGate else .wire fun _ => index)) ≤
        ∑ _index : Fin n, 1 := by
          apply Finset.sum_le_sum
          intro index _
          cases message index <;> simp [Circuit.gateCount]
    _ = n := by simp

def reduction (message : Bits front) (monitor : Circuit front 1) :
    Circuit (front + suffix) 1 :=
  .seq (.wire fun index => Fin.castLE (Nat.le_add_right front suffix) index)
    (.seq (xorCircuit message) monitor)

@[simp] theorem eval_reduction (message : Bits front) (monitor : Circuit front 1)
    (input : Bits (front + suffix)) :
    Circuit.eval (reduction message monitor) input 0 =
      Circuit.eval monitor (bitXor message
        (Fin.take front (Nat.le_add_right front suffix) input)) 0 := by
  simp only [reduction, Circuit.eval, eval_xorCircuit]
  rfl

theorem reduction_gateCount_le (message : Bits front) (monitor : Circuit front 1) :
    Circuit.gateCount (reduction (suffix := suffix) message monitor) ≤
      front + Circuit.gateCount monitor := by
  simpa [reduction, Circuit.gateCount] using
    Nat.add_le_add_right (xorCircuit_gateCount_le message) (Circuit.gateCount monitor)

/-- Prefix and plaintext-XOR reduction with explicit polynomial witnesses. -/
def reductionFamily
    {front suffix : ℕ → ℕ}
    (monitor : PolynomialMonitorFamily front) (message : ∀ n, Bits (front n))
    (traceCoefficient traceExponent : ℕ)
    (traceLength : ∀ n, front n ≤ traceCoefficient * (n + 1) ^ traceExponent) :
    PolynomialMonitorFamily (fun n => front n + suffix n) where
  circuit := fun n => reduction (message n) (monitor.circuit n)
  coefficient := traceCoefficient + monitor.coefficient
  exponent := traceExponent + monitor.exponent
  size_le := by
    intro n
    apply (reduction_gateCount_le (message n) (monitor.circuit n)).trans
    calc
      front n + Circuit.gateCount (monitor.circuit n) ≤
          traceCoefficient * (n + 1) ^ traceExponent +
            monitor.coefficient * (n + 1) ^ monitor.exponent :=
        Nat.add_le_add (traceLength n) (monitor.size_le n)
      _ ≤ traceCoefficient * (n + 1) ^ (traceExponent + monitor.exponent) +
            monitor.coefficient * (n + 1) ^ (traceExponent + monitor.exponent) := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ = (traceCoefficient + monitor.coefficient) *
          (n + 1) ^ (traceExponent + monitor.exponent) := by ring

/-- A single negligible error bounds every plaintext at every input length.
Only the PRG assumption is imported; closure under prefix restriction and XOR
is proved by the explicit circuit construction. -/
theorem pointwise_security_finite
    {Input : ℕ → Type*} [∀ n, Fintype (Input n)] [∀ n, Nonempty (Input n)]
    {seedLength front suffix : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLength (fun n => front n + suffix n))
    (secure : generator.IsPseudorandom)
    (plainTrace : ∀ n, Input n → Bits (front n))
    (monitor : PolynomialMonitorFamily front)
    (traceCoefficient traceExponent : ℕ)
    (traceLength : ∀ n, front n ≤ traceCoefficient * (n + 1) ^ traceExponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n input,
      distinguishingAdvantage
        (encryptedTrace (plainTrace n) (prefixGenerator (generator.generator n).generate) input)
        (monitor.monitor n) ≤ error n := by
  classical
  let advantage : (n : ℕ) → Input n → ℝ := fun n input =>
    distinguishingAdvantage
      (encryptedTrace (plainTrace n) (prefixGenerator (generator.generator n).generate) input)
      (monitor.monitor n)
  have hmax : ∀ n, ∃ chosen : Input n, ∀ input, advantage n input ≤ advantage n chosen := by
    intro n
    obtain ⟨chosen, _, hchosen⟩ := Finset.exists_max_image Finset.univ (advantage n)
      Finset.univ_nonempty
    exact ⟨chosen, fun input => hchosen input (by simp)⟩
  let chosen : ∀ n, Input n := fun n => Classical.choose (hmax n)
  let reduced := reductionFamily (suffix := suffix) monitor
    (fun n => plainTrace n (chosen n)) traceCoefficient traceExponent traceLength
  obtain ⟨error, hnegligible, hsecure⟩ := secure reduced
  refine ⟨error, hnegligible, ?_⟩
  intro n input
  have hchosen := Classical.choose_spec (hmax n) input
  have hreduce : distinguishingAdvantage (generator.generator n).generate (reduced.monitor n) =
      advantage n (chosen n) := by
    unfold distinguishingAdvantage samplerAcceptance
    have hmonitor : reduced.monitor n = fun output => (monitor.monitor n)
        (bitXor (plainTrace n (chosen n))
          (Fin.take (front n) (Nat.le_add_right (front n) (suffix n)) output)) := by
      funext output
      simp [reduced, reductionFamily, PolynomialMonitorFamily.monitor]
    rw [hmonitor]
    rw [show uniformAcceptance (fun output : Bits (front n + suffix n) =>
          (monitor.monitor n) (bitXor (plainTrace n (chosen n))
            (Fin.take (front n) (Nat.le_add_right (front n) (suffix n)) output))) =
        uniformAcceptance (fun pad => (monitor.monitor n) (bitXor (plainTrace n (chosen n)) pad)) from
      uniformAcceptance_take (front n) (suffix n)
        (fun pad => (monitor.monitor n) (bitXor (plainTrace n (chosen n)) pad))]
    rw [uniformAcceptance_xor]
    rfl
  have hsecure_n := hsecure n
  rw [hreduce] at hsecure_n
  exact hchosen.trans hsecure_n

theorem pointwise_security
    {inputLength seedLength front suffix : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLength (fun n => front n + suffix n))
    (secure : generator.IsPseudorandom)
    (plainTrace : ∀ n, Bits (inputLength n) → Bits (front n))
    (monitor : PolynomialMonitorFamily front) (traceCoefficient traceExponent : ℕ)
    (traceLength : ∀ n, front n ≤ traceCoefficient * (n + 1) ^ traceExponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n input,
      distinguishingAdvantage
        (encryptedTrace (plainTrace n) (prefixGenerator (generator.generator n).generate) input)
        (monitor.monitor n) ≤ error n :=
  pointwise_security_finite generator secure plainTrace monitor traceCoefficient traceExponent traceLength

/-- The same reduction covers the full task input alphabets, not only a
Boolean restriction of those inputs. -/
theorem no_readability_finite
    {Input : ℕ → Type*} [∀ n, Fintype (Input n)] [∀ n, Nonempty (Input n)]
    {seedLength front suffix : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLength (fun n => front n + suffix n))
    (secure : generator.IsPseudorandom) (plainTrace : ∀ n, Input n → Bits (front n))
    (monitor : PolynomialMonitorFamily front) (traceCoefficient traceExponent : ℕ)
    (traceLength : ∀ n, front n ≤ traceCoefficient * (n + 1) ^ traceExponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧
      ∀ n (distribution : FiniteDistribution (Input n)) (predicate : Input n → Bool),
        predictionSuccess distribution
          (encryptedTrace (plainTrace n) (prefixGenerator (generator.generator n).generate))
          (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  obtain ⟨error, hnegligible, hpointwise⟩ := pointwise_security_finite generator secure plainTrace monitor
    traceCoefficient traceExponent traceLength
  refine ⟨error, hnegligible, ?_⟩
  intro n distribution predicate
  exact prediction_le_prior distribution _ (monitor.monitor n) predicate (error n) (hpointwise n)

/-- The paper's privacy guarantee for every polynomial circuit monitor,
arbitrary finite input distribution, and arbitrary input predicate. -/
theorem no_readability
    {inputLength seedLength front suffix : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLength (fun n => front n + suffix n))
    (secure : generator.IsPseudorandom)
    (plainTrace : ∀ n, Bits (inputLength n) → Bits (front n))
    (monitor : PolynomialMonitorFamily front)
    (traceCoefficient traceExponent : ℕ)
    (traceLength : ∀ n, front n ≤ traceCoefficient * (n + 1) ^ traceExponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧
      ∀ n (D : FiniteDistribution (Bits (inputLength n))) (predicate : Bits (inputLength n) → Bool),
        predictionSuccess D
          (encryptedTrace (plainTrace n) (prefixGenerator (generator.generator n).generate))
          (monitor.monitor n) predicate ≤ D.bestConstantSuccess predicate + error n := by
  obtain ⟨error, hnegligible, hpointwise⟩ := pointwise_security generator secure plainTrace monitor
    traceCoefficient traceExponent traceLength
  refine ⟨error, hnegligible, ?_⟩
  intro n D predicate
  apply prediction_le_prior D _ (monitor.monitor n) predicate (error n)
  intro input
  exact hpointwise n input

/-- Information leakage and cryptographic privacy of the same concrete
ciphertext distribution.  Both conclusions refer to the trace generated by
`models`, XOR-encrypted by the specified PRG prefix.  The only research inputs
are Tal and PRG security. -/
theorem leakage_and_privacy
    {inputLength seedLength front suffix : ℕ → ℕ}
    (tal : Tal.FourierTailTheorem)
    (models : ∀ n, Autoregressive.FixedPrecisionGenerator (inputLength n) (front n))
    (correct : ∀ n input, (models n).answer input = Tal.parity input)
    (hinput : ∀ n, 1 ≤ inputLength n)
    (generator : NC0GeneratorFamily seedLength (fun n => front n + suffix n))
    (secure : generator.IsPseudorandom)
    (monitor : PolynomialMonitorFamily front)
    (traceCoefficient traceExponent : ℕ)
    (traceLength : ∀ n, front n ≤ traceCoefficient * (n + 1) ^ traceExponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n,
      (-Real.logb 2 (Real.sqrt (Tal.tailBound (models n).explicitFiberDepth
          (models n).explicitFiberSize (inputLength n))) - (seedLength n : ℝ) ≤
        (FiniteInformation.Distribution.uniform
          (Bits (inputLength n) × Bits (seedLength n))).mutualInformation Prod.fst
          (fun pair => encryptedTrace (models n).transcript
            (prefixGenerator (generator.generator n).generate) pair.1 pair.2)) ∧
      ∀ (D : FiniteDistribution (Bits (inputLength n))) (predicate : Bits (inputLength n) → Bool),
        predictionSuccess D
          (encryptedTrace (models n).transcript (prefixGenerator (generator.generator n).generate))
          (monitor.monitor n) predicate ≤ D.bestConstantSuccess predicate + error n := by
  obtain ⟨error, hnegligible, hprivacy⟩ := no_readability generator secure
    (fun n => (models n).transcript) monitor traceCoefficient traceExponent traceLength
  refine ⟨error, hnegligible, ?_⟩
  intro n
  exact ⟨ConcreteReasoning.encrypted_autoregressive_footprint tal (models n) (correct n)
    (prefixGenerator (generator.generator n).generate) (hinput n), hprivacy n⟩

end PolynomialEncryption
