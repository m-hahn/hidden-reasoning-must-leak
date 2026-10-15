import EncryptedReadout

/-!
# Whole-word privacy on arbitrary finite input alphabets

The nonuniform security reduction maximizes over every input in the full
finite alphabet. No Boolean-subalphabet assumption is made here.
-/

noncomputable section
namespace ProtocolSerialization
open TransformerAC0 Encryption
variable {Input : ℕ → Type*} [∀ n, Fintype (Input n)] [∀ n, Nonempty (Input n)]
variable {seedLengths fronts times heads opcodes codeWidth : ℕ → ℕ}

theorem no_readability_finite {seedLengths fronts times : ℕ → ℕ} {heads opcodes codeWidth : ℕ}
    (schedules : ∀ n, RoutedSchedule.Schedule (fronts n) (times n) heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (prompts : ∀ n, Input n → Fin (fronts n) → Fin 2)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n + 1)) (secure : generator.IsPseudorandom)
    (encoding : Encoding codeWidth) (monitor : PolynomialMonitorFamily (fun n => (times n + 1) * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Input n)) (predicate : Input n → Bool),
      predictionSuccess distribution
        (fun input seed => transcript (schedules n) transition label (generator.generator n) encoding (prompts n input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  obtain ⟨error, hnegligible, hprivacy⟩ := PolynomialEncryption.no_readability_finite
    (suffix := fun _ => 1) generator secure
    (fun n input => EncryptedBinaryMatrix.plainTranscript (schedules n) transition (prompts n input))
    (pullbackMonitor encoding monitor coefficient exponent timeLength) coefficient exponent timeLength
  refine ⟨error, hnegligible, ?_⟩
  intro n distribution predicate
  simpa only [predictionSuccess, transcript_eq_encode, ProtocolEncryptedBinary.transcript_eq_original,
    EncryptedBinaryMatrix.transcript_eq_encryptedTrace, pullback_monitor] using hprivacy n distribution predicate

end ProtocolSerialization

namespace EncryptedReadout
open TransformerAC0 Encryption RoutedSchedule

theorem no_readability_finite {Input : ℕ → Type*} [∀ n, Fintype (Input n)] [∀ n, Nonempty (Input n)]
    {seedLengths fronts times extras : ℕ → ℕ} {heads opcodes width codeWidth : ℕ}
    (originals : ∀ n, Schedule (fronts n) (times n) heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (sources : ∀ n, Fin (extras n + 1) → Fin width → Fin (times n)) (decode : Bits width → Bool)
    (prompts : ∀ n, Input n → Fin (fronts n) → Fin 2)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n + 1)) (secure : generator.IsPseudorandom)
    (encoding : ProtocolSerialization.Encoding codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (times n + 1) * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Input n)) (predicate : Input n → Bool),
      predictionSuccess distribution
        (fun input seed => encodedTrace (originals n) originalTransition (generator.generator n) (sources n) decode encoding (prompts n input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  simp_rw [encodedTrace_eq_original]
  exact ProtocolSerialization.no_readability_finite originals originalTransition (fun _ => false) prompts generator secure
    encoding monitor coefficient exponent timeLength

end EncryptedReadout
