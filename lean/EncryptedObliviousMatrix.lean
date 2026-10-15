import EncryptedMatrix
import ObliviousMatrix

/-!
# Actual encrypted matrix execution of fixed-address programs

The plaintext recurrence is derived from the last-write schedule of the
program. The encrypted numerical Transformer initializes only initial
memory observations, constant control, and raw seed bits. Its finite local
map performs decryption, one instruction, and encryption during generation.
-/

noncomputable section
namespace EncryptedObliviousMatrix
open TransformerAC0 Encryption ObliviousProgram

variable {Input Address Control Symbol : Type*}
variable [DecidableEq Address] [Fintype Control] [Fintype Symbol]
variable [Inhabited Control] [Inhabited Symbol]

def schedule (program : Program Input Address Control Symbol) (steps : ℕ) :
    RoutedSchedule.Schedule (ObliviousMatrix.front steps) steps 2 (ObliviousMatrix.opcodes Control Symbol) :=
  RoutedSchedule.ofPlan (ObliviousMatrix.plan program steps)
    (by unfold ObliviousMatrix.front; omega) (by unfold ObliviousMatrix.front ObliviousMatrix.window; omega)

/-- The schedule computes the source program's actual event trace, rather
than assuming an abstract plaintext simulator is already correct. -/
theorem token_correct (program : Program Input Address Control Symbol) (steps : ℕ)
    (input : Input) (time : Fin (steps + 1)) :
    RoutedSchedule.token (schedule program steps) ObliviousMatrix.transition
      (ObliviousMatrix.prompt program steps input) time =
        ObliviousMatrix.traceEncoding (program.traceToken input time.val) := by
  unfold schedule
  rw [RoutedSchedule.token_ofPlan _ _ ObliviousMatrix.vocabulary_positive ObliviousMatrix.opcodes_positive]
  exact ObliviousMatrix.routed_correct program steps input time

def model (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool)
    (generator : LocalGenerator seedLength
      (steps * ObliviousMatrix.vocabulary Control Symbol + ObliviousMatrix.vocabulary Control Symbol) locality) :=
  EncryptedMatrix.model (schedule program steps) ObliviousMatrix.vocabulary_positive
    ObliviousMatrix.transition (ObliviousMatrix.label finish) generator

def inputEncoding (program : Program Input Address Control Symbol) (steps : ℕ)
    (input : Input) (seed : Bits seedLength) :=
  RoutedMatrix.promptInput (EncryptedMatrix.prompt (ObliviousMatrix.prompt program steps input) seed)

theorem output_correct (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool)
    (generator : LocalGenerator seedLength
      (steps * ObliviousMatrix.vocabulary Control Symbol + ObliviousMatrix.vocabulary Control Symbol) locality)
    (input : Input) (seed : Bits seedLength) :
    (model program steps finish generator).answer (inputEncoding program steps input seed) =
      finish (program.configurationAt input (steps + 1)).control := by
  unfold model inputEncoding
  rw [EncryptedMatrix.output_correct, token_correct]
  simp only [ObliviousMatrix.label, ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply,
    ObliviousMatrix.controlOf, Program.traceToken_control, Fin.val_last]

def plainTranscript (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input) :
    Bits (steps * ObliviousMatrix.vocabulary Control Symbol) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  RoutedMatrix.indicator (ObliviousMatrix.traceEncoding (program.traceToken input pair.1.val)) pair.2

theorem plainTranscript_correct (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input) :
    EncryptedMatrix.plainTranscript (schedule program steps) ObliviousMatrix.transition
      (ObliviousMatrix.prompt program steps input) = plainTranscript program steps input := by
  funext wire
  simp only [EncryptedMatrix.plainTranscript, token_correct, plainTranscript]
  rfl

/-- Equality for the ciphertext actually emitted by the matrix driver.
There is no postprocessing assumption in the construction. -/
theorem transcript_eq_encryptedTrace (program : Program Input Address Control Symbol) (steps : ℕ)
    (finish : Control → Bool)
    (generator : LocalGenerator seedLength
      (steps * ObliviousMatrix.vocabulary Control Symbol + ObliviousMatrix.vocabulary Control Symbol) locality)
    (input : Input) (seed : Bits seedLength) :
    EncryptedMatrix.transcript (schedule program steps) ObliviousMatrix.vocabulary_positive
      ObliviousMatrix.transition (ObliviousMatrix.label finish) generator
      (ObliviousMatrix.prompt program steps input) seed =
        encryptedTrace (plainTranscript program steps)
          (prefixGenerator generator.generate) input seed := by
  simp_rw [EncryptedMatrix.transcript_eq_encryptedTrace, encryptedTrace, plainTranscript_correct]

theorem no_readability
    {inputLength seedLengths times : ℕ → ℕ}
    (programs : ∀ n, Program (Bits (inputLength n)) Address Control Symbol)
    (finish : Control → Bool)
    (generator : NC0GeneratorFamily seedLengths
      (fun n => times n * ObliviousMatrix.vocabulary Control Symbol + ObliviousMatrix.vocabulary Control Symbol))
    (secure : generator.IsPseudorandom)
    (monitor : PolynomialMonitorFamily (fun n => times n * ObliviousMatrix.vocabulary Control Symbol))
    (coefficient exponent : ℕ)
    (traceLength : ∀ n, times n * ObliviousMatrix.vocabulary Control Symbol ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits (inputLength n))) (predicate : Bits (inputLength n) → Bool),
      predictionSuccess distribution
        (fun input seed => EncryptedMatrix.transcript (schedule (programs n) (times n))
          ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition (ObliviousMatrix.label finish)
          (generator.generator n) (ObliviousMatrix.prompt (programs n) (times n) input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n :=
  EncryptedMatrix.no_readability (fun n => schedule (programs n) (times n))
    ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition (ObliviousMatrix.label finish)
    (fun n input => ObliviousMatrix.prompt (programs n) (times n) input)
    generator secure monitor coefficient exponent traceLength

end EncryptedObliviousMatrix
