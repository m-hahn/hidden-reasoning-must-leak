import EncryptedBinaryMatrix
import EncryptedObliviousMatrix

/-!
# Binary plaintext and encrypted execution of fixed-address programs

The binary recurrence is connected to the program's proved event trace.
Both numerical constructions use that same literal source prompt. They
emit a fixed number of actual binary payload tokens per source event.
-/

noncomputable section
namespace BinaryObliviousMatrix
open TransformerAC0 Encryption ObliviousProgram
variable {Input Address Control Symbol : Type*}
variable [DecidableEq Address] [Fintype Control] [Fintype Symbol] [Inhabited Control] [Inhabited Symbol]

def model (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool) :=
  BinaryMatrix.model (EncryptedObliviousMatrix.schedule program steps) ObliviousMatrix.vocabulary_positive
    ObliviousMatrix.transition (ObliviousMatrix.label finish)

def inputEncoding (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input) :=
  BinaryMatrix.inputEncoding (ObliviousMatrix.prompt program steps input)

theorem output_correct (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool) (input : Input) :
    (model program steps finish).answer (inputEncoding program steps input) =
      finish (program.configurationAt input (steps + 1)).control := by
  unfold model inputEncoding
  rw [BinaryMatrix.output_correct, EncryptedObliviousMatrix.token_correct]
  simp only [ObliviousMatrix.label, ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply,
    ObliviousMatrix.controlOf, Program.traceToken_control, Fin.val_last]

def encryptedModel (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool)
    (generator : LocalGenerator seedLength (steps * ObliviousMatrix.vocabulary Control Symbol + 1) locality) :=
  EncryptedBinaryMatrix.model
    (BinarySchedule.schedule (EncryptedObliviousMatrix.schedule program steps) ObliviousMatrix.vocabulary_positive)
    (BinarySchedule.transition ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition (ObliviousMatrix.label finish))
    BinarySchedule.tokenBit generator

def encryptedInput (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input) (seed : Bits seedLength) :=
  EncryptedBinaryMatrix.inputEncoding (BinarySchedule.prompt (ObliviousMatrix.prompt program steps input)) seed

theorem encrypted_output_correct (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool)
    (generator : LocalGenerator seedLength (steps * ObliviousMatrix.vocabulary Control Symbol + 1) locality)
    (input : Input) (seed : Bits seedLength) :
    (encryptedModel program steps finish generator).answer (encryptedInput program steps input seed) =
      finish (program.configurationAt input (steps + 1)).control := by
  have he := EncryptedBinaryMatrix.output_correct
    (BinarySchedule.schedule (EncryptedObliviousMatrix.schedule program steps) ObliviousMatrix.vocabulary_positive)
    (BinarySchedule.transition ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition (ObliviousMatrix.label finish))
    BinarySchedule.tokenBit generator (BinarySchedule.prompt (ObliviousMatrix.prompt program steps input)) seed
  have h := output_correct program steps finish input
  exact he.trans (by simpa only [model, inputEncoding, BinaryMatrix.model, BinaryMatrix.inputEncoding, RoutedSchedule.output_correct] using h)

/-- The entire actual encrypted payload uses just the two fixed binary
packet tokens, with no unobserved token fields carrying extra information. -/
theorem encrypted_binary (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool)
    (generator : LocalGenerator seedLength (steps * ObliviousMatrix.vocabulary Control Symbol + 1) locality)
    (input : Input) (seed : Bits seedLength) (time : Fin (steps * ObliviousMatrix.vocabulary Control Symbol)) :
    ∃ bit : Bool, (encryptedModel program steps finish generator).transcript (encryptedInput program steps input seed) time =
      EncryptedBinaryMatrix.binaryPacket bit := by
  let schedule := BinarySchedule.schedule (EncryptedObliviousMatrix.schedule program steps)
    (ObliviousMatrix.vocabulary_positive (Control := Control) (Symbol := Symbol))
  let transition := BinarySchedule.transition (ObliviousMatrix.vocabulary_positive (Control := Control) (Symbol := Symbol))
    (ObliviousMatrix.transition (Control := Control) (Symbol := Symbol)) (ObliviousMatrix.label (Symbol := Symbol) finish)
  let plain := BinarySchedule.prompt (ObliviousMatrix.prompt program steps input)
  refine ⟨xor (EncryptedBinaryMatrix.plainTranscript schedule transition plain time) (generator.generate seed time.castSucc), ?_⟩
  exact EncryptedBinaryMatrix.generated_binary schedule transition BinarySchedule.tokenBit generator plain seed time

end BinaryObliviousMatrix
