import VerifiedMultiplicationSource
import PlainPolylogBit

/-! An assumption-free four-token multiplication construction with
O(N log³ N) context, a native middle bit and EOS, and fixed precision. -/

noncomputable section
namespace VerifiedPlainMultiplication
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
open VerifiedMultiplicationSource

def model (n : ℕ) :=
  PlainPolylogBit.model (times := times) machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit n

def inputEncoding (n : ℕ) (input : Bits (n + n)) :=
  PlainPolylogBit.inputEncoding (times := times) machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) n (initialTape n input)

def OutputCorrect : Prop := ∀ n, 1 ≤ n → ∀ (input : Bits (n + n)) (output : Fin 2),
  (model n).generatedToken (inputEncoding n input)
    ⟨PolylogPrivateBit.payloadLength (times := times) machine SchonhageInitializer.inputTape n + 1 + output.val, by
      change PolylogPrivateBit.payloadLength (times := times) machine SchonhageInitializer.inputTape n + 1 + output.val <
        PolylogPrivateBit.payloadLength (times := times) machine SchonhageInitializer.inputTape n + 3
      have h := output.isLt; omega⟩ =
    ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryOutput (ExactTaskAlphabet.boolCode
      (if output = 0 then some (MultiplicationFootprint.middleBitTarget n input) else none)))

theorem output_correct : OutputCorrect := by
  intro n hn input output
  rw [model, inputEncoding, PlainPolylogBit.generated_output, middle_bit n hn input]

def contextCoefficient : ℕ := PlainPolylogBit.contextCoefficient 64 State (Fin 4) coefficient

theorem context_bound (n : ℕ) : (model n).architecture.contextLength + 1 ≤
    contextCoefficient * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3 :=
  PlainPolylogBit.context_bound machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound n

theorem polynomial_resources : ∃ D P : ℕ, ∀ n,
    (model n).architecture.hiddenWidth ≤ D * (n + 1) ^ 4 ∧
    (model n).architecture.parameterCount ≤ P * (n + 1) ^ 8 :=
  PlainPolylogBit.polynomial_resources machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound

theorem architecture_fixed : ∃ heads precision : ℕ, ∀ n,
    (model n).architecture.vocabulary = 4 ∧ (model n).architecture.layers = 1 ∧
    (model n).architecture.heads = heads ∧ (model n).parameters.scalarBits = precision :=
  PlainPolylogBit.architecture_fixed (times := times) machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit

theorem complete : OutputCorrect ∧
    (∀ n, (model n).architecture.contextLength + 1 ≤ contextCoefficient * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3) ∧
    (∃ D P : ℕ, ∀ n, (model n).architecture.hiddenWidth ≤ D * (n + 1) ^ 4 ∧
      (model n).architecture.parameterCount ≤ P * (n + 1) ^ 8) ∧
    (∃ heads precision : ℕ, ∀ n, (model n).architecture.vocabulary = 4 ∧
      (model n).architecture.layers = 1 ∧ (model n).architecture.heads = heads ∧
      (model n).parameters.scalarBits = precision) :=
  ⟨output_correct, context_bound, polynomial_resources, architecture_fixed⟩

end VerifiedPlainMultiplication
