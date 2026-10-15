import CausalBoundary
import ExactEncryptedAlphabet
import ProtocolToken

/-! # First-separator seeded fibers of the same exact-alphabet matrices -/
noncomputable section
set_option maxHeartbeats 1200000
namespace ExactProtocolToken
open TransformerAC0 Encryption
variable {n front steps extra heads opcodes width vocabulary outputCard seedLength locality : ℕ}
variable (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary outputCard)
variable (schedule : RoutedSchedule.Schedule front steps heads opcodes)
variable (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
variable (generator : LocalGenerator seedLength (steps + 1) locality)
variable (sources : Fin (extra + 1) → Fin width → Fin steps)
variable (decode : Fin (extra + 1) → Bits width → Fin outputCard) (label : Fin vocabulary → Bool)
variable (plain : Bits n → Fin front → Fin 2)
variable (literal : Fin (front * 2) → Autoregressive.ContextLiteral n)
variable (literal_correct : ∀ input wire, (literal wire).eval input = RoutedMatrix.promptInput (plain input) wire)
include literal_correct

theorem prompt_append (input : Bits n) (seed : Bits seedLength) :
    CausalToken.promptInput (ExactEncryptedAlphabet.inputLiteral alphabet literal seedLength) (Fin.append input seed) =
      ExactEncryptedAlphabet.inputEncoding alphabet (plain input) seed := by
  funext wire
  exact ExactEncryptedAlphabet.inputLiteral_correct alphabet literal input (plain input) seed (literal_correct input) wire

theorem prompt_raw (word : Bits (n + seedLength)) :
    CausalToken.promptInput (ExactEncryptedAlphabet.inputLiteral alphabet literal seedLength) word =
      ExactEncryptedAlphabet.inputEncoding alphabet (plain (ProtocolToken.rawInput word)) (ProtocolToken.rawSeed word) := by
  have h := prompt_append alphabet plain literal literal_correct (ProtocolToken.rawInput word) (ProtocolToken.rawSeed word)
  rw [ProtocolToken.append_raw] at h
  exact h

theorem stops (word : Bits (n + seedLength)) :
    (ExactEncryptedAlphabet.model alphabet schedule transition generator sources decode label).generatedToken
      (CausalToken.promptInput (ExactEncryptedAlphabet.inputLiteral alphabet literal seedLength) word)
      ⟨steps, by omega⟩ = ProtocolMatrix.separator vocabulary := by
  rw [prompt_raw alphabet plain literal literal_correct]
  exact ExactEncryptedAlphabet.separator_generated _ _ _ _ _ _ _ _ _

theorem before (word : Bits (n + seedLength)) (time : Fin steps) :
    (ExactEncryptedAlphabet.model alphabet schedule transition generator sources decode label).generatedToken
      (CausalToken.promptInput (ExactEncryptedAlphabet.inputLiteral alphabet literal seedLength) word)
      ⟨time.val, by have h := time.isLt; omega⟩ ≠ ProtocolMatrix.separator vocabulary := by
  rw [prompt_raw alphabet plain literal literal_correct, ExactEncryptedAlphabet.payload_correct]
  exact ProtocolMatrix.data_ne_separator _

def tokenGenerator : TokenAutoregressive.Generator (n + seedLength) (steps + extra) :=
  CausalBoundary.generator (ExactEncryptedAlphabet.model alphabet schedule transition generator sources decode label)
    (ExactEncryptedAlphabet.inputLiteral alphabet literal seedLength) (ProtocolMatrix.separator vocabulary)
    steps (by omega) (stops alphabet schedule transition generator sources decode label plain literal literal_correct)

theorem length_fixed (word : Bits (n + seedLength)) :
    ((tokenGenerator alphabet schedule transition generator sources decode label plain literal literal_correct).length word).val = steps :=
  CausalBoundary.length_eq _ _ _ _ _ _ (before alphabet schedule transition generator sources decode label plain literal literal_correct) word

theorem native_answer (input : Bits n) (seed : Bits seedLength) :
    (tokenGenerator alphabet schedule transition generator sources decode label plain literal literal_correct).answer (Fin.append input seed) =
      (ExactEncryptedAlphabet.model alphabet schedule transition generator sources decode label).parameters.outputLabel
        ((ExactEncryptedAlphabet.model alphabet schedule transition generator sources decode label).generatedToken
          (ExactEncryptedAlphabet.inputEncoding alphabet (plain input) seed) ⟨steps + 1, by omega⟩) := by
  rw [tokenGenerator, CausalBoundary.answer_eq _ _ _ _ _ _
    (before alphabet schedule transition generator sources decode label plain literal literal_correct)]
  rw [prompt_append alphabet plain literal literal_correct]

theorem answer_correct (input : Bits n) (seed : Bits seedLength) :
    (tokenGenerator alphabet schedule transition generator sources decode label plain literal literal_correct).answer (Fin.append input seed) =
      label (alphabet.output (decode 0 (fun bit => EncryptedBinaryMatrix.plainTranscript schedule transition (plain input) (sources 0 bit)))) := by
  rw [native_answer]
  have h := ExactEncryptedAlphabet.output_correct alphabet schedule transition generator sources decode label (plain input) seed (0 : Fin (extra + 1))
  simp only [Fin.val_zero, Nat.add_zero] at h
  rw [h]
  change ProtocolMatrix.label label (ProtocolMatrix.dataToken _) = _
  simp [ProtocolMatrix.label, ProtocolMatrix.dataToken]

theorem native_trace (input : Bits n) (seed : Bits seedLength)
    (time : Fin ((tokenGenerator alphabet schedule transition generator sources decode label plain literal literal_correct).length (Fin.append input seed)).val) :
    (((tokenGenerator alphabet schedule transition generator sources decode label plain literal literal_correct).seededTrace (input, seed)).2 time).val =
      (ExactEncryptedAlphabet.model alphabet schedule transition generator sources decode label).generatedToken
        (ExactEncryptedAlphabet.inputEncoding alphabet (plain input) seed)
        ⟨time.val, by
          have h := time.isLt
          have hl := length_fixed alphabet schedule transition generator sources decode label plain literal literal_correct (Fin.append input seed)
          omega⟩ := by
  change (CausalToken.core _ _ _).generatedToken _ _ = _
  have ht : time.val < steps + extra + 2 := by
    have h := time.isLt
    have hl := length_fixed alphabet schedule transition generator sources decode label plain literal literal_correct (Fin.append input seed)
    omega
  have h := CausalToken.generated_correct
    (ExactEncryptedAlphabet.model alphabet schedule transition generator sources decode label)
    (ExactEncryptedAlphabet.inputLiteral alphabet literal seedLength) (ProtocolMatrix.separator vocabulary)
    (Fin.append input seed) ⟨time.val, ht⟩
  rw [prompt_append alphabet plain literal literal_correct] at h
  exact h

end ExactProtocolToken
