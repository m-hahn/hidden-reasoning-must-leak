import ProtocolMatrix
import EncryptedBinaryMatrix
import EncryptedEfficientMatrix

/-!
# Binary ciphertext, native separator, and plaintext answer

The separator is a greedy numerical output event, not concatenated after
generation. The preceding tokens are exactly the two encrypted binary
packets; the next event is the correct plaintext answer. Privacy follows
from the already-proved one-bit-per-event PRG reduction.
-/

noncomputable section
namespace ProtocolEncryptedBinary
open TransformerAC0 Encryption
variable {front steps heads opcodes seedLength locality : ℕ}

def baseSchedule (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps + 1) locality) :=
  RoutedSchedule.ofPlan (EncryptedMatrix.plan schedule (EncryptedBinaryMatrix.repeatGenerator generator))
    (by have hf := schedule.front_positive; omega : 0 < seedLength + front) le_rfl

def run (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool) :=
  EncryptedMatrix.transition (by decide : 0 < 2) transition label (locality := locality)

theorem base_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin (steps + 1)) :
    RoutedSchedule.token (baseSchedule schedule generator) (run transition label) (EncryptedMatrix.prompt plain seed) time =
      EncryptedMatrix.target schedule transition label (EncryptedBinaryMatrix.repeatGenerator generator) plain seed time := by
  rw [baseSchedule, RoutedSchedule.token_ofPlan _ _ (EncryptedMatrix.packet_positive 2)
    (EncryptedMatrix.opcode_positive (EncryptedMatrix.plainOpcodes_positive schedule))]
  exact EncryptedMatrix.routed_correct schedule (by decide) transition label
    (EncryptedBinaryMatrix.repeatGenerator generator) plain seed time

def model (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) :=
  ProtocolMatrix.model (baseSchedule schedule generator) (EncryptedMatrix.packet_positive 2)
    (run transition label) (EncryptedMatrix.answerValue (vocabulary := 2)) steps le_rfl

def inputEncoding (plain : Fin front → Fin 2) (seed : Bits seedLength) :=
  RoutedMatrix.promptInput (fun p => ProtocolMatrix.dataToken (EncryptedMatrix.prompt plain seed p))

def inputLiteral (literal : Fin (front * 2) → Autoregressive.ContextLiteral n) (seedLength : ℕ) :
    Fin ((seedLength + front) * (EncryptedMatrix.packetCount 2 + 1)) → Autoregressive.ContextLiteral (n + seedLength) :=
  fun wire =>
    let pair := finProdFinEquiv.symm wire
    Fin.addCases
      (fun index => EfficientMatrix.bitLiteral
        (decide (pair.2 = ProtocolMatrix.dataToken (EncryptedMatrix.seedPacket 2 false)))
        (decide (pair.2 = ProtocolMatrix.dataToken (EncryptedMatrix.seedPacket 2 true))) (Fin.natAdd n index))
      (fun position => Fin.lastCases (.constant false)
        (fun packet => match EncryptedMatrix.packetCode.symm packet with
          | .inl token => EncryptedEfficientMatrix.liftLiteral (literal (finProdFinEquiv (position, token)))
          | .inr _ => .constant false) pair.2) pair.1

theorem inputLiteral_correct (literal : Fin (front * 2) → Autoregressive.ContextLiteral n)
    (input : Bits n) (plain : Fin front → Fin 2) (seed : Bits seedLength)
    (correct : ∀ wire, (literal wire).eval input = RoutedMatrix.promptInput plain wire)
    (wire : Fin ((seedLength + front) * (EncryptedMatrix.packetCount 2 + 1))) :
    (inputLiteral literal seedLength wire).eval (Fin.append input seed) = inputEncoding plain seed wire := by
  obtain ⟨⟨position, packet⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [inputLiteral, inputEncoding, RoutedMatrix.promptInput, Equiv.symm_apply_apply]
  refine Fin.addCases (fun index => ?_) (fun index => ?_) position
  · simp only [Fin.addCases_left, EfficientMatrix.eval_bitLiteral, Fin.append_right]
    cases h : seed index <;> simp [EncryptedMatrix.prompt, h]
  · simp only [Fin.addCases_right]
    refine Fin.lastCases ?_ (fun packet => ?_) packet
    · simp [Autoregressive.ContextLiteral.eval, ProtocolMatrix.dataToken, ProtocolMatrix.separator,
        (ProtocolMatrix.data_ne_separator (EncryptedMatrix.plainPacket (plain index))).symm,
        EncryptedMatrix.prompt]
      exact (ProtocolMatrix.data_ne_separator (EncryptedMatrix.plainPacket (plain index))).symm
    · simp only [Fin.lastCases_castSucc]
      obtain ⟨value, rfl⟩ := EncryptedMatrix.packetCode.surjective packet
      cases value with
      | inl token =>
          simp only [Equiv.symm_apply_apply, EncryptedEfficientMatrix.eval_liftLiteral, correct]
          simp [RoutedMatrix.promptInput, EncryptedMatrix.prompt, EncryptedMatrix.plainPacket, ProtocolMatrix.dataToken]
      | inr value =>
          simp [Autoregressive.ContextLiteral.eval, EncryptedMatrix.prompt, EncryptedMatrix.plainPacket, ProtocolMatrix.dataToken]

theorem payload_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin steps) :
    (model schedule transition label generator).generatedToken (inputEncoding plain seed)
      ⟨time.val, by have h := time.isLt; omega⟩ =
      ProtocolMatrix.dataToken (EncryptedBinaryMatrix.binaryPacket
        (xor (EncryptedBinaryMatrix.plainTranscript schedule transition plain time) (generator.generate seed time.castSucc))) := by
  rw [model, inputEncoding, ProtocolMatrix.generated_correct]
  have hnot : time.val ≠ steps := by have h := time.isLt; omega
  simp only [ProtocolMatrix.target, hnot, ↓reduceIte]
  rw [base_correct]
  have htime : ProtocolMatrix.oldTime steps le_rfl ⟨time.val, by have h := time.isLt; omega⟩ = time.castSucc := by
    apply Fin.ext
    simp [ProtocolMatrix.oldTime, Nat.le_of_lt time.isLt]
  rw [htime]
  have hnotCast : time.castSucc.val ≠ steps := hnot
  simp only [EncryptedMatrix.target, hnotCast, ↓reduceIte,
    EncryptedBinaryMatrix.repeat_pad, EncryptedBinaryMatrix.xor_indicator]
  rfl

theorem separator_generated (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    (model schedule transition label generator).generatedToken (inputEncoding plain seed)
      ⟨steps, by omega⟩ = ProtocolMatrix.separator (EncryptedMatrix.packetCount 2) :=
  ProtocolMatrix.separator_generated _ _ _ _ _ _ _

theorem output_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    (model schedule transition label generator).answer (inputEncoding plain seed) =
      label (RoutedSchedule.token schedule transition plain (Fin.last steps)) := by
  unfold CausalAutoregressive.Model.answer
  rw [model, inputEncoding, ProtocolMatrix.generated_correct]
  have htime : ProtocolMatrix.oldTime steps le_rfl (Fin.last (steps + 1)) = Fin.last steps := by
    apply Fin.ext
    simp [ProtocolMatrix.oldTime]
  simp only [ProtocolMatrix.target, Fin.val_last, show steps + 1 ≠ steps by omega, ↓reduceIte, htime]
  rw [base_correct]
  simp only [EncryptedMatrix.target, Fin.val_last, if_true]
  change ProtocolMatrix.label EncryptedMatrix.answerValue
    (ProtocolMatrix.dataToken (EncryptedMatrix.answerPacket 2 _)) = _
  simp [ProtocolMatrix.label, ProtocolMatrix.dataToken]

def transcript (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) : Bits steps := fun time =>
  EncryptedMatrix.cipherValue (vocabulary := 2)
    (ProtocolMatrix.decode (EncryptedMatrix.packet_positive 2)
      ((model schedule transition label generator).generatedToken (inputEncoding plain seed)
        ⟨time.val, by have h := time.isLt; omega⟩)) 1

theorem transcript_eq_original (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    transcript schedule transition label generator plain seed =
      EncryptedBinaryMatrix.transcript schedule transition label generator plain seed := by
  funext time
  simp only [transcript, payload_correct, ProtocolMatrix.decode_data,
    EncryptedBinaryMatrix.transcript, EncryptedBinaryMatrix.generated_binary]

theorem no_readability {inputLength seedLengths fronts times : ℕ → ℕ}
    (schedules : ∀ n, RoutedSchedule.Schedule (fronts n) (times n) heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (prompts : ∀ n, Bits (inputLength n) → Fin (fronts n) → Fin 2)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n + 1)) (secure : generator.IsPseudorandom)
    (monitor : PolynomialMonitorFamily times) (coefficient exponent : ℕ)
    (traceLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits (inputLength n))) (predicate : Bits (inputLength n) → Bool),
      predictionSuccess distribution
        (fun input seed => transcript (schedules n) transition label (generator.generator n) (prompts n input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  simp_rw [transcript_eq_original]
  exact EncryptedBinaryMatrix.no_readability schedules transition label prompts generator secure monitor coefficient exponent traceLength

end ProtocolEncryptedBinary
