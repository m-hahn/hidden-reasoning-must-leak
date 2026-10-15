import ProtocolEncryptedBinary

/-!
# Privacy of the entire natively generated visible word

The observer may use any fixed encoding of all payload tokens and the actual
separator. A derived depth-three, linear-size circuit maps binary ciphertext
to that complete encoding. No losslessness or token projection is assumed.
-/

noncomputable section
namespace ProtocolSerialization
open scoped BigOperators
open TransformerAC0 Encryption
variable {steps codeWidth : ℕ}

abbrev Encoding (width : ℕ) := Fin (EncryptedMatrix.packetCount 2 + 1) → Bits width

def encode (encoding : Encoding codeWidth) (word : Bits steps) : Bits ((steps + 1) * codeWidth) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  Fin.lastCases (encoding (ProtocolMatrix.separator (EncryptedMatrix.packetCount 2)) pair.2)
    (fun position => encoding (ProtocolMatrix.dataToken (EncryptedBinaryMatrix.binaryPacket (word position))) pair.2) pair.1

def branch (steps : ℕ) (encoding : Encoding codeWidth) (bit : Fin codeWidth) (position : Fin (steps + 1)) : Circuit steps 1 :=
  Fin.lastCases (Circuit.const steps (encoding (ProtocolMatrix.separator (EncryptedMatrix.packetCount 2)) bit))
    (fun position => Circuit.seq (Circuit.wire (fun _ : Fin 1 => position))
      (Circuit.ofPredicate (fun word : Bits 1 =>
        encoding (ProtocolMatrix.dataToken (EncryptedBinaryMatrix.binaryPacket (word 0))) bit))) position

def encodingCircuit (steps : ℕ) (encoding : Encoding codeWidth) : Circuit steps ((steps + 1) * codeWidth) :=
  .bundle fun wire => let pair := finProdFinEquiv.symm wire
    branch steps encoding pair.2 pair.1

theorem eval_encodingCircuit (encoding : Encoding codeWidth) (word : Bits steps) :
    Circuit.eval (encodingCircuit steps encoding) word = encode encoding word := by
  funext wire
  obtain ⟨⟨position, bit⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [encodingCircuit, Circuit.eval, encode, Equiv.symm_apply_apply]
  refine Fin.lastCases ?_ (fun position => ?_) position <;> simp [branch, Circuit.eval]

theorem branch_depth (encoding : Encoding codeWidth) (bit : Fin codeWidth) (position : Fin (steps + 1)) :
    Circuit.depth (branch steps encoding bit position) ≤ 3 := by
  refine Fin.lastCases ?_ (fun position => ?_) position
  · simp only [branch, Fin.lastCases_last, Circuit.const, Circuit.depth, Nat.zero_add]
    split_ifs <;> simp [Circuit.depth]
  · simp only [branch, Fin.lastCases_castSucc, Circuit.depth, Nat.zero_add]
    exact Circuit.depth_ofPredicate_le_three _

theorem branch_size (encoding : Encoding codeWidth) (bit : Fin codeWidth) (position : Fin (steps + 1)) :
    Circuit.gateCount (branch steps encoding bit position) ≤ 5 := by
  refine Fin.lastCases ?_ (fun position => ?_) position
  · simp only [branch, Fin.lastCases_last, Circuit.gateCount_const]
    omega
  · simp only [branch, Fin.lastCases_castSucc, Circuit.gateCount, Nat.zero_add]
    have h := Circuit.gateCount_ofPredicate_le (fun word : Bits 1 =>
      encoding (ProtocolMatrix.dataToken (EncryptedBinaryMatrix.binaryPacket (word 0))) bit)
    simpa [Bits] using h

theorem encodingCircuit_depth (encoding : Encoding codeWidth) : Circuit.depth (encodingCircuit steps encoding) ≤ 3 := by
  simp only [encodingCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => branch_depth _ _ _

theorem encodingCircuit_size (encoding : Encoding codeWidth) :
    Circuit.gateCount (encodingCircuit steps encoding) ≤ (steps + 1) * codeWidth * 5 := by
  simp only [encodingCircuit, Circuit.gateCount]
  calc
    _ ≤ ∑ _wire : Fin ((steps + 1) * codeWidth), 5 := Finset.sum_le_sum fun _ _ => branch_size _ _ _
    _ = _ := by simp

def pullbackMonitor {times : ℕ → ℕ} (encoding : Encoding codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (times n + 1) * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    PolynomialMonitorFamily times where
  circuit n := .seq (encodingCircuit (times n) encoding) (monitor.circuit n)
  coefficient := (coefficient + 1) * codeWidth * 5 + monitor.coefficient
  exponent := exponent + monitor.exponent
  size_le n := by
    have ht : times n + 1 ≤ (coefficient + 1) * (n + 1) ^ exponent := by
      have hp : 1 ≤ (n + 1) ^ exponent := Nat.one_le_pow _ _ (by omega)
      have h := timeLength n
      nlinarith
    have he := Nat.mul_le_mul_right (codeWidth * 5) ht
    have hp₁ := Nat.mul_le_mul_left ((coefficient + 1) * codeWidth * 5)
      (Nat.pow_le_pow_right (by omega : 0 < n + 1) (by omega : exponent ≤ exponent + monitor.exponent))
    have hp₂ := Nat.mul_le_mul_left monitor.coefficient
      (Nat.pow_le_pow_right (by omega : 0 < n + 1) (by omega : monitor.exponent ≤ exponent + monitor.exponent))
    change (encodingCircuit (times n) encoding).gateCount + (monitor.circuit n).gateCount ≤ _
    apply (Nat.add_le_add (encodingCircuit_size encoding) (monitor.size_le n)).trans
    nlinarith

@[simp] theorem pullback_monitor {times : ℕ → ℕ} (encoding : Encoding codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (times n + 1) * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (n : ℕ) (word : Bits (times n)) :
    (pullbackMonitor encoding monitor coefficient exponent timeLength).monitor n word = monitor.monitor n (encode encoding word) := by
  simp only [PolynomialMonitorFamily.monitor, pullbackMonitor, Circuit.eval, eval_encodingCircuit]

variable {front heads opcodes seedLength locality : ℕ}

theorem payload_packet (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin steps) :
    (ProtocolEncryptedBinary.model schedule transition label generator).generatedToken
      (ProtocolEncryptedBinary.inputEncoding plain seed) ⟨time.val, by have h := time.isLt; omega⟩ =
      ProtocolMatrix.dataToken (EncryptedBinaryMatrix.binaryPacket
        (ProtocolEncryptedBinary.transcript schedule transition label generator plain seed time)) := by
  rw [ProtocolEncryptedBinary.payload_correct]
  simp only [ProtocolEncryptedBinary.transcript, ProtocolEncryptedBinary.payload_correct, ProtocolMatrix.decode_data,
    EncryptedBinaryMatrix.binaryPacket, EncryptedMatrix.cipherValue_cipherPacket]
  cases h : xor (EncryptedBinaryMatrix.plainTranscript schedule transition plain time) (generator.generate seed time.castSucc) <;> rfl

def transcript (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (encoding : Encoding codeWidth)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) : Bits ((steps + 1) * codeWidth) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  encoding ((ProtocolEncryptedBinary.model schedule transition label generator).transcript
    (ProtocolEncryptedBinary.inputEncoding plain seed) pair.1) pair.2

theorem transcript_eq_encode (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (encoding : Encoding codeWidth)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    transcript schedule transition label generator encoding plain seed =
      encode encoding (ProtocolEncryptedBinary.transcript schedule transition label generator plain seed) := by
  funext wire
  obtain ⟨⟨position, bit⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [transcript, encode, Equiv.symm_apply_apply, CausalAutoregressive.Model.transcript]
  refine Fin.lastCases ?_ (fun position => ?_) position
  · simp only [Fin.lastCases_last]
    exact congrArg (fun token => encoding token bit)
      (ProtocolEncryptedBinary.separator_generated schedule transition label generator plain seed)
  · simp only [Fin.lastCases_castSucc]
    exact congrArg (fun token => encoding token bit) (payload_packet schedule transition label generator plain seed position)

theorem no_readability {inputLength seedLengths fronts times : ℕ → ℕ}
    (schedules : ∀ n, RoutedSchedule.Schedule (fronts n) (times n) heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (prompts : ∀ n, Bits (inputLength n) → Fin (fronts n) → Fin 2)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n + 1)) (secure : generator.IsPseudorandom)
    (encoding : Encoding codeWidth) (monitor : PolynomialMonitorFamily (fun n => (times n + 1) * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits (inputLength n))) (predicate : Bits (inputLength n) → Bool),
      predictionSuccess distribution
        (fun input seed => transcript (schedules n) transition label (generator.generator n) encoding (prompts n input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  obtain ⟨error, hnegligible, hprivacy⟩ := ProtocolEncryptedBinary.no_readability schedules transition label prompts generator secure
    (pullbackMonitor encoding monitor coefficient exponent timeLength) coefficient exponent timeLength
  refine ⟨error, hnegligible, ?_⟩
  intro n distribution predicate
  simpa only [predictionSuccess, pullback_monitor, transcript_eq_encode] using hprivacy n distribution predicate

end ProtocolSerialization
