import BinaryMatrix
import EncryptedMatrix

/-!
# Actual encrypted binary-token generation

A binary plaintext token has a two-bit one-hot encoding. The same PRG bit
is XORed into both coordinates, which swaps the two one-hot words. Thus
every emitted ciphertext packet is one of two fixed vocabulary tokens.
The duplicated pad is not claimed pseudorandom as a two-bit string: privacy
is proved from the original one-bit-per-event PRG, by an exact reduction.
-/

noncomputable section
namespace EncryptedBinaryMatrix
open TransformerAC0 Encryption
variable {front steps heads opcodes seedLength locality : ℕ}

def halfIndex (wire : Fin (steps * 2 + 2)) : Fin (steps + 1) := ⟨wire.val / 2, by have h := wire.isLt; omega⟩

def repeatGenerator (generator : LocalGenerator seedLength (steps + 1) locality) : LocalGenerator seedLength (steps * 2 + 2) locality where
  generate seed wire := generator.generate seed (halfIndex wire)
  dependency wire index := generator.dependency (halfIndex wire) index
  locality_correct wire first second hagree := generator.locality_correct (halfIndex wire) first second hagree

theorem halfIndex_padIndex (time : Fin (steps + 1)) (bit : Fin 2) : halfIndex (EncryptedMatrix.padIndex time bit) = time := by
  apply Fin.ext
  change (bit.val + 2 * time.val) / 2 = time.val
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt bit.isLt]
  omega

theorem repeat_pad (generator : LocalGenerator seedLength (steps + 1) locality) (seed : Bits seedLength) (time : Fin (steps + 1)) :
    EncryptedMatrix.pad (repeatGenerator generator) seed time = fun _ => generator.generate seed time := by
  funext bit
  change generator.generate seed (halfIndex (EncryptedMatrix.padIndex time bit)) = _
  rw [halfIndex_padIndex]

theorem xor_indicator (token : Fin 2) (mask : Bool) :
    bitXor (RoutedMatrix.indicator token) (fun _ => mask) =
      RoutedMatrix.indicator (BinarySchedule.bitToken (xor (BinarySchedule.tokenBit token) mask)) := by
  funext bit
  fin_cases token <;> fin_cases bit <;> cases mask <;>
    simp [bitXor, RoutedMatrix.indicator, BinarySchedule.bitToken, BinarySchedule.tokenBit, Bool.xor]

def model (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) :=
  EncryptedMatrix.model schedule (by decide : 0 < 2) transition label (repeatGenerator generator)

def inputEncoding (plain : Fin front → Fin 2) (seed : Bits seedLength) :=
  RoutedMatrix.promptInput (EncryptedMatrix.prompt plain seed)

def binaryPacket (bit : Bool) : Fin (EncryptedMatrix.packetCount 2) :=
  EncryptedMatrix.cipherPacket (RoutedMatrix.indicator (BinarySchedule.bitToken bit))

theorem binaryPacket_injective : Function.Injective binaryPacket := by
  intro first second heq
  have hwords : RoutedMatrix.indicator (BinarySchedule.bitToken first) = RoutedMatrix.indicator (BinarySchedule.bitToken second) := by
    exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (EncryptedMatrix.packetCode.injective heq)))
  have ht := RoutedMatrix.indicator_injective 2 hwords
  simpa using congrArg BinarySchedule.tokenBit ht

def plainTranscript (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (plain : Fin front → Fin 2) : Bits steps :=
  fun time => BinarySchedule.tokenBit (RoutedSchedule.token schedule transition plain time.castSucc)

def transcript (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (plain : Fin front → Fin 2) (seed : Bits seedLength) : Bits steps :=
  fun time => EncryptedMatrix.cipherValue (vocabulary := 2)
    ((model schedule transition label generator).transcript (inputEncoding plain seed) time) 1

/-- Every payload event is an actual binary ciphertext token. There are
exactly two possible packet values, independent of time and input length. -/
theorem generated_binary (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin steps) :
    (model schedule transition label generator).transcript (inputEncoding plain seed) time =
      binaryPacket (xor (plainTranscript schedule transition plain time) (generator.generate seed time.castSucc)) := by
  unfold model inputEncoding CausalAutoregressive.Model.transcript
  rw [EncryptedMatrix.generated_correct]
  have hlast : time.castSucc.val ≠ steps := by change time.val ≠ steps; have h := time.isLt; omega
  simp only [EncryptedMatrix.target, if_neg hlast, repeat_pad, xor_indicator]
  rfl

theorem transcript_eq_encryptedTrace (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    transcript schedule transition label generator plain seed =
      encryptedTrace (plainTranscript schedule transition) (prefixGenerator generator.generate) plain seed := by
  funext time
  simp only [transcript, generated_binary, binaryPacket, EncryptedMatrix.cipherValue_cipherPacket]
  change RoutedMatrix.indicator (BinarySchedule.bitToken (xor (plainTranscript schedule transition plain time)
      (generator.generate seed time.castSucc))) 1 =
    xor (plainTranscript schedule transition plain time) (generator.generate seed time.castSucc)
  cases h : xor (plainTranscript schedule transition plain time) (generator.generate seed time.castSucc) <;>
    rfl

theorem output_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
    (generator : LocalGenerator seedLength (steps + 1) locality) (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    (model schedule transition label generator).answer (inputEncoding plain seed) =
      label (RoutedSchedule.token schedule transition plain (Fin.last steps)) :=
  EncryptedMatrix.output_correct schedule (by decide) transition label (repeatGenerator generator) plain seed

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
  obtain ⟨error, hnegligible, hprivacy⟩ := PolynomialEncryption.no_readability generator secure
    (fun n input => plainTranscript (schedules n) transition (prompts n input)) monitor coefficient exponent traceLength
  refine ⟨error, hnegligible, ?_⟩
  intro n distribution predicate
  simp_rw [transcript_eq_encryptedTrace]
  exact hprivacy n distribution predicate

end EncryptedBinaryMatrix
