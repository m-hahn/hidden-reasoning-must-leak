import EncryptedMatrix

/-!
# Privacy for the complete encoded matrix token trace

Every payload token is a ciphertext packet, and all of that packet's bits
are a fixed finite function of its ciphertext chunk. This file constructs
the corresponding constant-depth, linear-size circuit. Thus security is
not restricted to an observer given only a projection of a larger token.
The encoding may be any fixed binary code, including a lossless one.
-/

noncomputable section
namespace EncryptedSerialization
open scoped BigOperators
open TransformerAC0 Encryption

variable {vocabulary codeWidth steps : ℕ}

def encode (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth)
    (word : Bits (steps * vocabulary)) : Bits (steps * codeWidth) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  encoding (EncryptedMatrix.cipherPacket (fun bit => word (finProdFinEquiv (pair.1, bit)))) pair.2

def encodingCircuit (steps : ℕ)
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth) :
    Circuit (steps * vocabulary) (steps * codeWidth) := .bundle fun wire =>
  let pair := finProdFinEquiv.symm wire
  .seq (.wire (fun bit => finProdFinEquiv (pair.1, bit)))
    (Circuit.ofPredicate (fun word => encoding (EncryptedMatrix.cipherPacket word) pair.2))

theorem eval_encodingCircuit
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth)
    (word : Bits (steps * vocabulary)) : Circuit.eval (encodingCircuit steps encoding) word = encode encoding word := by
  funext wire
  simp [encodingCircuit, Circuit.eval, encode]

theorem encodingCircuit_depth
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth) :
    Circuit.depth (encodingCircuit steps encoding) ≤ 3 := by
  simp only [encodingCircuit, Circuit.depth, Nat.zero_add]
  exact Finset.sup_le fun _ _ => Circuit.depth_ofPredicate_le_three _

def encodingCost (vocabulary : ℕ) : ℕ := Fintype.card (Bits vocabulary) * (vocabulary + 1) + 1

theorem encodingCircuit_size
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth) :
    Circuit.gateCount (encodingCircuit steps encoding) ≤ steps * codeWidth * encodingCost vocabulary := by
  simp only [encodingCircuit, Circuit.gateCount, Nat.zero_add]
  calc
    _ ≤ ∑ _wire : Fin (steps * codeWidth), encodingCost vocabulary :=
      Finset.sum_le_sum fun _ _ => Circuit.gateCount_ofPredicate_le _
    _ = _ := by simp

def pullbackMonitor {times : ℕ → ℕ}
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => times n * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    PolynomialMonitorFamily (fun n => times n * vocabulary) where
  circuit n := .seq (encodingCircuit (times n) encoding) (monitor.circuit n)
  coefficient := coefficient * codeWidth * encodingCost vocabulary + monitor.coefficient
  exponent := exponent + monitor.exponent
  size_le := by
    intro n
    simp only [Circuit.gateCount]
    apply (Nat.add_le_add (encodingCircuit_size encoding) (monitor.size_le n)).trans
    have he : times n * codeWidth * encodingCost vocabulary ≤
        coefficient * codeWidth * encodingCost vocabulary * (n + 1) ^ exponent := by
      have ht := Nat.mul_le_mul_right (codeWidth * encodingCost vocabulary) (timeLength n)
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
    calc
      _ ≤ coefficient * codeWidth * encodingCost vocabulary * (n + 1) ^ exponent +
          monitor.coefficient * (n + 1) ^ monitor.exponent := Nat.add_le_add_right he _
      _ ≤ coefficient * codeWidth * encodingCost vocabulary * (n + 1) ^ (exponent + monitor.exponent) +
          monitor.coefficient * (n + 1) ^ (exponent + monitor.exponent) := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ = _ := by ring

@[simp] theorem pullback_monitor {times : ℕ → ℕ}
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => times n * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (n : ℕ) (word : Bits (times n * vocabulary)) :
    (pullbackMonitor encoding monitor coefficient exponent timeLength).monitor n word =
      monitor.monitor n (encode encoding word) := by
  simp only [PolynomialMonitorFamily.monitor, pullbackMonitor, Circuit.eval, eval_encodingCircuit]

variable {front heads opcodes seedLength locality : ℕ}

def transcript (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) : Bits (steps * codeWidth) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  encoding ((EncryptedMatrix.model schedule hv plainTransition label generator).transcript
    (RoutedMatrix.promptInput (EncryptedMatrix.prompt plain seed)) pair.1) pair.2

theorem transcript_eq_encode (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) :
    transcript schedule hv plainTransition label generator encoding plain seed =
      encode encoding (EncryptedMatrix.transcript schedule hv plainTransition label generator plain seed) := by
  funext wire
  simp only [transcript, encode, EncryptedMatrix.full_transcript_reconstructible]

/-- Privacy for any fixed encoding of the whole emitted token word. The
explicit pullback circuit ensures that arbitrary polynomial monitors of
this word are covered by the allowed PRG security assumption. -/
theorem no_readability
    {inputLength seedLengths fronts times : ℕ → ℕ}
    (schedules : ∀ n, RoutedSchedule.Schedule (fronts n) (times n) heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (prompts : ∀ n, Bits (inputLength n) → Fin (fronts n) → Fin vocabulary)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n * vocabulary + vocabulary))
    (secure : generator.IsPseudorandom)
    (encoding : Fin (EncryptedMatrix.packetCount vocabulary) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => times n * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits (inputLength n))) (predicate : Bits (inputLength n) → Bool),
      predictionSuccess distribution
        (fun input seed => transcript (schedules n) hv plainTransition label (generator.generator n) encoding (prompts n input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  obtain ⟨error, hnegligible, hprivacy⟩ := EncryptedMatrix.no_readability schedules hv plainTransition label prompts generator secure
    (pullbackMonitor encoding monitor coefficient exponent timeLength) (coefficient * vocabulary) exponent
    (fun n => by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right vocabulary (timeLength n))
  refine ⟨error, hnegligible, ?_⟩
  intro n distribution predicate
  simpa only [predictionSuccess, pullback_monitor, transcript_eq_encode] using hprivacy n distribution predicate

end EncryptedSerialization
