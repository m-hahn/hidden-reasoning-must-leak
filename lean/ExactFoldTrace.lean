import ExactFoldPrompt
import ConcreteReasoning
import CausalSymbolicFootprint

/-! # Information and length of the same native exact-alphabet encrypted fold

Fixing a seed changes raw prompt constants, not the matrices. The trace is
the actual first-separator word. Its length, native token identity, complete
answer, and private-seed information tax are derived here.
-/
noncomputable section
set_option maxHeartbeats 1200000
namespace ExactFoldTrace
open TransformerAC0 Encryption UniformTaskFootprint FiniteInformation
variable {Control Input Label : Type*} [Fintype Control] [Fintype Input] [DecidableEq Input]
variable [Inhabited Control] [Inhabited Input] {vocabulary n seedLength locality : ℕ}

theorem expectation_constant {Ω : Type*} [Fintype Ω] (D : Distribution Ω) (value : ℝ) :
    D.expectation (fun _ => value) = value := by
  simp only [Distribution.expectation, ← Finset.sum_mul, D.sum_one, one_mul]

section Fixed
variable (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
variable (initial : Control) (update : Control → Input → Control)
variable (generator : LocalGenerator seedLength (EncryptedFold.payloadLength Control Input n + 1) locality)
variable (label : Fin vocabulary → Bool)

theorem stops (seed : Bits seedLength) (input : Fin n → Input) :
    (ExactFold.model alphabet initial update n generator label).generatedToken
      (CausalSymbolicToken.promptInput (ExactFoldPrompt.prompt (Input := Input) alphabet initial n seed) input)
      ⟨EncryptedFold.payloadLength Control Input n, by
        change EncryptedFold.payloadLength Control Input n < EncryptedFold.payloadLength Control Input n + 3; omega⟩ =
      ProtocolMatrix.separator vocabulary := by
  rw [ExactFoldPrompt.prompt_correct alphabet initial update]
  unfold ExactFold.model ExactFold.inputEncoding
  exact ExactEncryptedAlphabet.separator_generated _ _ _ _ _ _ _ _ _

theorem before (seed : Bits seedLength) (input : Fin n → Input) (time : Fin (EncryptedFold.payloadLength Control Input n)) :
    (ExactFold.model alphabet initial update n generator label).generatedToken
      (CausalSymbolicToken.promptInput (ExactFoldPrompt.prompt (Input := Input) alphabet initial n seed) input)
      ⟨time.val, by change time.val < EncryptedFold.payloadLength Control Input n + 3; have h := time.isLt; omega⟩ ≠
      ProtocolMatrix.separator vocabulary := by
  rw [ExactFoldPrompt.prompt_correct alphabet initial update]
  unfold ExactFold.model ExactFold.inputEncoding
  rw [ExactEncryptedAlphabet.payload_correct]
  exact ProtocolMatrix.data_ne_separator _

def model (seed : Bits seedLength) : TokenSymbolic.Generator n (EncryptedFold.payloadLength Control Input n + 1) Input :=
  CausalSymbolicToken.generator (ExactFold.model alphabet initial update n generator label)
    (ExactFoldPrompt.prompt (Input := Input) alphabet initial n seed) (ProtocolMatrix.separator vocabulary)
    (EncryptedFold.payloadLength Control Input n) (by omega) (stops alphabet initial update generator label seed)

theorem length_eq (seed : Bits seedLength) (input : Fin n → Input) :
    ((model alphabet initial update generator label seed).length input).val = EncryptedFold.payloadLength Control Input n :=
  CausalSymbolicToken.length_eq _ _ _ _ _ (stops alphabet initial update generator label seed)
    (before alphabet initial update generator label seed) input

theorem answer_correct (seed : Bits seedLength) (input : Fin n → Input) :
    (model alphabet initial update generator label seed).answer input =
      label (alphabet.output (EncryptedFold.outputCode (some ((List.ofFn input).foldl update initial)))) := by
  rw [model, CausalSymbolicToken.answer_eq _ _ _ _ _ _ (before alphabet initial update generator label seed)]
  rw [ExactFoldPrompt.prompt_correct alphabet initial update]
  have h := ExactFold.generated_output alphabet initial update generator label input seed (0 : Fin 2)
  simp only [Fin.val_zero, Nat.add_zero, ite_true] at h
  rw [h]
  change ProtocolMatrix.label label (ProtocolMatrix.dataToken _) = _
  simp [ProtocolMatrix.label, ProtocolMatrix.dataToken]

def trace (pair : (Fin n → Input) × Bits seedLength) :=
  CausalSymbolicToken.nativePrefix (Alphabet := Input) (n := n) (ExactFold.model alphabet initial update n generator label)
    (ExactFoldPrompt.prompt (Input := Input) alphabet initial n pair.2) (EncryptedFold.payloadLength Control Input n)
    (by change EncryptedFold.payloadLength Control Input n ≤ EncryptedFold.payloadLength Control Input n + 1; omega) pair.1

theorem trace_native (pair : (Fin n → Input) × Bits seedLength) (time : Fin (EncryptedFold.payloadLength Control Input n + 1)) :
    trace alphabet initial update generator label pair time =
      (ExactFold.model alphabet initial update n generator label).generatedToken
        (ExactFold.inputEncoding alphabet initial update pair.1 pair.2)
        ⟨time.val, by change time.val < EncryptedFold.payloadLength Control Input n + 3; have h := time.isLt; omega⟩ := by
  unfold trace CausalSymbolicToken.nativePrefix
  rw [ExactFoldPrompt.prompt_correct alphabet initial update]

def expectedLength : ℝ :=
  (Distribution.uniform ((Fin n → Input) × Bits seedLength)).expectation
    (fun pair => (((model alphabet initial update generator label pair.2).length pair.1).val + 1 : ℕ))

theorem depth_seed (seed : Bits seedLength) :
    (model alphabet initial update generator label seed).fiberDepth =
      (model alphabet initial update generator label (fun _ => false)).fiberDepth := by
  unfold TokenSymbolic.Generator.fiberDepth model CausalSymbolicToken.generator CausalSymbolicToken.core
  rfl

theorem size_seed (seed : Bits seedLength) :
    (model alphabet initial update generator label seed).fiberSize =
      (model alphabet initial update generator label (fun _ => false)).fiberSize := by
  unfold TokenSymbolic.Generator.fiberSize TokenSymbolic.Generator.predictionSize model CausalSymbolicToken.generator CausalSymbolicToken.core
  rfl

theorem seedwise_footprint [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (pairing : Input ≃ Bool × Label)
    (correct : ∀ input : Fin n → Input,
      label (alphabet.output (EncryptedFold.outputCode (some ((List.ofFn input).foldl update initial)))) =
        Tal.parity (fun i => (pairing (input i)).1)) (hn : 1 ≤ n) (seed : Bits seedLength) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound
      (model alphabet initial update generator label (fun _ => false)).fiberDepth
      (model alphabet initial update generator label (fun _ => false)).fiberSize n)) ≤
      (Distribution.uniform (Fin n → Input)).entropy (fun input => trace alphabet initial update generator label (input, seed)) := by
  have h := (model alphabet initial update generator label seed).uniform_footprint tal pairing
    (fun input => (answer_correct alphabet initial update generator label seed input).trans (correct input)) hn
  rw [Distribution.mutualInformation_id_eq_entropy] at h
  rw [depth_seed alphabet initial update generator label seed, size_seed alphabet initial update generator label seed] at h
  have hc : (Distribution.uniform (Fin n → Input)).entropy
      (model alphabet initial update generator label seed).transcript ≤
      (Distribution.uniform (Fin n → Input)).entropy
        (fun input => trace alphabet initial update generator label (input, seed)) := by
    exact CausalSymbolicToken.entropy_prefix
      (ExactFold.model alphabet initial update n generator label) (ExactFoldPrompt.prompt (Input := Input) alphabet initial n seed)
      (ProtocolMatrix.separator vocabulary) (EncryptedFold.payloadLength Control Input n)
      (by change EncryptedFold.payloadLength Control Input n ≤ EncryptedFold.payloadLength Control Input n + 1; omega)
      (stops alphabet initial update generator label seed) (before alphabet initial update generator label seed)
      (Distribution.uniform (Fin n → Input)) ⟨ProtocolMatrix.dataToken (alphabet.bit false), ProtocolMatrix.data_ne_separator _⟩
  exact h.trans hc

theorem information_lower_bound [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (pairing : Input ≃ Bool × Label)
    (correct : ∀ input : Fin n → Input,
      label (alphabet.output (EncryptedFold.outputCode (some ((List.ofFn input).foldl update initial)))) =
        Tal.parity (fun i => (pairing (input i)).1)) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound
      (model alphabet initial update generator label (fun _ => false)).fiberDepth
      (model alphabet initial update generator label (fun _ => false)).fiberSize n)) - (seedLength : ℝ) ≤
      (Distribution.uniform ((Fin n → Input) × Bits seedLength)).mutualInformation Prod.fst
        (trace alphabet initial update generator label) := by
  have hbits : Real.logb 2 (Fintype.card (Bits seedLength)) = (seedLength : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
    rw [Real.logb, Real.log_pow]
    have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog]
  rw [← hbits]
  exact Distribution.private_randomness_information_lower_bound _ _
    (seedwise_footprint alphabet initial update generator label tal pairing correct hn)

theorem expected_length_lower_bound [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (pairing : Input ≃ Bool × Label)
    (correct : ∀ input : Fin n → Input,
      label (alphabet.output (EncryptedFold.outputCode (some ((List.ofFn input).foldl update initial)))) =
        Tal.parity (fun i => (pairing (input i)).1)) (hn : 1 ≤ n) (hv : 1 < vocabulary + 1) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound
      (model alphabet initial update generator label (fun _ => false)).fiberDepth
      (model alphabet initial update generator label (fun _ => false)).fiberSize n)) /
      Real.logb 2 (vocabulary + 1 : ℕ) ≤ expectedLength alphabet initial update generator label := by
  let M := model alphabet initial update generator label (fun _ => false)
  have h := M.uniform_expected_length_lower_bound tal pairing
    (fun input => (answer_correct alphabet initial update generator label (fun _ => false) input).trans (correct input)) hn hv
  change _ ≤ (Distribution.uniform ((Fin n → Input) × Bits seedLength)).expectation _
  simp_rw [length_eq]
  rw [expectation_constant]
  dsimp only [M, TokenSymbolic.Generator.expectedLength] at h
  simp_rw [length_eq] at h
  rw [expectation_constant] at h
  exact h

end Fixed
end ExactFoldTrace
