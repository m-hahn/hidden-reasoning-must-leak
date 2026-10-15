import TokenAutoregressive
import UniformTaskFootprint

/-!
# Full-uniform task alphabets and full-vocabulary matrix traces

Both sides of the paper's task reductions are concrete: inputs range over
the full task alphabet, and autoregression emits actual vocabulary tokens.
The variable-length trace ends at the first separator. Pairing slice bounds
are averaged over all label sequences, and source coding uses `log₂ |Γ|`.
-/

noncomputable section

namespace TokenSymbolic

open TransformerAC0 Autoregressive FiniteInformation UniformTaskFootprint

structure Core (n : ℕ) (Alphabet : Type*) where
  architecture : Architecture
  transformer : FixedPrecisionTransformer architecture
  vocabulary_positive : 0 < architecture.vocabulary
  context_positive : 0 < architecture.contextLength
  separator : Fin architecture.vocabulary
  context : (time : ℕ) → (Fin time → Fin architecture.vocabulary) →
    Fin architecture.inputBits → SymbolLiteral n Alphabet
  prefixLength : ℕ → {length : ℕ // 0 < length ∧ length ≤ architecture.contextLength} :=
    fun _ => ⟨architecture.contextLength, context_positive, le_rfl⟩

namespace Core

def stepTransformer (core : Core n Alphabet) (time : ℕ) :=
  CausalMatrix.restrictContext core.transformer (core.prefixLength time).val (core.prefixLength time).property.2

def inputWire (core : Core n Alphabet) (time : ℕ) :
    Fin (CausalMatrix.architecture core.architecture (core.prefixLength time).val).inputBits →
      Fin core.architecture.inputBits :=
  Fin.castLE (Nat.mul_le_mul_right core.architecture.vocabulary (core.prefixLength time).property.2)

def generatedToken [DecidableEq Alphabet] (core : Core n Alphabet) (input : Fin n → Alphabet)
    (time : ℕ) : Fin core.architecture.vocabulary :=
  (core.stepTransformer time).runToken core.vocabulary_positive (core.prefixLength time).property.1
    (fun wire => (core.context time (fun previous => core.generatedToken input previous) (core.inputWire time wire)).eval input)
termination_by time

def slice [DecidableEq Alphabet] (core : Core n Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) : TokenAutoregressive.Core n where
  architecture := core.architecture
  transformer := core.transformer
  vocabulary_positive := core.vocabulary_positive
  context_positive := core.context_positive
  separator := core.separator
  context := fun time prefixTokens wire => (core.context time prefixTokens wire).restrict pairing labels
  prefixLength := core.prefixLength

@[simp] theorem slice_generatedToken [DecidableEq Alphabet] (core : Core n Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) (input : Bits n) (time : ℕ) :
    (core.slice pairing labels).generatedToken input time =
      core.generatedToken (fun i => pairing.symm (input i, labels i)) time := by
  induction time using Nat.strong_induction_on with
  | h time ih =>
      rw [TokenAutoregressive.Core.generatedToken, generatedToken]
      change (core.stepTransformer time).runToken core.vocabulary_positive (core.prefixLength time).property.1 _ =
        (core.stepTransformer time).runToken core.vocabulary_positive (core.prefixLength time).property.1 _
      congr 1
      funext wire
      change ((core.context time
        (fun previous => (core.slice pairing labels).generatedToken input previous) (core.inputWire time wire)).restrict pairing labels).eval input = _
      rw [SymbolLiteral.eval_restrict]
      congr 2
      funext previous
      exact ih previous previous.isLt

end Core

structure Generator (n bound : ℕ) (Alphabet : Type*) [DecidableEq Alphabet] where
  core : Core n Alphabet
  terminates : ∀ input : Fin n → Alphabet, ∃ time : ℕ,
    time ≤ bound ∧ core.generatedToken input time = core.separator

namespace Generator

variable {Alphabet Label : Type*} [DecidableEq Alphabet]

abbrev Nonterminal (model : Generator n bound Alphabet) :=
  {token : Fin model.core.architecture.vocabulary // token ≠ model.core.separator}

abbrev Transcript (model : Generator n bound Alphabet) :=
  (length : Fin (bound + 1)) × (Fin length.val → model.Nonterminal)

def length (model : Generator n bound Alphabet) (input : Fin n → Alphabet) : Fin (bound + 1) :=
  ⟨Nat.find (model.terminates input), by have h := (Nat.find_spec (model.terminates input)).1; omega⟩

theorem nonterminal_before_length (model : Generator n bound Alphabet) (input : Fin n → Alphabet)
    (time : Fin (model.length input).val) : model.core.generatedToken input time ≠ model.core.separator := by
  intro heq
  apply Nat.find_min (model.terminates input) time.isLt
  exact ⟨by have h := (Nat.find_spec (model.terminates input)).1; have hi := time.isLt; omega, heq⟩

def transcript (model : Generator n bound Alphabet) (input : Fin n → Alphabet) : model.Transcript :=
  ⟨model.length input, fun time => ⟨model.core.generatedToken input time, model.nonterminal_before_length input time⟩⟩

def answer (model : Generator n bound Alphabet) (input : Fin n → Alphabet) : Bool :=
  model.core.transformer.outputLabel (model.core.generatedToken input ((model.length input).val + 1))

def slice (model : Generator n bound Alphabet) (pairing : Alphabet ≃ Bool × Label)
    (labels : Fin n → Label) : TokenAutoregressive.Generator n bound where
  core := model.core.slice pairing labels
  terminates := by
    intro input
    obtain ⟨time, htime, hsep⟩ := model.terminates (fun i => pairing.symm (input i, labels i))
    exact ⟨time, htime, by rw [Core.slice_generatedToken]; exact hsep⟩

theorem slice_length (model : Generator n bound Alphabet) (pairing : Alphabet ≃ Bool × Label)
    (labels : Fin n → Label) (input : Bits n) :
    (model.slice pairing labels).length input = model.length (fun i => pairing.symm (input i, labels i)) := by
  apply Fin.ext
  apply le_antisymm
  · apply Nat.find_min' ((model.slice pairing labels).terminates input)
    have h := Nat.find_spec (model.terminates (fun i => pairing.symm (input i, labels i)))
    refine ⟨h.1, ?_⟩
    change (model.core.slice pairing labels).generatedToken input _ = model.core.separator
    rw [Core.slice_generatedToken]
    exact h.2
  · apply Nat.find_min' (model.terminates (fun i => pairing.symm (input i, labels i)))
    have h := Nat.find_spec ((model.slice pairing labels).terminates input)
    have hs := h.2
    change (model.core.slice pairing labels).generatedToken input _ = model.core.separator at hs
    rw [Core.slice_generatedToken] at hs
    exact ⟨h.1, hs⟩

@[simp] theorem slice_transcript (model : Generator n bound Alphabet) (pairing : Alphabet ≃ Bool × Label)
    (labels : Fin n → Label) (input : Bits n) :
    (model.slice pairing labels).transcript input = model.transcript (fun i => pairing.symm (input i, labels i)) := by
  have word_eq {firstCount secondCount : Fin (bound + 1)}
      (first : Fin firstCount.val → model.Nonterminal)
      (second : Fin secondCount.val → model.Nonterminal)
      (hcount : firstCount = secondCount)
      (htokens : ∀ i j, i.val = j.val → first i = second j) :
      (⟨firstCount, first⟩ : model.Transcript) = ⟨secondCount, second⟩ := by
    subst secondCount
    congr 1
    funext i
    exact htokens i i rfl
  apply word_eq _ _ (model.slice_length pairing labels input)
  intro i j hij
  apply Subtype.ext
  change (model.core.slice pairing labels).generatedToken input i.val =
    model.core.generatedToken (fun k => pairing.symm (input k, labels k)) j.val
  rw [Core.slice_generatedToken, hij]

@[simp] theorem slice_answer (model : Generator n bound Alphabet) (pairing : Alphabet ≃ Bool × Label)
    (labels : Fin n → Label) (input : Bits n) :
    (model.slice pairing labels).answer input = model.answer (fun i => pairing.symm (input i, labels i)) := by
  unfold TokenAutoregressive.Generator.answer answer
  rw [slice_length]
  exact congrArg model.core.transformer.outputLabel (model.core.slice_generatedToken pairing labels input _)

def fiberDepth (model : Generator n bound Alphabet) : ℕ :=
  (model.core.architecture.layers + 2) * TransformerDepthCost.stage model.core.transformer.arithmetic + 4

def predictionSize (model : Generator n bound Alphabet) : ℕ :=
  model.core.architecture.inputBits + TransformerGateCost.total model.core.transformer.arithmetic
    (FixedPrecisionTransformer.sizeBound model.core.architecture) + 1

def fiberSize (model : Generator n bound Alphabet) : ℕ := 3 * (bound + 1) * model.predictionSize + 10

def expectedLength [Fintype Alphabet] [Nonempty Alphabet] (model : Generator n bound Alphabet) : ℝ :=
  (Distribution.uniform (Fin n → Alphabet)).expectation
    (fun input => ((model.length input).val + 1 : ℕ))

theorem uniform_footprint
    [Fintype Alphabet] [Nonempty Alphabet] [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (model : Generator n bound Alphabet)
    (pairing : Alphabet ≃ Bool × Label)
    (correct : ∀ input, model.answer input = Tal.parity (fun i => (pairing (input i)).1))
    (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (Distribution.uniform (Fin n → Alphabet)).mutualInformation id model.transcript := by
  rw [Distribution.mutualInformation_id_eq_entropy]
  have hsize : 1 < model.fiberSize := by unfold fiberSize; omega
  apply paired_uniform_entropy_lower_bound pairing model.transcript _
    (Real.sqrt_pos.mpr (Tal.tailBound_pos _ _ _))
  intro labels candidate
  have hsliced : ∀ input, (model.slice pairing labels).answer input = Tal.parity input := by
    intro input
    rw [slice_answer, correct]
    simp
  let sliced := model.slice pairing labels
  let G := sliced.parityTrace hsliced
  have h := G.transcriptProbability_le_of_correlation (sliced.fiberCircuitFamily hsliced)
    (Footprint.indicatorParityCorrelationBound_of_sign hn
      (Footprint.signParityCorrelationBound_of_tal tal hsize)) candidate
  have hrewrite : (fun input => model.transcript (fun i => pairing.symm (input i, labels i))) = sliced.transcript := by
    funext input
    exact (model.slice_transcript pairing labels input).symm
  rw [hrewrite, Distribution.uniform_pushMass_eq_card]
  simpa only [G, Footprint.ParityTrace.transcriptProbability, Footprint.ParityTrace.transcriptFiber,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, TokenAutoregressive.Generator.parityTrace] using h

theorem nonterminal_card (model : Generator n bound Alphabet) :
    Fintype.card model.Nonterminal = model.core.architecture.vocabulary - 1 := by
  unfold Nonterminal
  rw [Fintype.card_subtype_compl (fun token => token = model.core.separator)]
  simp [Fintype.card_subtype]

def payload (model : Generator n bound Alphabet) (candidate : model.Transcript) :
    List (Fin (Fintype.card model.Nonterminal)) :=
  List.ofFn (fun time => Fintype.equivFin model.Nonterminal (candidate.2 time))

theorem payload_injective (model : Generator n bound Alphabet) : Function.Injective model.payload := by
  intro first second heq
  have hlength := congrArg List.length heq
  simp only [payload, List.length_ofFn] at hlength
  have hcount : first.1 = second.1 := Fin.ext hlength
  rcases first with ⟨firstCount, firstTokens⟩
  rcases second with ⟨secondCount, secondTokens⟩
  dsimp only at hcount
  cases hcount
  congr 1
  funext time
  exact (Fintype.equivFin model.Nonterminal).injective (congrFun (List.ofFn_injective heq) time)

theorem uniform_expected_length_lower_bound
    [Fintype Alphabet] [Nonempty Alphabet] [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (model : Generator n bound Alphabet)
    (pairing : Alphabet ≃ Bool × Label)
    (correct : ∀ input, model.answer input = Tal.parity (fun i => (pairing (input i)).1))
    (hn : 1 ≤ n) (hv : 1 < model.core.architecture.vocabulary) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.expectedLength := by
  have hfootprint := model.uniform_footprint tal pairing correct hn
  rw [Distribution.mutualInformation_id_eq_entropy] at hfootprint
  have hcard := model.nonterminal_card
  have hpositive : 0 < Fintype.card model.Nonterminal := by omega
  have htotal : Fintype.card model.Nonterminal + 1 = model.core.architecture.vocabulary := by omega
  have hcoding := TerminatedCode.entropy_le_expected_terminated_length
    (Distribution.uniform (Fin n → Alphabet)) model.transcript
    (Fintype.card model.Nonterminal) hpositive model.payload model.payload_injective
  rw [htotal] at hcoding
  have hcoding' : (Distribution.uniform (Fin n → Alphabet)).entropy model.transcript ≤
      model.expectedLength * Real.logb 2 (model.core.architecture.vocabulary : ℝ) := by
    simpa [payload, expectedLength, transcript] using hcoding
  have hlog : 0 < Real.logb 2 (model.core.architecture.vocabulary : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hv)
  apply (div_le_iff₀ hlog).mpr
  exact hfootprint.trans hcoding'

end Generator

open TaskReductions

theorem s5_uniform_expected_length
    (tal : Tal.FourierTailTheorem) (model : Generator n bound S5)
    (correct : ∀ input, model.answer input = oddUnit (Equiv.Perm.sign (orderedProduct input)))
    (hn : 1 ≤ n) (hv : 1 < model.core.architecture.vocabulary) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.expectedLength := by
  apply model.uniform_expected_length_lower_bound tal s5Pairing _ hn hv
  intro input
  rw [correct, ← s5StateTrackingParity_eq_product_sign]
  rfl

theorem addition100_uniform_expected_length
    (tal : Tal.FourierTailTheorem) (model : Generator n bound (Fin 100))
    (correct : ∀ input, model.answer input = additionLSB (fun i => (input i).val))
    (hn : 1 ≤ n) (hv : 1 < model.core.architecture.vocabulary) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.expectedLength := by
  apply model.uniform_expected_length_lower_bound tal additionPairing100 _ hn hv
  intro input
  rw [correct, additionLSB_eq_parity]
  rfl

end TokenSymbolic
