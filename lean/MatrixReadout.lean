import TransformerAC0
import Mathlib.Data.Finset.Max

/-!
# Genuine greedy token readout

The matrix semantics computes each vocabulary logit in finite scalar order.
The next token is the least-indexed logit maximizer. This module proves that
the Boolean compiler's readout labels classify exactly that token, and
constructs an exact classifier circuit for every vocabulary symbol.
-/

noncomputable section

namespace TransformerAC0.FixedPrecisionTransformer

variable {a : Architecture}

def logitRank (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (token : Fin a.vocabulary) : Fin (Fintype.card (Bits model.scalarBits)) :=
  model.arithmetic.scalarRank (model.readoutScalarValue state position token)

theorem exists_max_logit (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) :
    ∃ token : Fin a.vocabulary, token ∈ (Finset.univ : Finset (Fin a.vocabulary)) ∧
      ∀ other ∈ (Finset.univ : Finset (Fin a.vocabulary)),
        model.logitRank state position other ≤ model.logitRank state position token := by
  exact Finset.exists_max_image Finset.univ (model.logitRank state position) ⟨⟨0, hv⟩, by simp⟩

def maxLogitToken (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) : Fin a.vocabulary :=
  Classical.choose (model.exists_max_logit state position hv)

def maximizers (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) : Finset (Fin a.vocabulary) :=
  Finset.univ.filter fun token => model.logitRank state position token =
    model.logitRank state position (model.maxLogitToken state position hv)

theorem maximizers_nonempty (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) :
    (model.maximizers state position hv).Nonempty :=
  ⟨model.maxLogitToken state position hv, by simp [maximizers]⟩

def chosenToken (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) : Fin a.vocabulary :=
  (model.maximizers state position hv).min' (model.maximizers_nonempty state position hv)

theorem chosenToken_maximal (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) (other : Fin a.vocabulary) :
    model.logitRank state position other ≤ model.logitRank state position (model.chosenToken state position hv) := by
  have hmem := Finset.min'_mem (model.maximizers state position hv) (model.maximizers_nonempty state position hv)
  have hscore : model.logitRank state position (model.chosenToken state position hv) =
      model.logitRank state position (model.maxLogitToken state position hv) := by
    simpa [maximizers, chosenToken] using hmem
  rw [hscore]
  exact (Classical.choose_spec (model.exists_max_logit state position hv)).2 other (by simp)

theorem chosenToken_minimal_tie (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) (other : Fin a.vocabulary)
    (tie : model.logitRank state position other = model.logitRank state position (model.chosenToken state position hv)) :
    model.chosenToken state position hv ≤ other := by
  have hmem := Finset.min'_mem (model.maximizers state position hv) (model.maximizers_nonempty state position hv)
  have hscore : model.logitRank state position (model.chosenToken state position hv) =
      model.logitRank state position (model.maxLogitToken state position hv) := by
    simpa [maximizers, chosenToken] using hmem
  apply Finset.min'_le
  simp [maximizers, tie, hscore]

theorem chosenToken_winner (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) :
    model.readoutWinnerValue state position (model.chosenToken state position hv) = true := by
  simp only [readoutWinnerValue, decide_eq_true_eq]
  intro other
  by_cases heq : model.chosenToken state position hv = other
  · simp [readoutComparisonValue, heq]
  · by_cases horder : other.val < (model.chosenToken state position hv).val
    · have hmax := model.chosenToken_maximal state position hv other
      have hne : model.logitRank state position other ≠
          model.logitRank state position (model.chosenToken state position hv) := by
        intro htie
        have hmin := model.chosenToken_minimal_tie state position hv other htie
        have hval : (model.chosenToken state position hv).val ≤ other.val := hmin
        omega
      have hlt := lt_of_le_of_ne hmax hne
      simpa [readoutComparisonValue, heq, horder, FixedPrecisionArithmetic.lessEqual_append,
        logitRank] using hlt
    · have hmax := model.chosenToken_maximal state position hv other
      simpa [readoutComparisonValue, heq, horder, FixedPrecisionArithmetic.lessEqual_append,
        logitRank] using hmax

theorem winner_unique (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (first second : Fin a.vocabulary)
    (hfirst : model.readoutWinnerValue state position first = true)
    (hsecond : model.readoutWinnerValue state position second = true) : first = second := by
  by_contra hne
  have hfirst' := (of_decide_eq_true hfirst) second
  have hsecond' := (of_decide_eq_true hsecond) first
  have hne' : second ≠ first := Ne.symm hne
  rcases lt_or_gt_of_ne hne with horder | horder
  · have hv : first.val < second.val := horder
    have hnot : ¬second.val < first.val := by omega
    simp [readoutComparisonValue, hne, hnot, FixedPrecisionArithmetic.lessEqual_append] at hfirst'
    simp [readoutComparisonValue, hne', hv, FixedPrecisionArithmetic.lessEqual_append] at hsecond'
    exact (not_le_of_gt hsecond') hfirst'
  · have hv : second.val < first.val := horder
    have hnot : ¬first.val < second.val := by omega
    simp [readoutComparisonValue, hne, hv, FixedPrecisionArithmetic.lessEqual_append] at hfirst'
    simp [readoutComparisonValue, hne', hnot, FixedPrecisionArithmetic.lessEqual_append] at hsecond'
    exact (not_le_of_gt hfirst') hsecond'

theorem winner_iff_chosenToken (model : FixedPrecisionTransformer a) (state : Bits model.stateBitWidth)
    (position : Fin a.contextLength) (hv : 0 < a.vocabulary) (candidate : Fin a.vocabulary) :
    model.readoutWinnerValue state position candidate = true ↔ candidate = model.chosenToken state position hv := by
  constructor
  · intro h
    exact model.winner_unique state position candidate _ h (model.chosenToken_winner state position hv)
  · intro h
    rw [h]
    exact model.chosenToken_winner state position hv

def hiddenValue (model : FixedPrecisionTransformer a) (input : Bits a.inputBits) : Bits model.stateBitWidth :=
  (List.ofFn model.layer).foldl (fun state parameters => model.layerValue parameters state)
    (model.embeddingValue input)

def runToken (model : FixedPrecisionTransformer a) (hv : 0 < a.vocabulary) (hcontext : 0 < a.contextLength)
    (input : Bits a.inputBits) : Fin a.vocabulary :=
  model.chosenToken (model.hiddenValue input) ⟨a.contextLength - 1, by omega⟩ hv

/-- Boolean readout labels classify precisely the actual greedy token. -/
theorem run_eq_label_runToken (model : FixedPrecisionTransformer a)
    (hv : 0 < a.vocabulary) (hcontext : 0 < a.contextLength) (input : Bits a.inputBits) :
    model.run input = model.outputLabel (model.runToken hv hcontext input) := by
  apply Bool.eq_iff_iff.mpr
  simp only [run, readoutValue, dif_pos hcontext, decide_eq_true_eq]
  change (∃ token, model.outputLabel token = true ∧
      model.readoutWinnerValue (model.hiddenValue input) _ token = true) ↔ _
  simp only [winner_iff_chosenToken model _ _ hv]
  constructor
  · rintro ⟨token, hlabel, heq⟩
    simpa [heq, runToken] using hlabel
  · intro hlabel
    exact ⟨model.runToken hv hcontext input, hlabel, rfl⟩

def withLabel (model : FixedPrecisionTransformer a) (label : Fin a.vocabulary → Bool) :
    FixedPrecisionTransformer a := { model with outputLabel := label }

@[simp] theorem runToken_withLabel (model : FixedPrecisionTransformer a) (label : Fin a.vocabulary → Bool)
    (hv : 0 < a.vocabulary) (hcontext : 0 < a.contextLength) (input : Bits a.inputBits) :
    (model.withLabel label).runToken hv hcontext input = model.runToken hv hcontext input := rfl

/-- An actual compiled matrix circuit classifying one vocabulary token. -/
def tokenClassifier (model : FixedPrecisionTransformer a) (token : Fin a.vocabulary) :
    Circuit a.inputBits 1 :=
  (model.withLabel (fun candidate => decide (candidate = token))).compile

@[simp] theorem eval_tokenClassifier (model : FixedPrecisionTransformer a) (token : Fin a.vocabulary)
    (hv : 0 < a.vocabulary) (hcontext : 0 < a.contextLength) (input : Bits a.inputBits) :
    Circuit.eval (model.tokenClassifier token) input 0 = decide (model.runToken hv hcontext input = token) := by
  rw [tokenClassifier, FixedPrecisionTransformer.compile_correct,
    run_eq_label_runToken _ hv hcontext]
  rfl

theorem tokenClassifier_depth_le (model : FixedPrecisionTransformer a) (token : Fin a.vocabulary) :
    Circuit.depth (model.tokenClassifier token) ≤
      (a.layers + 2) * TransformerDepthCost.stage model.arithmetic :=
  (model.withLabel (fun candidate => decide (candidate = token))).compile_depth_le_fixed

theorem tokenClassifier_size_le (model : FixedPrecisionTransformer a) (token : Fin a.vocabulary) :
    Circuit.gateCount (model.tokenClassifier token) ≤
      TransformerGateCost.total model.arithmetic (FixedPrecisionTransformer.sizeBound a) :=
  (model.withLabel (fun candidate => decide (candidate = token))).compile_gateCount_le_total

end TransformerAC0.FixedPrecisionTransformer
