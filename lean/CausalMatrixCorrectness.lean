import CausalMatrix

/-!
# Shared-weight causal prefix execution

Restricting the context changes neither learned weights nor the output at an
existing causal position. This is proved from numerical execution, layer by
layer, not supplied as an autoregressive-model field.
-/

noncomputable section
namespace CausalMatrix
open TransformerAC0

variable {a : Architecture}

def restrictInput (_model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (input : Bits a.inputBits) : Bits (architecture a length).inputBits := fun wire =>
  let pt := finProdFinEquiv.symm wire
  input (FixedPrecisionTransformer.inputIndex (Fin.castLE bounded pt.1) pt.2)

def StateAgrees (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (short : Bits (restrictContext model length bounded).stateBitWidth) (full : Bits model.stateBitWidth) : Prop :=
  ∀ position coordinate, (restrictContext model length bounded).stateValue short position coordinate =
    model.stateValue full (Fin.castLE bounded position) coordinate

def keyPosition (position : Fin length) (index : Fin (position.val + 1)) : Fin length :=
  ⟨index.val, index.isLt.trans_le (Nat.succ_le_iff.mpr position.isLt)⟩

theorem embedding_agrees (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (input : Bits a.inputBits) :
    StateAgrees model length bounded
      ((restrictContext model length bounded).embeddingValue (restrictInput model length bounded input))
      (model.embeddingValue input) := by
  intro position coordinate
  have hlookup (c : Fin a.halfWidth) :
      (restrictContext model length bounded).tokenScalarValue (restrictInput model length bounded input) position c =
        model.tokenScalarValue input (Fin.castLE bounded position) c := by
    funext bit
    simp [FixedPrecisionTransformer.tokenScalarValue, restrictInput, restrictContext,
      FixedPrecisionTransformer.inputIndex]
    rfl
  have hscalar : (restrictContext model length bounded).embeddingScalarValue
      (restrictInput model length bounded input) position coordinate =
      model.embeddingScalarValue input (Fin.castLE bounded position) coordinate := by
    unfold FixedPrecisionTransformer.embeddingScalarValue
    have hsplit : FixedPrecisionTransformer.hiddenSplit (a := architecture a length) coordinate =
        FixedPrecisionTransformer.hiddenSplit (a := a) coordinate := rfl
    rw [hsplit]
    cases FixedPrecisionTransformer.hiddenSplit (a := a) coordinate with
    | inl c => exact hlookup c
    | inr c => rfl
  funext bit
  simpa only [FixedPrecisionTransformer.stateValue, FixedPrecisionTransformer.embeddingValue,
    FixedPrecisionTransformer.stateBlock, Equiv.symm_apply_apply] using congrFun hscalar bit

theorem linear_agrees (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (matrix : Fin a.hiddenWidth → Fin a.hiddenWidth → Bits model.scalarBits)
    (short full : Fin a.hiddenWidth → Bits model.scalarBits) (coordinate : Fin a.hiddenWidth)
    (agrees : ∀ i, short i = full i) :
    (restrictContext model length bounded).linearValue matrix short coordinate =
      model.linearValue matrix full coordinate := by
  have heq : short = full := funext agrees
  rw [heq]
  rfl

set_option maxHeartbeats 1000000 in
theorem layer_agrees (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (parameters : TransformerLayerParameters a model.scalarBits)
    (short : Bits (restrictContext model length bounded).stateBitWidth) (full : Bits model.stateBitWidth)
    (agrees : StateAgrees model length bounded short full) :
    StateAgrees model length bounded
      ((restrictContext model length bounded).layerValue (layer parameters) short)
      (model.layerValue parameters full) := by
  let small := restrictContext model length bounded
  have hquery head position coordinate : small.queryValue (layer parameters) short head position coordinate =
      model.queryValue parameters full head (Fin.castLE bounded position) coordinate :=
    linear_agrees model length bounded _ _ _ coordinate (agrees position)
  have hkey head position coordinate : small.keyValue (layer parameters) short head position coordinate =
      model.keyValue parameters full head (Fin.castLE bounded position) coordinate :=
    linear_agrees model length bounded _ _ _ coordinate (agrees position)
  have hvalue head position coordinate : small.valueValue (layer parameters) short head position coordinate =
      model.valueValue parameters full head (Fin.castLE bounded position) coordinate :=
    linear_agrees model length bounded _ _ _ coordinate (agrees position)
  have hscore head queryPos keyPos : small.scoreValue (layer parameters) short head queryPos keyPos =
      model.scoreValue parameters full head (Fin.castLE bounded queryPos) (Fin.castLE bounded keyPos) := by
    unfold FixedPrecisionTransformer.scoreValue
    simp_rw [hquery, hkey]
    rfl
  have hexp head queryPos keyPos : small.expScoreValue (layer parameters) short head queryPos keyPos =
      model.expScoreValue parameters full head (Fin.castLE bounded queryPos) (Fin.castLE bounded keyPos) := by
    unfold FixedPrecisionTransformer.expScoreValue
    rw [hscore]
    rfl
  have hdenom head position : small.denominatorValue (layer parameters) short head position =
      model.denominatorValue parameters full head (Fin.castLE bounded position) := by
    change small.aggregateValues (fun index => small.expScoreValue (layer parameters) short head position
      (keyPosition position index)) =
      model.aggregateValues (fun index => model.expScoreValue parameters full head (Fin.castLE bounded position)
        (Fin.castLE bounded (keyPosition position index)))
    simp_rw [hexp]
    rfl
  have hsoftmax head queryPos keyPos : small.softmaxValue (layer parameters) short head queryPos keyPos =
      model.softmaxValue parameters full head (Fin.castLE bounded queryPos) (Fin.castLE bounded keyPos) := by
    unfold FixedPrecisionTransformer.softmaxValue
    rw [hexp, hdenom]
    rfl
  have hhead head position coordinate : small.headOutputValue (layer parameters) short head position coordinate =
      model.headOutputValue parameters full head (Fin.castLE bounded position) coordinate := by
    change small.aggregateValues (fun index => FixedPrecisionTransformer.binaryValue small.arithmetic.multiply
      (small.softmaxValue (layer parameters) short head position (keyPosition position index))
      (small.valueValue (layer parameters) short head (keyPosition position index) coordinate)) =
      model.aggregateValues (fun index => FixedPrecisionTransformer.binaryValue model.arithmetic.multiply
        (model.softmaxValue parameters full head (Fin.castLE bounded position)
          (Fin.castLE bounded (keyPosition position index)))
        (model.valueValue parameters full head (Fin.castLE bounded (keyPosition position index)) coordinate))
    simp_rw [hsoftmax, hvalue]
    rfl
  have hattention position coordinate : small.attentionValue (layer parameters) short position coordinate =
      model.attentionValue parameters full (Fin.castLE bounded position) coordinate := by
    unfold FixedPrecisionTransformer.attentionValue
    simp_rw [hhead]
    rfl
  have hresidual position coordinate : small.attentionResidualValue (layer parameters) short position coordinate =
      model.attentionResidualValue parameters full (Fin.castLE bounded position) coordinate := by
    unfold FixedPrecisionTransformer.attentionResidualValue
    rw [agrees position coordinate, hattention]
    rfl
  have hhidden position coordinate : small.mlpHiddenValue (layer parameters) short position coordinate =
      model.mlpHiddenValue parameters full (Fin.castLE bounded position) coordinate := by
    unfold FixedPrecisionTransformer.mlpHiddenValue
    rw [linear_agrees model length bounded _ _ _ coordinate (hresidual position)]
    rfl
  have houtput position coordinate : small.mlpOutputValue (layer parameters) short position coordinate =
      model.mlpOutputValue parameters full (Fin.castLE bounded position) coordinate :=
    linear_agrees model length bounded _ _ _ coordinate (hhidden position)
  have hfinal position coordinate : small.layerOutputScalarValue (layer parameters) short position coordinate =
      model.layerOutputScalarValue parameters full (Fin.castLE bounded position) coordinate := by
    unfold FixedPrecisionTransformer.layerOutputScalarValue
    rw [hresidual, houtput]
    rfl
  intro position coordinate
  funext bit
  simpa only [FixedPrecisionTransformer.stateValue, FixedPrecisionTransformer.layerValue,
    FixedPrecisionTransformer.stateBlock, Equiv.symm_apply_apply] using congrFun (hfinal position coordinate) bit

theorem fold_agrees (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (parameters : List (TransformerLayerParameters a model.scalarBits))
    (short : Bits (restrictContext model length bounded).stateBitWidth) (full : Bits model.stateBitWidth)
    (agrees : StateAgrees model length bounded short full) :
    StateAgrees model length bounded
      ((parameters.map layer).foldl (fun state p => (restrictContext model length bounded).layerValue p state) short)
      (parameters.foldl (fun state p => model.layerValue p state) full) := by
  induction parameters generalizing short full with
  | nil => exact agrees
  | cons head tail ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih _ _ (layer_agrees model length bounded head short full agrees)

theorem hidden_agrees (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (input : Bits a.inputBits) :
    StateAgrees model length bounded
      ((restrictContext model length bounded).hiddenValue (restrictInput model length bounded input))
      (model.hiddenValue input) := by
  have hlayers : List.ofFn (restrictContext model length bounded).layer = (List.ofFn model.layer).map layer := by
    simp only [List.map_ofFn, Function.comp_def]
    rfl
  unfold FixedPrecisionTransformer.hiddenValue
  rw [hlayers]
  exact fold_agrees model length bounded _ _ _ (embedding_agrees model length bounded input)

theorem readout_agrees (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (input : Bits a.inputBits) (position : Fin length) (token : Fin a.vocabulary) :
    (restrictContext model length bounded).readoutScalarValue
      ((restrictContext model length bounded).hiddenValue (restrictInput model length bounded input)) position token =
      model.readoutScalarValue (model.hiddenValue input) (Fin.castLE bounded position) token := by
  unfold FixedPrecisionTransformer.readoutScalarValue
  have h := hidden_agrees model length bounded input
  unfold StateAgrees at h
  simp_rw [h]
  rfl

theorem chosenToken_agrees (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength)
    (input : Bits a.inputBits) (position : Fin length) (hv : 0 < a.vocabulary) :
    (restrictContext model length bounded).chosenToken
      ((restrictContext model length bounded).hiddenValue (restrictInput model length bounded input)) position hv =
      model.chosenToken (model.hiddenValue input) (Fin.castLE bounded position) hv := by
  let small := restrictContext model length bounded
  let candidate := small.chosenToken (small.hiddenValue (restrictInput model length bounded input)) position hv
  have hwinner := small.chosenToken_winner (small.hiddenValue (restrictInput model length bounded input)) position hv
  have hcomparison other : small.readoutComparisonValue
      (small.hiddenValue (restrictInput model length bounded input)) position candidate other =
      model.readoutComparisonValue (model.hiddenValue input) (Fin.castLE bounded position) candidate other := by
    dsimp only [small]
    unfold FixedPrecisionTransformer.readoutComparisonValue
    simp_rw [readout_agrees]
    rfl
  have hwin : model.readoutWinnerValue (model.hiddenValue input) (Fin.castLE bounded position) candidate = true := by
    change decide (∀ other, model.readoutComparisonValue (model.hiddenValue input)
      (Fin.castLE bounded position) candidate other = true) = true
    apply of_decide_eq_true at hwinner
    apply decide_eq_true
    intro other
    rw [← hcomparison]
    exact hwinner other
  exact (model.winner_iff_chosenToken _ _ hv candidate).mp hwin

end CausalMatrix
