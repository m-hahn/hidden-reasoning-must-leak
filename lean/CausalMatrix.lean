import MatrixReadout

/-!
# Prefix restriction of one shared matrix Transformer

Autoregression uses causal prefixes of increasing length, not unrelated
models for different times. This module restricts only the absolute-position
table and context length. Scalar precision, arithmetic, vocabulary, token
embeddings, Q/K/V and MLP matrices, unembedding, and layer/head counts remain
the same. The restricted model executes the existing matrix semantics.
-/

noncomputable section

namespace CausalMatrix

open TransformerAC0

def architecture (original : Architecture) (length : ℕ) : Architecture :=
  { original with contextLength := length }

def layer (original : TransformerLayerParameters a bits) :
    TransformerLayerParameters (architecture a length) bits where
  query := original.query
  key := original.key
  value := original.value
  mlpIn := original.mlpIn
  mlpOut := original.mlpOut

def restrictContext (model : FixedPrecisionTransformer a) (length : ℕ) (bounded : length ≤ a.contextLength) :
    FixedPrecisionTransformer (architecture a length) where
  scalarBits := model.scalarBits
  arithmetic := model.arithmetic
  position := fun position coordinate => model.position (Fin.castLE bounded position) coordinate
  tokenEmbedding := model.tokenEmbedding
  layer := fun index => layer (model.layer index)
  readoutWeight := model.readoutWeight
  outputLabel := model.outputLabel

@[simp] theorem prefix_scalarBits (model : FixedPrecisionTransformer a) (length : ℕ)
    (bounded : length ≤ a.contextLength) : (restrictContext model length bounded).scalarBits = model.scalarBits := rfl

@[simp] theorem prefix_arithmetic (model : FixedPrecisionTransformer a) (length : ℕ)
    (bounded : length ≤ a.contextLength) : (restrictContext model length bounded).arithmetic = model.arithmetic := rfl

@[simp] theorem prefix_position (model : FixedPrecisionTransformer a) (length : ℕ)
    (bounded : length ≤ a.contextLength) (position : Fin length) (coordinate : Fin a.halfWidth) :
    (restrictContext model length bounded).position position coordinate =
      model.position (Fin.castLE bounded position) coordinate := rfl

/-- All learned numerical parameters are literally shared across prefixes. -/
theorem learned_weights_shared (model : FixedPrecisionTransformer a) (length : ℕ)
    (bounded : length ≤ a.contextLength) :
    (restrictContext model length bounded).tokenEmbedding = model.tokenEmbedding ∧
      (restrictContext model length bounded).readoutWeight = model.readoutWeight ∧
      (∀ index, ((restrictContext model length bounded).layer index).query = (model.layer index).query) ∧
      (∀ index, ((restrictContext model length bounded).layer index).key = (model.layer index).key) ∧
      (∀ index, ((restrictContext model length bounded).layer index).value = (model.layer index).value) ∧
      (∀ index, ((restrictContext model length bounded).layer index).mlpIn = (model.layer index).mlpIn) ∧
      (∀ index, ((restrictContext model length bounded).layer index).mlpOut = (model.layer index).mlpOut) := by
  exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

@[simp] theorem parameter_count_shared (original : Architecture) (length : ℕ) :
    (architecture original length).parameterCount = original.parameterCount := rfl

/-- The layer count and fixed-precision circuit depth do not grow when the
same Transformer is run on longer causal prefixes. -/
theorem prefix_compile_depth (model : FixedPrecisionTransformer a) (length : ℕ)
    (bounded : length ≤ a.contextLength) :
    Circuit.depth (restrictContext model length bounded).compile ≤
      (a.layers + 2) * TransformerDepthCost.stage model.arithmetic :=
  (restrictContext model length bounded).compile_depth_le_fixed

theorem sizeBound_prefix (a : Architecture) (length : ℕ) (bounded : length ≤ a.contextLength) :
    FixedPrecisionTransformer.sizeBound (architecture a length) ≤ FixedPrecisionTransformer.sizeBound a := by
  simp only [FixedPrecisionTransformer.sizeBound, Architecture.localBase, architecture, Architecture.hiddenWidth]
  omega

theorem gateCost_monotone (arithmetic : FixedPrecisionArithmetic bits) :
    Monotone (TransformerGateCost.total arithmetic) := by
  intro first second h
  simp only [TransformerGateCost.total, TransformerGateCost.embedding, TransformerGateCost.layer,
    TransformerGateCost.layerScalar, TransformerGateCost.unary, TransformerGateCost.aggregate,
    TransformerGateCost.attentionResidual, TransformerGateCost.attention, TransformerGateCost.headOutput,
    TransformerGateCost.binary, TransformerGateCost.softmax, TransformerGateCost.expScore,
    TransformerGateCost.score, TransformerGateCost.projected, TransformerGateCost.linear,
    TransformerGateCost.denominator, TransformerGateCost.mlpOutput, TransformerGateCost.mlpHidden,
    TransformerGateCost.readout, TransformerGateCost.readoutWinner, TransformerGateCost.readoutComparison,
    FixedPrecisionArithmetic.sumUpper]
  gcongr

end CausalMatrix
