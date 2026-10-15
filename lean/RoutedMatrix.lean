import NumericalAttention
import NumericalMLP
import CausalMatrix

/-!
# Explicit shared one-layer routing/local-map matrices

This constructor contains actual token embeddings, absolute position vectors,
Q/K/V matrices, numerical MLP matrices, and unembedding. The finite local map
is compiled into a constant-width truth table; it is not stored as a layer
function in the resulting Transformer. The context-dependent coordinate
blocks grow linearly, while scalar precision and the local-map table remain
fixed. `RoutedMatrixCorrectness` proves end-to-end numerical execution of
these matrices, separately from this construction and dimension accounting.
-/

noncomputable section

namespace RoutedMatrix

open TransformerAC0 CanonicalArithmetic

def featureCount (vocabulary heads opcodes : ℕ) : ℕ := heads * vocabulary + opcodes

inductive Coordinate (vocabulary window heads opcodes : ℕ)
  | constant
  | token (index : Fin vocabulary)
  | key (position : Fin window)
  | query (head : Fin heads) (position : Fin window)
  | feature (index : Fin (featureCount vocabulary heads opcodes))
  | neuron (pattern : Bits (featureCount vocabulary heads opcodes))
  | output (index : Fin vocabulary)
  deriving DecidableEq, Fintype

variable {vocabulary window heads opcodes : ℕ}

abbrev Coordinates := Coordinate vocabulary window heads opcodes

def coordinates : Coordinates (vocabulary := vocabulary) (window := window) (heads := heads) (opcodes := opcodes) ≃
    Fin (Fintype.card (Coordinate vocabulary window heads opcodes)) := Fintype.equivFin _

def architecture (vocabulary window heads opcodes : ℕ) : Architecture where
  vocabulary := vocabulary
  halfWidth := Fintype.card (Coordinate vocabulary window heads opcodes)
  layers := 1
  heads := heads
  contextLength := window

def location (index : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes :=
  match FixedPrecisionTransformer.hiddenSplit index with
  | .inl tokenCoordinate => .inl (coordinates.symm tokenCoordinate)
  | .inr positionCoordinate => .inr (coordinates.symm positionCoordinate)

def headFeature (head : Fin heads) (token : Fin vocabulary) : Fin (featureCount vocabulary heads opcodes) :=
  Fin.castAdd opcodes (finProdFinEquiv (head, token))

def opcodeFeature (opcode : Fin opcodes) : Fin (featureCount vocabulary heads opcodes) :=
  Fin.natAdd (heads * vocabulary) opcode

structure Plan (vocabulary window heads opcodes : ℕ) where
  route : Fin window → Fin heads → Fin window
  causal : ∀ position head, route position head ≤ position
  opcode : Fin window → Fin opcodes

def features (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) : Bits (featureCount vocabulary heads opcodes) :=
  Fin.addCases
    (fun index => let headToken := finProdFinEquiv.symm index
      decide (word (plan.route position headToken.1) = headToken.2))
    (fun opcode => decide (plan.opcode position = opcode))

def precision (vocabulary heads opcodes : ℕ) : ℕ :=
  NumericalMLP.precision (featureCount vocabulary heads opcodes)

def offset (vocabulary heads opcodes : ℕ) : ℕ :=
  NumericalMLP.radius (featureCount vocabulary heads opcodes)

def scalar (integer : ℤ) : Bits (precision vocabulary heads opcodes) :=
  encode (precision vocabulary heads opcodes) 0 (offset vocabulary heads opcodes) (integer : ℝ)

def tokenEmbedding (token : Fin vocabulary) (coordinate : Fin (Fintype.card (Coordinate vocabulary window heads opcodes))) :
    Bits (precision vocabulary heads opcodes) :=
  match coordinates.symm coordinate with
  | .constant => scalar 1
  | .token candidate => scalar (if candidate = token then 1 else 0)
  | _ => scalar 0

def positionEmbedding (plan : Plan vocabulary window heads opcodes) (position : Fin window)
    (coordinate : Fin (Fintype.card (Coordinate vocabulary window heads opcodes))) : Bits (precision vocabulary heads opcodes) :=
  match coordinates.symm coordinate with
  | .key candidate => scalar (if candidate = position then 0 else 1)
  | .query head candidate => scalar (if candidate = plan.route position head then 1 else 0)
  | .feature feature =>
      Fin.addCases (fun _ => scalar 0) (fun opcode => scalar (if opcode = plan.opcode position then 1 else 0)) feature
  | _ => scalar 0

def queryWeight (head : Fin heads)
    (output input : Fin (architecture vocabulary window heads opcodes).hiddenWidth) : Bits (precision vocabulary heads opcodes) :=
  match location output, location input with
  | .inl (.key outputPosition), .inr (.query inputHead inputPosition) =>
      scalar (if inputHead = head ∧ inputPosition = outputPosition then -1 else 0)
  | _, _ => scalar 0

def keyWeight (_head : Fin heads)
    (output input : Fin (architecture vocabulary window heads opcodes).hiddenWidth) : Bits (precision vocabulary heads opcodes) :=
  match location output, location input with
  | .inl (.key outputPosition), .inr (.key inputPosition) => scalar (if inputPosition = outputPosition then 1 else 0)
  | _, _ => scalar 0

def valueWeight (head : Fin heads)
    (output input : Fin (architecture vocabulary window heads opcodes).hiddenWidth) : Bits (precision vocabulary heads opcodes) :=
  match location output, location input with
  | .inl (.feature feature), .inl (.token token) => scalar (if feature = headFeature head token then 1 else 0)
  | _, _ => scalar 0

def mlpInWeight (output input : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    Bits (precision vocabulary heads opcodes) :=
  match location output, location input with
  | .inl (.neuron pattern), .inl .constant => scalar (NumericalMLP.bias pattern)
  | .inl (.neuron pattern), .inl (.feature feature) => scalar (NumericalMLP.slope (pattern feature))
  | .inl (.neuron pattern), .inr (.feature feature) => scalar (NumericalMLP.slope (pattern feature))
  | _, _ => scalar 0

def mlpOutWeight (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (output input : Fin (architecture vocabulary window heads opcodes).hiddenWidth) : Bits (precision vocabulary heads opcodes) :=
  match location output, location input with
  | .inl (.output token), .inl (.neuron pattern) => scalar (if localMap pattern = token then 1 else 0)
  | _, _ => scalar 0

def layer (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) :
    TransformerLayerParameters (architecture vocabulary window heads opcodes) (precision vocabulary heads opcodes) where
  query := queryWeight
  key := keyWeight
  value := valueWeight
  mlpIn := mlpInWeight
  mlpOut := mlpOutWeight localMap

def readoutWeight (token : Fin vocabulary) (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    Bits (precision vocabulary heads opcodes) :=
  match location coordinate with
  | .inl (.output candidate) => scalar (if candidate = token then 1 else 0)
  | _ => scalar 0

/-- This is an instance of the original matrix Transformer, not the semantic
attention/local-map record. The local map is materialized in its weights. -/
def transformer (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (label : Fin vocabulary → Bool) : FixedPrecisionTransformer (architecture vocabulary window heads opcodes) where
  scalarBits := precision vocabulary heads opcodes
  arithmetic := CanonicalArithmetic.arithmetic (precision vocabulary heads opcodes) 0 (offset vocabulary heads opcodes)
  position := positionEmbedding plan
  tokenEmbedding := tokenEmbedding
  layer := fun _ => layer localMap
  readoutWeight := readoutWeight
  outputLabel := label

theorem one_layer : (architecture vocabulary window heads opcodes).layers = 1 := rfl

theorem fixed_heads : (architecture vocabulary window heads opcodes).heads = heads := rfl

theorem fixed_precision (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool) :
    (transformer plan localMap label).scalarBits = precision vocabulary heads opcodes := rfl

theorem coordinate_card :
    Fintype.card (Coordinate vocabulary window heads opcodes) =
      1 + 2 * vocabulary + (heads + 1) * window + featureCount vocabulary heads opcodes +
        2 ^ featureCount vocabulary heads opcodes := by
  let representation : Coordinate vocabulary window heads opcodes ≃
      Unit ⊕ (Fin vocabulary ⊕ (Fin window ⊕ ((Fin heads × Fin window) ⊕
        (Fin (featureCount vocabulary heads opcodes) ⊕
          (Bits (featureCount vocabulary heads opcodes) ⊕ Fin vocabulary))))) :=
    { toFun := fun coordinate => match coordinate with
        | .constant => .inl ()
        | .token token => .inr (.inl token)
        | .key position => .inr (.inr (.inl position))
        | .query head position => .inr (.inr (.inr (.inl (head, position))))
        | .feature feature => .inr (.inr (.inr (.inr (.inl feature))))
        | .neuron pattern => .inr (.inr (.inr (.inr (.inr (.inl pattern)))))
        | .output token => .inr (.inr (.inr (.inr (.inr (.inr token)))))
      invFun := fun representation => match representation with
        | .inl _ => .constant
        | .inr (.inl token) => .token token
        | .inr (.inr (.inl position)) => .key position
        | .inr (.inr (.inr (.inl (head, position)))) => .query head position
        | .inr (.inr (.inr (.inr (.inl feature)))) => .feature feature
        | .inr (.inr (.inr (.inr (.inr (.inl pattern))))) => .neuron pattern
        | .inr (.inr (.inr (.inr (.inr (.inr token))))) => .output token
      left_inv := by intro coordinate; cases coordinate <;> rfl
      right_inv := by
        intro representation
        rcases representation with singleton | rest
        · cases singleton; rfl
        · rcases rest with token | rest
          · rfl
          · rcases rest with position | rest
            · rfl
            · rcases rest with query | rest
              · cases query; rfl
              · rcases rest with feature | rest
                · rfl
                · rcases rest with pattern | token <;> rfl }
  rw [Fintype.card_congr representation]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_bool]
  ring

def dimensionConstant (vocabulary heads opcodes : ℕ) : ℕ :=
  2 + 2 * vocabulary + heads + featureCount vocabulary heads opcodes + 2 ^ featureCount vocabulary heads opcodes

/-- The local finite-map table is a context-independent constant. The only
growing coordinate blocks are the key/positional selector blocks. -/
theorem hidden_dimension_linear : (architecture vocabulary window heads opcodes).hiddenWidth ≤
    2 * dimensionConstant vocabulary heads opcodes * (window + 1) := by
  have hbase : 1 + 2 * vocabulary + featureCount vocabulary heads opcodes +
      2 ^ featureCount vocabulary heads opcodes ≤ dimensionConstant vocabulary heads opcodes := by
    calc
      _ ≤ (1 + 2 * vocabulary + featureCount vocabulary heads opcodes +
          2 ^ featureCount vocabulary heads opcodes) + (heads + 1) := Nat.le_add_right _ _
      _ = _ := by unfold dimensionConstant; ring
  have hheads : heads + 1 ≤ dimensionConstant vocabulary heads opcodes := by
    calc
      _ ≤ (1 + 2 * vocabulary + featureCount vocabulary heads opcodes +
          2 ^ featureCount vocabulary heads opcodes) + (heads + 1) := Nat.le_add_left _ _
      _ = _ := by unfold dimensionConstant; ring
  have hcard : Fintype.card (Coordinate vocabulary window heads opcodes) ≤
      dimensionConstant vocabulary heads opcodes * (window + 1) := by
    rw [coordinate_card]
    calc
      _ = (1 + 2 * vocabulary + featureCount vocabulary heads opcodes + 2 ^ featureCount vocabulary heads opcodes) +
          (heads + 1) * window := by ring
      _ ≤ dimensionConstant vocabulary heads opcodes + dimensionConstant vocabulary heads opcodes * window :=
        Nat.add_le_add hbase (Nat.mul_le_mul_right window hheads)
      _ = _ := by ring
  simpa only [Architecture.hiddenWidth, architecture, Nat.mul_assoc] using Nat.mul_le_mul_left 2 hcard

theorem parameter_count_quadratic : (architecture vocabulary window heads opcodes).parameterCount ≤
    (3 * vocabulary * dimensionConstant vocabulary heads opcodes +
      4 * (3 * heads + 2) * dimensionConstant vocabulary heads opcodes ^ 2) * (window + 1) ^ 2 := by
  have hwidth : (architecture vocabulary window heads opcodes).halfWidth ≤
      dimensionConstant vocabulary heads opcodes * (window + 1) := by
    have h := hidden_dimension_linear (vocabulary := vocabulary) (window := window) (heads := heads) (opcodes := opcodes)
    unfold Architecture.hiddenWidth at h
    rw [Nat.mul_assoc] at h
    omega
  have hsquare := Nat.pow_le_pow_left hwidth 2
  have hone : 1 ≤ window + 1 := by omega
  have hlinear : window + 1 ≤ (window + 1) ^ 2 := by nlinarith
  change 3 * vocabulary * (architecture vocabulary window heads opcodes).halfWidth +
    (3 * heads + 2) * (2 * (architecture vocabulary window heads opcodes).halfWidth) ^ 2 ≤ _
  calc
    _ ≤ 3 * vocabulary * (dimensionConstant vocabulary heads opcodes * (window + 1)) +
        (3 * heads + 2) * (2 * (dimensionConstant vocabulary heads opcodes * (window + 1))) ^ 2 := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ hwidth
      · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hwidth) 2)
    _ ≤ (3 * vocabulary * dimensionConstant vocabulary heads opcodes +
        4 * (3 * heads + 2) * dimensionConstant vocabulary heads opcodes ^ 2) * (window + 1) ^ 2 := by
      nlinarith [Nat.mul_le_mul_left (3 * vocabulary * dimensionConstant vocabulary heads opcodes) hlinear]

def oneHot (word : Fin window → Fin vocabulary) : Bits (architecture vocabulary window heads opcodes).inputBits :=
  fun wire =>
    let location := finProdFinEquiv.symm wire
    decide (location.2 = word location.1)

/-- The matrix input is the literal one-hot encoding of the context word;
no attended value or next local-map output is computed by preprocessing. -/
theorem tokenScalarValue_oneHot (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (coordinate : Fin (Fintype.card (Coordinate vocabulary window heads opcodes))) :
    (transformer plan localMap label).tokenScalarValue (oneHot word) position coordinate =
      tokenEmbedding (window := window) (word position) coordinate := by
  funext bit
  simp [FixedPrecisionTransformer.tokenScalarValue, oneHot, FixedPrecisionTransformer.inputIndex, transformer]

end RoutedMatrix
