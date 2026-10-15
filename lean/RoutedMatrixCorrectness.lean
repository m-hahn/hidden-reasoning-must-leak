import RoutedMatrix
import MatrixReadout
import CausalMatrixCorrectness

/-!
# Execution of the explicit routing matrices

All operations here are the independent numerical matrix semantics. Integer
identities are lifted to that semantics only after bounding every rounded
accumulation, including its intermediate prefixes.
-/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

namespace RoutedMatrix

open TransformerAC0 CanonicalArithmetic NumericalPrimitives

variable {vocabulary window heads opcodes : ℕ}

def coordinateRepresentation : Coordinate vocabulary window heads opcodes ≃
    Unit ⊕ (Fin vocabulary ⊕ (Fin window ⊕ ((Fin heads × Fin window) ⊕
      (Fin (featureCount vocabulary heads opcodes) ⊕
        (Bits (featureCount vocabulary heads opcodes) ⊕ Fin vocabulary))))) where
  toFun coordinate := match coordinate with
    | .constant => .inl ()
    | .token token => .inr (.inl token)
    | .key position => .inr (.inr (.inl position))
    | .query head position => .inr (.inr (.inr (.inl (head, position))))
    | .feature feature => .inr (.inr (.inr (.inr (.inl feature))))
    | .neuron pattern => .inr (.inr (.inr (.inr (.inr (.inl pattern)))))
    | .output token => .inr (.inr (.inr (.inr (.inr (.inr token)))))
  invFun representation := match representation with
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
            · rcases rest with pattern | token <;> rfl

theorem sum_coordinates (f : Coordinate vocabulary window heads opcodes → ℤ) :
    ∑ c, f c = f .constant + (∑ t, f (.token t)) + (∑ k, f (.key k)) +
      (∑ h, ∑ k, f (.query h k)) + (∑ i, f (.feature i)) +
      (∑ p, f (.neuron p)) + (∑ t, f (.output t)) := by
  rw [← (coordinateRepresentation.symm).sum_comp f]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique,
    coordinateRepresentation, Equiv.symm, add_assoc]

def locationEquiv : Fin (architecture vocabulary window heads opcodes).hiddenWidth ≃
    Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes :=
  (finCongr (by simp [architecture, Architecture.hiddenWidth]; omega)).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr coordinates.symm coordinates.symm))

theorem locationEquiv_apply (i : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    locationEquiv i = location i := by
  change Sum.map coordinates.symm coordinates.symm (FixedPrecisionTransformer.hiddenSplit i) =
    match FixedPrecisionTransformer.hiddenSplit i with
    | .inl c => .inl (coordinates.symm c)
    | .inr c => .inr (coordinates.symm c)
  cases FixedPrecisionTransformer.hiddenSplit i <;> rfl

theorem sum_locations (f : Coordinate vocabulary window heads opcodes ⊕
    Coordinate vocabulary window heads opcodes → ℤ) :
    ∑ i, f (location i) = (∑ c, f (.inl c)) + (∑ c, f (.inr c)) := by
  simp_rw [← locationEquiv_apply]
  rw [locationEquiv.sum_comp, Fintype.sum_sum_type]

theorem scalar_supported (integer : ℤ) (bound : |integer| ≤ offset vocabulary heads opcodes) :
    Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) integer :=
  supports_symmetric_interval _ _ _ integer
    (NumericalMLP.grid_supports_negative _) (NumericalMLP.grid_supports_positive _) bound

theorem scalar_small_supported (integer : ℤ) (bound : |integer| ≤ 1) :
    Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) integer := by
  apply scalar_supported
  exact bound.trans (by unfold offset NumericalMLP.radius; omega)

theorem multiply_scalar (first second : ℤ)
    (hf : Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) first)
    (hs : Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) second) :
    (CanonicalArithmetic.arithmetic (precision vocabulary heads opcodes) 0
      (offset vocabulary heads opcodes)).multiply (Fin.append (scalar first) (scalar second)) =
        scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) (first * second) :=
  multiply_integers _ _ _ _ hf hs

theorem aggregate_scalar (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (terms : Fin count → ℤ) (bound : ∑ i, |terms i| ≤ offset vocabulary heads opcodes) :
    (transformer plan localMap label).aggregateValues (fun i => scalar (terms i)) =
      scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) (∑ i, terms i) := by
  change (CanonicalArithmetic.arithmetic (precision vocabulary heads opcodes) 0
    (offset vocabulary heads opcodes)).roundedSum count (ScalarCircuit.pack (fun i => scalar (terms i))) = _
  rw [← aggregate_eq_matrix_aggregate]
  exact aggregate_signed_exact _ _ _ terms
    (NumericalMLP.grid_supports_negative _) (NumericalMLP.grid_supports_positive _) bound

def embeddingInteger (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl .constant => 1
  | .inl (.token token) => if token = word position then 1 else 0
  | .inr (.key key) => if key = position then 0 else 1
  | .inr (.query head key) => if key = plan.route position head then 1 else 0
  | .inr (.feature feature) => Fin.addCases (fun _ => 0)
      (fun opcode => if opcode = plan.opcode position then 1 else 0) feature
  | _ => 0

theorem embedding_integer_small (plan : Plan vocabulary window heads opcodes)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |embeddingInteger plan word position c| ≤ 1 := by
  rcases c with c | c <;> cases c <;> simp only [embeddingInteger]
  all_goals try { norm_num }
  all_goals try { split_ifs <;> norm_num }
  rename_i feature
  refine Fin.addCases (fun _ => by norm_num) (fun _ => ?_) feature
  simp only [Fin.addCases_right]
  split_ifs <;> norm_num

theorem embedding_scalar (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).stateValue
      ((transformer plan localMap label).embeddingValue (oneHot word)) position coordinate =
        scalar (embeddingInteger plan word position (location coordinate)) := by
  have hflatten : (transformer plan localMap label).stateValue
      ((transformer plan localMap label).embeddingValue (oneHot word)) position coordinate =
      (transformer plan localMap label).embeddingScalarValue (oneHot word) position coordinate := by
    funext bit
    simp [FixedPrecisionTransformer.stateValue, FixedPrecisionTransformer.embeddingValue,
      FixedPrecisionTransformer.stateBlock]
  rw [hflatten]
  unfold FixedPrecisionTransformer.embeddingScalarValue location
  cases hsplit : FixedPrecisionTransformer.hiddenSplit coordinate with
  | inl c =>
      dsimp only
      rw [tokenScalarValue_oneHot]
      unfold tokenEmbedding
      cases coordinates.symm c <;> rfl
  | inr c =>
      dsimp only
      change positionEmbedding plan position c = _
      unfold positionEmbedding
      cases hc : coordinates.symm c <;> try rfl
      rename_i feature
      refine Fin.addCases (fun _ => by simp [embeddingInteger])
        (fun _ => by simp only [embeddingInteger, Fin.addCases_right]) feature

def queryCoefficient (head : Fin heads) : Coordinate vocabulary window heads opcodes ⊕
    Coordinate vocabulary window heads opcodes → Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.key key), .inr (.query h k) => if h = head ∧ k = key then -1 else 0
  | _, _ => 0

def keyCoefficient : Coordinate vocabulary window heads opcodes ⊕
    Coordinate vocabulary window heads opcodes → Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.key key), .inr (.key k) => if k = key then 1 else 0
  | _, _ => 0

def valueCoefficient (head : Fin heads) : Coordinate vocabulary window heads opcodes ⊕
    Coordinate vocabulary window heads opcodes → Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.feature f), .inl (.token t) => if f = headFeature head t then 1 else 0
  | _, _ => 0

def queryInteger (plan : Plan vocabulary window heads opcodes) (head : Fin heads) (position : Fin window) :
    Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.key key) => if key = plan.route position head then -1 else 0
  | _ => 0

def keyInteger (position : Fin window) : Coordinate vocabulary window heads opcodes ⊕
    Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.key key) => if key = position then 0 else 1
  | _ => 0

def valueInteger (head : Fin heads) (word : Fin window → Fin vocabulary) (position : Fin window) :
    Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.feature f) => if f = headFeature head (word position) then 1 else 0
  | _ => 0

theorem queryWeight_scalar (head : Fin heads) (outCoord inCoord : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    queryWeight head outCoord inCoord = scalar (queryCoefficient head (location outCoord) (location inCoord)) := by
  unfold queryWeight
  rcases location outCoord with c | c <;> cases c <;>
    rcases location inCoord with d | d <;> cases d <;> rfl

theorem keyWeight_scalar (head : Fin heads) (outCoord inCoord : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    keyWeight head outCoord inCoord = scalar (keyCoefficient (location outCoord) (location inCoord)) := by
  unfold keyWeight
  rcases location outCoord with c | c <;> cases c <;>
    rcases location inCoord with d | d <;> cases d <;> rfl

theorem valueWeight_scalar (head : Fin heads) (outCoord inCoord : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    valueWeight head outCoord inCoord = scalar (valueCoefficient head (location outCoord) (location inCoord)) := by
  unfold valueWeight
  rcases location outCoord with c | c <;> cases c <;>
    rcases location inCoord with d | d <;> cases d <;> rfl

theorem projection_coefficient_small (head : Fin heads)
    (c d : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |queryCoefficient head c d| ≤ 1 ∧ |keyCoefficient c d| ≤ 1 ∧ |valueCoefficient head c d| ≤ 1 := by
  rcases c with c | c <;> cases c <;> rcases d with d | d <;> cases d <;>
    simp only [queryCoefficient, keyCoefficient, valueCoefficient] <;> try norm_num
  all_goals split_ifs <;> norm_num

theorem query_integer_small (plan : Plan vocabulary window heads opcodes) (head : Fin heads) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |queryInteger plan head position c| ≤ 1 := by
  rcases c with c | c <;> cases c <;> simp only [queryInteger] <;> try norm_num
  split_ifs <;> norm_num

theorem key_integer_small (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |keyInteger (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) position c| ≤ 1 := by
  rcases c with c | c <;> cases c <;> simp only [keyInteger] <;> try norm_num
  split_ifs <;> norm_num

theorem value_integer_small (head : Fin heads) (word : Fin window → Fin vocabulary) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |valueInteger (opcodes := opcodes) head word position c| ≤ 1 := by
  rcases c with c | c <;> cases c <;> simp only [valueInteger] <;> try norm_num
  split_ifs <;> norm_num

theorem projection_integer_sums (plan : Plan vocabulary window heads opcodes)
    (word : Fin window → Fin vocabulary) (head : Fin heads) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    (∑ i, queryCoefficient head c (location i) * embeddingInteger plan word position (location i)) =
      queryInteger plan head position c ∧
    (∑ i, keyCoefficient c (location i) * embeddingInteger plan word position (location i)) =
      keyInteger position c ∧
    (∑ i, valueCoefficient head c (location i) * embeddingInteger plan word position (location i)) =
      valueInteger head word position c := by
  rw [sum_locations (fun d => queryCoefficient head c d * embeddingInteger plan word position d),
    sum_locations (fun d => keyCoefficient c d * embeddingInteger plan word position d),
    sum_locations (fun d => valueCoefficient head c d * embeddingInteger plan word position d)]
  simp_rw [sum_coordinates]
  rcases c with c | c <;> cases c <;>
    simp [queryCoefficient, keyCoefficient, valueCoefficient, embeddingInteger,
      queryInteger, keyInteger, valueInteger, ite_and, ite_mul, mul_ite]
  rename_i key
  constructor
  · simp [eq_comm]
  · rw [Finset.sum_congr rfl (fun i _ =>
      (show (if i = position then (0 : ℤ) else if i = key then 1 else 0) =
        if i = key then (if key = position then 0 else 1) else 0 by
          by_cases h : i = key <;> simp [h]))]
    simp

theorem projection_absolute_sums (plan : Plan vocabulary window heads opcodes)
    (word : Fin window → Fin vocabulary) (head : Fin heads) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    (∑ i, |queryCoefficient head c (location i) * embeddingInteger plan word position (location i)|) ≤ 1 ∧
    (∑ i, |keyCoefficient c (location i) * embeddingInteger plan word position (location i)|) ≤ 1 ∧
    (∑ i, |valueCoefficient head c (location i) * embeddingInteger plan word position (location i)|) ≤ 1 := by
  rw [sum_locations (fun d => |queryCoefficient head c d * embeddingInteger plan word position d|),
    sum_locations (fun d => |keyCoefficient c d * embeddingInteger plan word position d|),
    sum_locations (fun d => |valueCoefficient head c d * embeddingInteger plan word position d|)]
  simp_rw [sum_coordinates]
  rcases c with c | c <;> cases c <;>
    simp [queryCoefficient, keyCoefficient, valueCoefficient, embeddingInteger,
      ite_and, ite_mul, mul_ite, abs_mul, apply_ite abs] <;> try norm_num
  case inl.feature => split_ifs <;> norm_num
  rename_i key
  constructor
  · split_ifs <;> norm_num
  · calc
      _ ≤ ∑ i : Fin window, if i = key then (1 : ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> omega
      _ = 1 := by simp

theorem linear_scalar (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (matrix : Fin (architecture vocabulary window heads opcodes).hiddenWidth →
      Fin (architecture vocabulary window heads opcodes).hiddenWidth → Bits (precision vocabulary heads opcodes))
    (source : Fin (architecture vocabulary window heads opcodes).hiddenWidth → Bits (precision vocabulary heads opcodes))
    (coefficients : Fin (architecture vocabulary window heads opcodes).hiddenWidth → ℤ)
    (values : Fin (architecture vocabulary window heads opcodes).hiddenWidth → ℤ)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth)
    (hmatrix : ∀ i, matrix coordinate i = scalar (coefficients i))
    (hsource : ∀ i, source i = scalar (values i))
    (hc : ∀ i, Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) (coefficients i))
    (hv : ∀ i, Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) (values i))
    (bound : ∑ i, |coefficients i * values i| ≤ offset vocabulary heads opcodes) :
    (transformer plan localMap label).linearValue matrix source coordinate = scalar (∑ i, coefficients i * values i) := by
  unfold FixedPrecisionTransformer.linearValue
  have hterms : (fun i => FixedPrecisionTransformer.binaryValue
      (transformer plan localMap label).arithmetic.multiply (matrix coordinate i) (source i)) =
      (fun i => scalar (coefficients i * values i)) := by
    funext i
    rw [hmatrix, hsource]
    exact multiply_scalar _ _ (hc i) (hv i)
  rw [hterms]
  exact aggregate_scalar plan localMap label _ bound

theorem projections_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (head : Fin heads) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).queryValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head position coordinate =
        scalar (queryInteger plan head position (location coordinate)) ∧
    (transformer plan localMap label).keyValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head position coordinate =
        scalar (keyInteger position (location coordinate)) ∧
    (transformer plan localMap label).valueValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head position coordinate =
        scalar (valueInteger head word position (location coordinate)) := by
  have hs := projection_integer_sums plan word head position (location coordinate)
  have hb := projection_absolute_sums plan word head position (location coordinate)
  have hsource := embedding_scalar plan localMap label word position
  have hvalues i := scalar_small_supported (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes)
    _ (embedding_integer_small plan word position (location i))
  have hr : (1 : ℤ) ≤ offset vocabulary heads opcodes := by unfold offset NumericalMLP.radius; omega
  refine ⟨?_, ?_, ?_⟩
  · change (transformer plan localMap label).linearValue (queryWeight head) _ coordinate = _
    rw [linear_scalar plan localMap label _ _ _ _ coordinate (queryWeight_scalar head coordinate) hsource
      (fun i => scalar_small_supported _ (projection_coefficient_small head _ _).1) hvalues (hb.1.trans hr), hs.1]
  · change (transformer plan localMap label).linearValue (keyWeight head) _ coordinate = _
    rw [linear_scalar plan localMap label _ _ _ _ coordinate (keyWeight_scalar head coordinate) hsource
      (fun i => scalar_small_supported _ (projection_coefficient_small head _ _).2.1) hvalues (hb.2.1.trans hr), hs.2.1]
  · change (transformer plan localMap label).linearValue (valueWeight head) _ coordinate = _
    rw [linear_scalar plan localMap label _ _ _ _ coordinate (valueWeight_scalar head coordinate) hsource
      (fun i => scalar_small_supported _ (projection_coefficient_small head _ _).2.2) hvalues (hb.2.2.trans hr), hs.2.2]

theorem aggregate_product_scalar (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (first second : Fin count → ℤ)
    (hf : ∀ i, Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) (first i))
    (hs : ∀ i, Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) (second i))
    (bound : ∑ i, |first i * second i| ≤ offset vocabulary heads opcodes) :
    (transformer plan localMap label).aggregateValues (fun i =>
      FixedPrecisionTransformer.binaryValue (transformer plan localMap label).arithmetic.multiply
        (scalar (first i)) (scalar (second i))) = scalar (∑ i, first i * second i) := by
  have hterms : (fun i => FixedPrecisionTransformer.binaryValue
      (transformer plan localMap label).arithmetic.multiply (scalar (first i)) (scalar (second i))) =
      (fun i => scalar (first i * second i)) := by
    funext i
    exact multiply_scalar _ _ (hf i) (hs i)
  rw [hterms]
  exact aggregate_scalar plan localMap label _ bound

theorem score_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (head : Fin heads) (queryPos keyPos : Fin window) :
    (transformer plan localMap label).scoreValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head queryPos keyPos =
        scalar (if keyPos = plan.route queryPos head then 0 else -1) := by
  have hquery c := (projections_exact plan localMap label word head queryPos c).1
  have hkey c := (projections_exact plan localMap label word head keyPos c).2.1
  have hsum : (∑ i, queryInteger plan head queryPos (location i) * keyInteger keyPos (location i)) =
      if keyPos = plan.route queryPos head then (0 : ℤ) else -1 := by
    rw [sum_locations (fun c => queryInteger plan head queryPos c * keyInteger keyPos c)]
    simp_rw [sum_coordinates]
    simp only [queryInteger, keyInteger, ite_mul, mul_ite, zero_mul, mul_zero, neg_mul,
      one_mul, mul_one, zero_add, add_zero, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl (fun i _ =>
      (show (if i = keyPos then (0 : ℤ) else if i = plan.route queryPos head then -1 else 0) =
        if i = plan.route queryPos head then (if keyPos = plan.route queryPos head then 0 else -1) else 0 by
          by_cases h : i = plan.route queryPos head <;> simp [h, eq_comm]))]
    simp
  have hbound : (∑ i, |queryInteger plan head queryPos (location i) * keyInteger keyPos (location i)|) ≤ 1 := by
    rw [sum_locations (fun c => |queryInteger plan head queryPos c * keyInteger keyPos c|)]
    simp_rw [sum_coordinates]
    simp [queryInteger, keyInteger, ite_mul, mul_ite, apply_ite abs]
    calc
      _ ≤ ∑ i : Fin window, if i = plan.route queryPos head then (1 : ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> omega
      _ = 1 := by simp
  unfold FixedPrecisionTransformer.scoreValue
  simp_rw [hquery, hkey]
  rw [aggregate_product_scalar plan localMap label _ _
    (fun i => scalar_small_supported _ (query_integer_small plan head queryPos (location i)))
    (fun i => scalar_small_supported _ (key_integer_small keyPos (location i)))
    (hbound.trans (by unfold offset NumericalMLP.radius; omega)), hsum]

theorem exp_score_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (head : Fin heads) (queryPos keyPos : Fin window) :
    (transformer plan localMap label).expScoreValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head queryPos keyPos =
        scalar (if keyPos = plan.route queryPos head then 1 else 0) := by
  unfold FixedPrecisionTransformer.expScoreValue
  rw [score_exact]
  by_cases heq : keyPos = plan.route queryPos head
  · simp only [heq, if_true]
    simpa only [transformer, scalar, Int.cast_zero, Int.cast_one] using
      exponentiate_zero (precision vocabulary heads opcodes) (offset vocabulary heads opcodes)
      (scalar_small_supported 0 (by norm_num))
  · simp only [heq, if_false]
    simpa only [transformer, scalar, Int.cast_neg, Int.cast_zero, Int.cast_one] using
      exponentiate_negative_one (precision vocabulary heads opcodes) (offset vocabulary heads opcodes)
      (scalar_small_supported (-1) (by norm_num))

def causalKey (position : Fin window) (index : Fin (position.val + 1)) : Fin window :=
  ⟨index.val, index.isLt.trans_le (Nat.succ_le_iff.mpr position.isLt)⟩

def routedIndex (plan : Plan vocabulary window heads opcodes) (head : Fin heads) (position : Fin window) :
    Fin (position.val + 1) := ⟨(plan.route position head).val, Nat.lt_succ_of_le (plan.causal position head)⟩

@[simp] theorem causalKey_routedIndex (plan : Plan vocabulary window heads opcodes) (head : Fin heads) (position : Fin window) :
    causalKey position (routedIndex plan head position) = plan.route position head := rfl

theorem causalKey_eq_route (plan : Plan vocabulary window heads opcodes) (head : Fin heads) (position : Fin window)
    (index : Fin (position.val + 1)) : causalKey position index = plan.route position head ↔
      index = routedIndex plan head position := by
  simp only [Fin.ext_iff, causalKey, routedIndex]

theorem denominator_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (head : Fin heads) (position : Fin window) :
    (transformer plan localMap label).denominatorValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head position = scalar 1 := by
  change (transformer plan localMap label).aggregateValues (fun index =>
    (transformer plan localMap label).expScoreValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head position (causalKey position index)) = _
  simp_rw [exp_score_exact, causalKey_eq_route]
  rw [aggregate_scalar plan localMap label _ (by
    simp only [apply_ite abs, abs_one, abs_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    unfold offset NumericalMLP.radius; omega)]
  simp

theorem softmax_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (head : Fin heads) (queryPos keyPos : Fin window) :
    (transformer plan localMap label).softmaxValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head queryPos keyPos =
        scalar (if keyPos = plan.route queryPos head then 1 else 0) := by
  unfold FixedPrecisionTransformer.softmaxValue
  rw [exp_score_exact, denominator_exact]
  by_cases heq : keyPos = plan.route queryPos head
  · simpa only [heq, if_true, FixedPrecisionTransformer.binaryValue, transformer, scalar, Int.cast_one] using
      divide_by_one (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) 1
        (scalar_small_supported 1 (by norm_num)) (scalar_small_supported 1 (by norm_num))
  · simpa only [heq, if_false, FixedPrecisionTransformer.binaryValue, transformer, scalar, Int.cast_zero, Int.cast_one] using
      divide_by_one (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) 0
        (scalar_small_supported 0 (by norm_num)) (scalar_small_supported 1 (by norm_num))

theorem head_output_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (head : Fin heads) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).headOutputValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) head position coordinate =
        scalar (valueInteger head word (plan.route position head) (location coordinate)) := by
  change (transformer plan localMap label).aggregateValues (fun index =>
    FixedPrecisionTransformer.binaryValue (transformer plan localMap label).arithmetic.multiply
      ((transformer plan localMap label).softmaxValue (layer localMap)
        ((transformer plan localMap label).embeddingValue (oneHot word)) head position (causalKey position index))
      ((transformer plan localMap label).valueValue (layer localMap)
        ((transformer plan localMap label).embeddingValue (oneHot word)) head (causalKey position index) coordinate)) = _
  have hvalue k := (projections_exact plan localMap label word head k coordinate).2.2
  simp_rw [softmax_exact, hvalue, causalKey_eq_route]
  rw [aggregate_product_scalar plan localMap label _ _
    (fun _ => scalar_small_supported _ (by split_ifs <;> norm_num))
    (fun i => scalar_small_supported _ (value_integer_small head word (causalKey position i) (location coordinate)))
    (by
      simp only [ite_mul, one_mul, zero_mul, apply_ite abs, abs_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, causalKey_routedIndex]
      exact (value_integer_small head word _ _).trans (by unfold offset NumericalMLP.radius; omega))]
  simp [ite_mul]

def headFeatures (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) : Fin (featureCount vocabulary heads opcodes) → ℤ :=
  Fin.addCases (fun index => let ht := finProdFinEquiv.symm index
    if word (plan.route position ht.1) = ht.2 then 1 else 0) (fun _ => 0)

def attentionInteger (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.feature f) => headFeatures plan word position f
  | _ => 0

theorem headFeatures_small (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (feature : Fin (featureCount vocabulary heads opcodes)) :
    |headFeatures plan word position feature| ≤ 1 := by
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) feature
  · simp only [headFeatures, Fin.addCases_left]
    split_ifs <;> norm_num
  · simp [headFeatures]

theorem headFeatures_nonnegative (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (feature : Fin (featureCount vocabulary heads opcodes)) :
    0 ≤ headFeatures plan word position feature := by
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) feature
  · simp only [headFeatures, Fin.addCases_left]
    split_ifs <;> norm_num
  · simp [headFeatures]

theorem head_sum (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (feature : Fin (featureCount vocabulary heads opcodes)) :
    (∑ head, if feature = headFeature head (word (plan.route position head)) then (1 : ℤ) else 0) =
      headFeatures plan word position feature := by
  refine Fin.addCases (fun index => ?_) (fun opcode => ?_) feature
  · obtain ⟨⟨head, token⟩, rfl⟩ := finProdFinEquiv.surjective index
    have hpred (h : Fin heads) : Fin.castAdd opcodes (finProdFinEquiv (head, token)) =
        headFeature h (word (plan.route position h)) ↔ h = head ∧ word (plan.route position h) = token := by
      unfold headFeature
      rw [Fin.castAdd_inj, Equiv.apply_eq_iff_eq]
      simp [Prod.mk.injEq, eq_comm]
    simp_rw [hpred, ite_and]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, headFeatures,
      Fin.addCases_left, Equiv.symm_apply_apply]
  · have hpred (h : Fin heads) : Fin.natAdd (heads * vocabulary) opcode ≠
        headFeature h (word (plan.route position h)) := by
      intro heq
      have hv := congrArg Fin.val heq
      change heads * vocabulary + opcode.val = (finProdFinEquiv (h, word (plan.route position h))).val at hv
      have ht := (finProdFinEquiv (h, word (plan.route position h))).isLt
      omega
    simp only [hpred, if_false, Finset.sum_const_zero, headFeatures, Fin.addCases_right]

theorem attention_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).attentionValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) position coordinate =
        scalar (attentionInteger plan word position (location coordinate)) := by
  have hsum : (∑ head, valueInteger head word (plan.route position head) (location coordinate)) =
      attentionInteger plan word position (location coordinate) := by
    rcases location coordinate with c | c <;> cases c <;>
      simp only [valueInteger, attentionInteger, Finset.sum_const_zero]
    exact head_sum plan word position _
  have habs : (∑ head, |valueInteger head word (plan.route position head) (location coordinate)|) ≤ 1 := by
    rcases location coordinate with c | c <;> cases c <;>
      simp only [valueInteger, abs_zero, Finset.sum_const_zero] <;> try norm_num
    simp only [apply_ite abs, abs_one, abs_zero, head_sum]
    exact (le_abs_self _).trans (headFeatures_small plan word position _)
  unfold FixedPrecisionTransformer.attentionValue
  simp_rw [head_output_exact]
  exact (aggregate_scalar plan localMap label
    (fun head => valueInteger head word (plan.route position head) (location coordinate))
    (habs.trans (by unfold offset NumericalMLP.radius; omega))).trans
      (congrArg (scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes)) hsum)

def residualInteger (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (coordinate : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes) : ℤ :=
  embeddingInteger plan word position coordinate + attentionInteger plan word position coordinate

theorem residual_small (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (coordinate : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes) : |residualInteger plan word position coordinate| ≤ 1 := by
  rcases coordinate with c | c <;> cases c <;>
    simp only [residualInteger, embeddingInteger, attentionInteger, zero_add, add_zero] <;> try norm_num
  all_goals try { split_ifs <;> norm_num }
  · exact headFeatures_small plan word position _
  · rename_i feature
    refine Fin.addCases (fun _ => by norm_num) (fun _ => ?_) feature
    simp only [Fin.addCases_right]
    split_ifs <;> norm_num

theorem residual_absolute_terms (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (coordinate : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes) :
    |embeddingInteger plan word position coordinate| + |attentionInteger plan word position coordinate| ≤ 1 := by
  rcases coordinate with c | c <;> cases c <;>
    simp only [embeddingInteger, attentionInteger, abs_zero, zero_add, add_zero] <;> try norm_num
  all_goals try { split_ifs <;> norm_num }
  · exact headFeatures_small plan word position _
  · rename_i feature
    refine Fin.addCases (fun _ => by norm_num) (fun _ => ?_) feature
    simp only [Fin.addCases_right]
    split_ifs <;> norm_num

theorem round_scalar (integer : ℤ) :
    (CanonicalArithmetic.arithmetic (precision vocabulary heads opcodes) 0
      (offset vocabulary heads opcodes)).round (scalar integer) =
        scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) integer := by
  rfl

theorem pair_scalar (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (first second : ℤ) (bound : |first| + |second| ≤ offset vocabulary heads opcodes) :
    (transformer plan localMap label).aggregateValues
      (FixedPrecisionTransformer.pairValues (scalar first) (scalar second)) = scalar (first + second) := by
  have hterms : FixedPrecisionTransformer.pairValues
      (scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) first) (scalar second) =
      (fun i => scalar (FixedPrecisionTransformer.pairValues first second i)) := by
    funext i
    fin_cases i <;> rfl
  rw [hterms, aggregate_scalar plan localMap label _ (by
    simpa [Fin.sum_univ_two, FixedPrecisionTransformer.pairValues] using bound)]
  simp only [Fin.sum_univ_two]
  rfl

theorem residual_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).attentionResidualValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) position coordinate =
        scalar (residualInteger plan word position (location coordinate)) := by
  unfold FixedPrecisionTransformer.attentionResidualValue
  rw [embedding_scalar, attention_exact, pair_scalar plan localMap label _ _
    ((residual_absolute_terms plan word position _).trans (by unfold offset NumericalMLP.radius; omega))]
  exact round_scalar _

theorem residual_feature (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (feature : Fin (featureCount vocabulary heads opcodes)) :
    residualInteger plan word position (.inl (.feature feature)) +
      residualInteger plan word position (.inr (.feature feature)) =
        NumericalMLP.bitInteger (features plan word position feature) := by
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) feature <;>
    simp [residualInteger, embeddingInteger, attentionInteger, headFeatures,
      features, NumericalMLP.bitInteger, eq_comm]

theorem residual_nonnegative (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (coordinate : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes) : 0 ≤ residualInteger plan word position coordinate := by
  rcases coordinate with c | c <;> cases c <;>
    simp only [residualInteger, embeddingInteger, attentionInteger, zero_add, add_zero] <;> try norm_num
  all_goals try { split_ifs <;> norm_num }
  · exact headFeatures_nonnegative plan word position _
  · rename_i feature
    refine Fin.addCases (fun _ => by norm_num) (fun _ => ?_) feature
    simp only [Fin.addCases_right]
    split_ifs <;> norm_num

def mlpInCoefficient : Coordinate vocabulary window heads opcodes ⊕
    Coordinate vocabulary window heads opcodes → Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.neuron pattern), .inl .constant => NumericalMLP.bias pattern
  | .inl (.neuron pattern), .inl (.feature f) => NumericalMLP.slope (pattern f)
  | .inl (.neuron pattern), .inr (.feature f) => NumericalMLP.slope (pattern f)
  | _, _ => 0

def innerInteger (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.neuron pattern) => 1 - NumericalMLP.mismatchCount pattern (features plan word position)
  | _ => 0

@[simp] theorem residual_constant (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) : residualInteger plan word position (.inl .constant) = 1 := rfl

def hiddenInteger (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.neuron pattern) => if features plan word position = pattern then 1 else 0
  | _ => 0

theorem mlpInWeight_scalar (outCoord inCoord : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    mlpInWeight outCoord inCoord = scalar (mlpInCoefficient (location outCoord) (location inCoord)) := by
  unfold mlpInWeight
  rcases location outCoord with c | c <;> cases c <;>
    rcases location inCoord with d | d <;> cases d <;> rfl

theorem mlp_in_supported (c d : Coordinate vocabulary window heads opcodes ⊕
    Coordinate vocabulary window heads opcodes) :
    Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) (mlpInCoefficient c d) := by
  apply scalar_supported
  rcases c with c | c <;> cases c <;> rcases d with d | d <;> cases d <;>
    simp only [mlpInCoefficient] <;> try { rw [abs_zero]; exact_mod_cast Nat.zero_le _ }
  · exact (NumericalMLP.abs_bias_le _).trans (by unfold offset NumericalMLP.radius; omega)
  all_goals unfold NumericalMLP.slope; split_ifs <;> norm_num <;> unfold offset NumericalMLP.radius <;> omega

theorem abs_slope (b : Bool) : |NumericalMLP.slope b| = 1 := by
  cases b <;> norm_num [NumericalMLP.slope]

theorem mlp_inner_sum (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (c : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes) :
    (∑ i, mlpInCoefficient c (location i) * residualInteger plan word position (location i)) =
      innerInteger plan word position c := by
  rw [sum_locations (fun d => mlpInCoefficient c d * residualInteger plan word position d)]
  simp_rw [sum_coordinates]
  rcases c with c | c <;> cases c <;>
    simp only [mlpInCoefficient, zero_mul, Finset.sum_const_zero, zero_add, add_zero, innerInteger,
      residual_constant, mul_one]
  rename_i pattern
  change NumericalMLP.bias pattern +
    (∑ f, NumericalMLP.slope (pattern f) * residualInteger plan word position (.inl (.feature f))) +
    (∑ f, NumericalMLP.slope (pattern f) * residualInteger plan word position (.inr (.feature f))) = _
  rw [add_assoc, ← Finset.sum_add_distrib]
  simp_rw [← mul_add, residual_feature]
  simpa only [Fin.sum_univ_succ, NumericalMLP.integerTerms, Fin.cases_zero, Fin.cases_succ] using
    NumericalMLP.integerTerms_sum pattern (features plan word position)

theorem mlp_inner_absolute_sum (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (c : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes) :
    (∑ i, |mlpInCoefficient c (location i) * residualInteger plan word position (location i)|) ≤
      offset vocabulary heads opcodes := by
  rw [sum_locations (fun d => |mlpInCoefficient c d * residualInteger plan word position d|)]
  simp_rw [sum_coordinates]
  rcases c with c | c <;> cases c <;>
    simp only [mlpInCoefficient, zero_mul, abs_zero, Finset.sum_const_zero, zero_add, add_zero,
      residual_constant, mul_one]
  all_goals try { exact_mod_cast Nat.zero_le (offset vocabulary heads opcodes) }
  rename_i pattern
  change |NumericalMLP.bias pattern| +
    (∑ f, |NumericalMLP.slope (pattern f) * residualInteger plan word position (.inl (.feature f))|) +
    (∑ f, |NumericalMLP.slope (pattern f) * residualInteger plan word position (.inr (.feature f))|) ≤ _
  simp_rw [abs_mul, abs_slope, one_mul, abs_of_nonneg (residual_nonnegative plan word position _)]
  rw [add_assoc, ← Finset.sum_add_distrib]
  simp_rw [residual_feature]
  have hb := NumericalMLP.abs_bias_le pattern
  have ht := (NumericalMLP.trueCount_bounds (features plan word position)).2
  unfold offset NumericalMLP.radius
  push_cast
  omega

theorem mlp_hidden_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).mlpHiddenValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) position coordinate =
        scalar (hiddenInteger plan word position (location coordinate)) := by
  unfold FixedPrecisionTransformer.mlpHiddenValue
  change (transformer plan localMap label).arithmetic.relu
    ((transformer plan localMap label).linearValue mlpInWeight _ coordinate) = _
  rw [linear_scalar plan localMap label _ _ _ _ coordinate (mlpInWeight_scalar coordinate)
    (residual_exact plan localMap label word position) (fun i => mlp_in_supported _ _)
    (fun i => scalar_small_supported _ (residual_small plan word position (location i)))
    (mlp_inner_absolute_sum plan word position (location coordinate)), mlp_inner_sum]
  have hs : Supports (precision vocabulary heads opcodes) (offset vocabulary heads opcodes)
      (innerInteger plan word position (location coordinate)) := by
    rw [← mlp_inner_sum]
    apply scalar_supported
    exact (Finset.abs_sum_le_sum_abs _ _).trans (mlp_inner_absolute_sum plan word position _)
  have hrelu : (transformer plan localMap label).arithmetic.relu
      (scalar (innerInteger plan word position (location coordinate))) =
      scalar (max 0 (innerInteger plan word position (location coordinate))) :=
    relu_integer (precision vocabulary heads opcodes) (offset vocabulary heads opcodes) _ hs
  rw [hrelu]
  rcases location coordinate with c | c <;> cases c <;>
    simp only [innerInteger, hiddenInteger, max_self, scalar]
  rw [NumericalMLP.neuron_margin]

def mlpOutCoefficient (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) :
    Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes →
      Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.output token), .inl (.neuron pattern) => if localMap pattern = token then 1 else 0
  | _, _ => 0

def outputInteger (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (input : Bits (featureCount vocabulary heads opcodes)) : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.output token) => if localMap input = token then 1 else 0
  | _ => 0

theorem mlpOutWeight_scalar (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (outCoord inCoord : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    mlpOutWeight localMap outCoord inCoord =
      scalar (mlpOutCoefficient localMap (location outCoord) (location inCoord)) := by
  unfold mlpOutWeight
  rcases location outCoord with c | c <;> cases c <;>
    rcases location inCoord with d | d <;> cases d <;> rfl

theorem mlp_out_coefficient_small (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (c d : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |mlpOutCoefficient localMap c d| ≤ 1 := by
  rcases c with c | c <;> cases c <;> rcases d with d | d <;> cases d <;>
    simp only [mlpOutCoefficient] <;> try norm_num
  split_ifs <;> norm_num

theorem hidden_integer_small (plan : Plan vocabulary window heads opcodes) (word : Fin window → Fin vocabulary)
    (position : Fin window) (c : Coordinate vocabulary window heads opcodes ⊕
      Coordinate vocabulary window heads opcodes) : |hiddenInteger plan word position c| ≤ 1 := by
  rcases c with c | c <;> cases c <;> simp only [hiddenInteger] <;> try norm_num
  split_ifs <;> norm_num

theorem mlp_output_sum (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    (∑ i, mlpOutCoefficient localMap c (location i) * hiddenInteger plan word position (location i)) =
      outputInteger localMap (features plan word position) c := by
  rw [sum_locations (fun d => mlpOutCoefficient localMap c d * hiddenInteger plan word position d)]
  simp_rw [sum_coordinates]
  rcases c with c | c <;> cases c <;>
    simp [mlpOutCoefficient, hiddenInteger, outputInteger, ite_mul, mul_ite]

theorem mlp_output_absolute_sum (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    (∑ i, |mlpOutCoefficient localMap c (location i) * hiddenInteger plan word position (location i)|) ≤ 1 := by
  rw [sum_locations (fun d => |mlpOutCoefficient localMap c d * hiddenInteger plan word position d|)]
  simp_rw [sum_coordinates]
  rcases c with c | c <;> cases c <;>
    (simp [mlpOutCoefficient, hiddenInteger, ite_mul, mul_ite, apply_ite abs]; try norm_num)
  split_ifs <;> norm_num

theorem mlp_output_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).mlpOutputValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) position coordinate =
        scalar (outputInteger localMap (features plan word position) (location coordinate)) := by
  change (transformer plan localMap label).linearValue (mlpOutWeight localMap) _ coordinate = _
  rw [linear_scalar plan localMap label _ _ _ _ coordinate (mlpOutWeight_scalar localMap coordinate)
    (mlp_hidden_exact plan localMap label word position)
    (fun i => scalar_small_supported _ (mlp_out_coefficient_small localMap _ _))
    (fun i => scalar_small_supported _ (hidden_integer_small plan word position (location i)))
    ((mlp_output_absolute_sum plan localMap word position (location coordinate)).trans
      (by unfold offset NumericalMLP.radius; omega)), mlp_output_sum]

def finalInteger (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) : ℤ :=
  residualInteger plan word position c + outputInteger localMap (features plan word position) c

theorem final_absolute_terms (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |residualInteger plan word position c| + |outputInteger localMap (features plan word position) c| ≤ 1 := by
  have hr := residual_small plan word position c
  rcases c with c | c <;> cases c <;> simp only [outputInteger, abs_zero, add_zero] <;> try exact hr
  simp only [residualInteger, embeddingInteger, attentionInteger, zero_add, abs_zero]
  split_ifs <;> norm_num

theorem final_integer_small (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |finalInteger plan localMap word position c| ≤ 1 :=
  (abs_add _ _).trans (final_absolute_terms plan localMap word position c)

theorem layer_output_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).layerOutputScalarValue (layer localMap)
      ((transformer plan localMap label).embeddingValue (oneHot word)) position coordinate =
        scalar (finalInteger plan localMap word position (location coordinate)) := by
  unfold FixedPrecisionTransformer.layerOutputScalarValue
  rw [residual_exact, mlp_output_exact, pair_scalar plan localMap label _ _
    ((final_absolute_terms plan localMap word position _).trans (by unfold offset NumericalMLP.radius; omega))]
  exact round_scalar _

theorem hidden_scalar_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    (transformer plan localMap label).stateValue
      ((transformer plan localMap label).hiddenValue (oneHot word)) position coordinate =
        scalar (finalInteger plan localMap word position (location coordinate)) := by
  have hsingle : (transformer plan localMap label).hiddenValue (oneHot word) =
      (transformer plan localMap label).layerValue (layer localMap)
        ((transformer plan localMap label).embeddingValue (oneHot word)) := by
    simp [FixedPrecisionTransformer.hiddenValue, transformer, architecture, List.ofFn_succ]
  rw [hsingle]
  have hflatten : (transformer plan localMap label).stateValue
      ((transformer plan localMap label).layerValue (layer localMap)
        ((transformer plan localMap label).embeddingValue (oneHot word))) position coordinate =
      (transformer plan localMap label).layerOutputScalarValue (layer localMap)
        ((transformer plan localMap label).embeddingValue (oneHot word)) position coordinate := by
    funext bit
    simp [FixedPrecisionTransformer.stateValue, FixedPrecisionTransformer.layerValue,
      FixedPrecisionTransformer.stateBlock]
  rw [hflatten]
  exact layer_output_exact plan localMap label word position coordinate

def readoutCoefficient (token : Fin vocabulary) : Coordinate vocabulary window heads opcodes ⊕
    Coordinate vocabulary window heads opcodes → ℤ
  | .inl (.output candidate) => if candidate = token then 1 else 0
  | _ => 0

theorem readoutWeight_scalar (token : Fin vocabulary)
    (coordinate : Fin (architecture vocabulary window heads opcodes).hiddenWidth) :
    readoutWeight token coordinate = scalar (readoutCoefficient token (location coordinate)) := by
  unfold readoutWeight
  rcases location coordinate with c | c <;> cases c <;> rfl

theorem readout_coefficient_small (token : Fin vocabulary)
    (c : Coordinate vocabulary window heads opcodes ⊕ Coordinate vocabulary window heads opcodes) :
    |readoutCoefficient token c| ≤ 1 := by
  rcases c with c | c <;> cases c <;> simp only [readoutCoefficient] <;> try norm_num
  split_ifs <;> norm_num

theorem readout_scalar_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window) (token : Fin vocabulary) :
    (transformer plan localMap label).readoutScalarValue
      ((transformer plan localMap label).hiddenValue (oneHot word)) position token =
        scalar (if localMap (features plan word position) = token then 1 else 0) := by
  have hsum : (∑ i, readoutCoefficient token (location i) * finalInteger plan localMap word position (location i)) =
      if localMap (features plan word position) = token then (1 : ℤ) else 0 := by
    rw [sum_locations (fun c => readoutCoefficient token c * finalInteger plan localMap word position c)]
    simp_rw [sum_coordinates]
    simp [readoutCoefficient, finalInteger, residualInteger, embeddingInteger, attentionInteger,
      outputInteger, ite_mul, mul_ite]
  have habs : (∑ i, |readoutCoefficient token (location i) * finalInteger plan localMap word position (location i)|) ≤ 1 := by
    rw [sum_locations (fun c => |readoutCoefficient token c * finalInteger plan localMap word position c|)]
    simp_rw [sum_coordinates]
    simp [readoutCoefficient, finalInteger, residualInteger, embeddingInteger, attentionInteger,
      outputInteger, ite_mul, mul_ite, apply_ite abs]
    split_ifs <;> norm_num
  change (transformer plan localMap label).aggregateValues (fun coordinate =>
    FixedPrecisionTransformer.binaryValue (transformer plan localMap label).arithmetic.multiply
      (readoutWeight token coordinate)
      ((transformer plan localMap label).stateValue
        ((transformer plan localMap label).hiddenValue (oneHot word)) position coordinate)) = _
  simp_rw [readoutWeight_scalar, hidden_scalar_exact]
  rw [aggregate_product_scalar plan localMap label _ _
    (fun i => scalar_small_supported _ (readout_coefficient_small token (location i)))
    (fun i => scalar_small_supported _ (final_integer_small plan localMap word position (location i)))
    (habs.trans (by unfold offset NumericalMLP.radius; omega)), hsum]

/-- The real greedy vocabulary readout selects the local-map value at every
causal position. No attention/MLP correctness certificate is an argument. -/
theorem chosen_token_exact (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (position : Fin window) (hv : 0 < vocabulary) :
    (transformer plan localMap label).chosenToken
      ((transformer plan localMap label).hiddenValue (oneHot word)) position hv =
        localMap (features plan word position) := by
  by_contra hne
  have hmax := (transformer plan localMap label).chosenToken_maximal
    ((transformer plan localMap label).hiddenValue (oneHot word)) position hv (localMap (features plan word position))
  simp only [FixedPrecisionTransformer.logitRank, readout_scalar_exact, if_true,
    if_neg (Ne.symm hne)] at hmax
  change rank (precision vocabulary heads opcodes) (scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) 1) ≤
    rank (precision vocabulary heads opcodes) (scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) 0) at hmax
  have hnumeric := (value_le_iff_rank_le (precision vocabulary heads opcodes) 0
    (offset vocabulary heads opcodes) _ _).mpr hmax
  have hone : value (precision vocabulary heads opcodes) 0 (offset vocabulary heads opcodes)
      (scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) 1) = 1 := by
    simpa only [scalar, Int.cast_one] using value_encode_integer (precision vocabulary heads opcodes)
      (offset vocabulary heads opcodes) 1 (scalar_small_supported 1 (by norm_num))
  have hzero : value (precision vocabulary heads opcodes) 0 (offset vocabulary heads opcodes)
      (scalar (vocabulary := vocabulary) (heads := heads) (opcodes := opcodes) 0) = 0 := by
    simpa only [scalar, Int.cast_zero] using value_encode_integer (precision vocabulary heads opcodes)
      (offset vocabulary heads opcodes) 0 (scalar_small_supported 0 (by norm_num))
  rw [hone, hzero] at hnumeric
  norm_num at hnumeric

/-- End-to-end execution of the original matrix Transformer on a literal
context word, including Q/K/V, numerical softmax, both residuals, the two
MLP matrices, and the unique greedy output token. -/
theorem run_token_correct (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (hv : 0 < vocabulary) (hwindow : 0 < window) :
    (transformer plan localMap label).runToken hv hwindow (oneHot word) =
      localMap (features plan word ⟨window - 1, by omega⟩) :=
  chosen_token_exact plan localMap label word _ hv

theorem run_correct (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (hv : 0 < vocabulary) (hwindow : 0 < window) :
    (transformer plan localMap label).run (oneHot word) =
      label (localMap (features plan word ⟨window - 1, by omega⟩)) := by
  rw [FixedPrecisionTransformer.run_eq_label_runToken _ hv hwindow, run_token_correct]
  rfl

/-- The same wide matrices run on every shorter context. Only literal input
positions and the absolute-position table are restricted. Future tokens are
not passed to the shorter execution. -/
theorem run_token_prefix_correct (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (length : ℕ) (bounded : length ≤ window)
    (hv : 0 < vocabulary) (hlength : 0 < length) :
    (CausalMatrix.restrictContext (transformer plan localMap label) length bounded).runToken hv hlength
      (CausalMatrix.restrictInput (transformer plan localMap label) length bounded (oneHot word)) =
        localMap (features plan word (Fin.castLE bounded ⟨length - 1, by omega⟩)) := by
  unfold FixedPrecisionTransformer.runToken
  rw [CausalMatrix.chosenToken_agrees]
  exact chosen_token_exact plan localMap label word _ hv

theorem prefix_input_literal (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (length : ℕ) (bounded : length ≤ window)
    (position : Fin length) (token : Fin vocabulary) :
    CausalMatrix.restrictInput (transformer plan localMap label) length bounded (oneHot word)
      (finProdFinEquiv (position, token)) = decide (token = word (Fin.castLE bounded position)) := by
  simp [CausalMatrix.restrictInput, oneHot, FixedPrecisionTransformer.inputIndex]

end RoutedMatrix
