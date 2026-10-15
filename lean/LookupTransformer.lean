import TransformerAC0

/-!
# A concrete finite lookup Transformer

Every function on a nonempty finite token alphabet is realized here by an
actual zero-layer instance of the matrix-level `FixedPrecisionTransformer`.
The construction is deliberately simple: token embeddings and unembedding
weights are matching one-hot vectors, rounded addition is maximum in the
finite scalar order, and greedy readout therefore recovers the input token.
This is useful for discharging finite local maps in the constructive upper
bounds without a realization hypothesis.
-/

noncomputable section

namespace LookupTransformer

open TransformerAC0

abbrev Scalar := Bits 1

theorem card_scalar : Fintype.card Scalar = 2 := by simp [Scalar, Bits]

def scalarEquivFinTwo : Scalar ≃ Fin 2 where
  toFun value := if value 0 then 1 else 0
  invFun value := fun _ => decide (value = 1)
  left_inv value := by
    funext index
    fin_cases index
    cases h : value 0 <;> simp [h]
  right_inv value := by
    fin_cases value <;> simp

def rank : Scalar ≃ Fin (Fintype.card Scalar) :=
  scalarEquivFinTwo.trans
    (Equiv.cast (congrArg Fin card_scalar.symm))

def low : Scalar := fun _ => false

def high : Scalar := fun _ => true

def left (pair : Bits (1 + 1)) : Scalar := fun bit => pair (Fin.castAdd 1 bit)

def right (pair : Bits (1 + 1)) : Scalar := fun bit => pair (Fin.natAdd 1 bit)

@[simp] theorem rank_low : rank low = 0 := by
  apply Fin.ext
  change (if low 0 then 1 else 0 : Fin 2).val = 0
  simp [low]

@[simp] theorem rank_high : rank high = Fin.last 1 := by
  apply Fin.ext
  change (if high 0 then 1 else 0 : Fin 2).val = 1
  simp [high]

theorem low_ne_high : low ≠ high := by
  intro h
  have := congrArg rank h
  simp [card_scalar] at this

theorem high_ne_low : high ≠ low := low_ne_high.symm

@[simp] theorem left_append (first second : Scalar) :
    left (Fin.append first second) = first := by
  funext bit
  simp [left]

@[simp] theorem right_append (first second : Scalar) :
    right (Fin.append first second) = second := by
  funext bit
  rw [right]
  rw [Fin.append_right]

/-- Boolean-like arithmetic whose rounded sums are ordered maxima. -/
def arithmetic : FixedPrecisionArithmetic 1 where
  zero := low
  scalarRank := rank
  round := id
  roundedAdd := fun pair => rank.symm (max (rank (left pair)) (rank (right pair)))
  roundedAdd_monotone := by
    intro term a b hab
    simp only [left_append, right_append, Equiv.apply_symm_apply]
    exact max_le_max hab le_rfl
  multiply := fun pair =>
    if left pair = high ∧ right pair = high then high else low
  exponentiate := id
  divide := fun pair => left pair
  relu := id

@[simp] theorem roundedAdd_low_left (value : Scalar) :
    arithmetic.roundedAdd (Fin.append low value) = value := by
  apply rank.injective
  simp [arithmetic, rank_low]

@[simp] theorem roundedAdd_high_left (value : Scalar) :
    arithmetic.roundedAdd (Fin.append high value) = high := by
  apply rank.injective
  have hle : rank value ≤ Fin.last 1 := by
    exact Fin.le_last _
  have hle' : rank value ≤ (1 : Fin 2) := by simpa using hle
  simp [arithmetic, rank_high, max_eq_left hle']

@[simp] theorem multiply_high_high :
    arithmetic.multiply (Fin.append high high) = high := by
  simp [arithmetic]

@[simp] theorem multiply_low_left (value : Scalar) :
    arithmetic.multiply (Fin.append low value) = low := by
  simp [arithmetic, low_ne_high]

@[simp] theorem multiply_low_right (value : Scalar) :
    arithmetic.multiply (Fin.append value low) = low := by
  simp [arithmetic, low_ne_high]

theorem scalar_eq_low_or_high (value : Scalar) : value = low ∨ value = high := by
  by_cases h : value 0 = true
  · right
    funext bit
    fin_cases bit
    simpa [high] using h
  · left
    funext bit
    fin_cases bit
    simp only [Bool.not_eq_true] at h
    simpa [low] using h

@[simp] theorem roundedSumWord_eq_high_iff (word : List Scalar) :
    arithmetic.roundedSumWord word = high ↔ high ∈ word := by
  suffices hgeneral : ∀ accumulator : Scalar,
      word.foldl
          (fun current term => arithmetic.roundedAdd (Fin.append current term))
          accumulator = high ↔
        accumulator = high ∨ high ∈ word by
    simpa [FixedPrecisionArithmetic.roundedSumWord, arithmetic, low_ne_high]
      using hgeneral low
  induction word with
  | nil => simp
  | cons head tail ih =>
      intro accumulator
      rw [List.foldl_cons, ih]
      rcases scalar_eq_low_or_high accumulator with hacc | hacc <;>
        rcases scalar_eq_low_or_high head with hhead | hhead <;>
        subst accumulator <;> subst head <;> simp [low_ne_high, high_ne_low]

@[simp] theorem multiply_eq_high_iff (first second : Scalar) :
    arithmetic.multiply (Fin.append first second) = high ↔
      first = high ∧ second = high := by
  simp [arithmetic, low_ne_high]

def architecture (vocabulary : ℕ) : Architecture where
  vocabulary := vocabulary
  halfWidth := vocabulary
  layers := 0
  heads := 0
  contextLength := 1

def scalar (value : Bool) : Scalar := if value then high else low

private abbrev lookupHiddenSplit {vocabulary : ℕ}
    (coordinate : Fin (architecture vocabulary).hiddenWidth) :
    Fin vocabulary ⊕ Fin vocabulary :=
  FixedPrecisionTransformer.hiddenSplit coordinate

private abbrev lookupInputIndex {vocabulary : ℕ}
    (position : Fin (architecture vocabulary).contextLength)
    (token : Fin vocabulary) : Fin (architecture vocabulary).inputBits :=
  FixedPrecisionTransformer.inputIndex position token

private def tokenCoordinate {vocabulary : ℕ} (coordinate : Fin vocabulary) :
    Fin (architecture vocabulary).hiddenWidth :=
  Fin.cast (by simp [architecture, Architecture.hiddenWidth]; omega)
    ((@finSumFinEquiv vocabulary vocabulary) (Sum.inl coordinate))

private def positionCoordinate {vocabulary : ℕ} (coordinate : Fin vocabulary) :
    Fin (architecture vocabulary).hiddenWidth :=
  Fin.cast (by simp [architecture, Architecture.hiddenWidth]; omega)
    ((@finSumFinEquiv vocabulary vocabulary) (Sum.inr coordinate))

@[simp] theorem hiddenSplit_tokenCoordinate {vocabulary : ℕ}
    (coordinate : Fin vocabulary) :
    FixedPrecisionTransformer.hiddenSplit (tokenCoordinate coordinate) =
      Sum.inl coordinate := by
  apply finSumFinEquiv.injective
  simp [FixedPrecisionTransformer.hiddenSplit, tokenCoordinate, architecture,
    Architecture.hiddenWidth]

@[simp] theorem hiddenSplit_positionCoordinate {vocabulary : ℕ}
    (coordinate : Fin vocabulary) :
    FixedPrecisionTransformer.hiddenSplit (positionCoordinate coordinate) =
      Sum.inr coordinate := by
  apply finSumFinEquiv.injective
  simp [FixedPrecisionTransformer.hiddenSplit, positionCoordinate, architecture,
    Architecture.hiddenWidth]

/-- The concrete lookup-table Transformer. -/
def transformer (vocabulary : ℕ) (label : Fin vocabulary → Bool) :
    FixedPrecisionTransformer (architecture vocabulary) where
  scalarBits := 1
  arithmetic := arithmetic
  position := fun _ _ => low
  tokenEmbedding := fun token coordinate => scalar (token = coordinate)
  layer := Fin.elim0
  readoutWeight := fun token coordinate =>
    match lookupHiddenSplit coordinate with
    | .inl tokenCoordinate => scalar (token = tokenCoordinate)
    | .inr _ => low
  outputLabel := label

/-- The valid one-hot context containing a single token. -/
def oneHot {vocabulary : ℕ} (token : Fin vocabulary) :
    Bits (architecture vocabulary).inputBits :=
  fun index =>
    let location := finProdFinEquiv.symm index
    decide (location.2 = token)

theorem oneHot_at {vocabulary : ℕ} (token candidate : Fin vocabulary) :
    oneHot token (lookupInputIndex
      (⟨0, by simp [architecture]⟩ : Fin (architecture vocabulary).contextLength)
      candidate) =
      decide (candidate = token) := by
  simp [oneHot, lookupInputIndex, FixedPrecisionTransformer.inputIndex]

@[simp] theorem tokenScalarValue_oneHot
    {vocabulary : ℕ} (label : Fin vocabulary → Bool)
    (token coordinate : Fin vocabulary) :
    (transformer vocabulary label).tokenScalarValue (oneHot token)
      ⟨0, by simp [architecture]⟩ coordinate =
      scalar (token = coordinate) := by
  funext bit
  fin_cases bit
  simp [FixedPrecisionTransformer.tokenScalarValue, transformer, scalar,
    oneHot, FixedPrecisionTransformer.inputIndex, high, low]

@[simp] theorem embeddingScalarValue_oneHot_token
    {vocabulary : ℕ} (label : Fin vocabulary → Bool)
    (token coordinate : Fin vocabulary) :
    (transformer vocabulary label).embeddingScalarValue (oneHot token)
      ⟨0, by simp [architecture]⟩
      (tokenCoordinate coordinate) = scalar (token = coordinate) := by
  rw [FixedPrecisionTransformer.embeddingScalarValue]
  rw [hiddenSplit_tokenCoordinate]
  exact tokenScalarValue_oneHot label token coordinate

@[simp] theorem embeddingScalarValue_oneHot_position
    {vocabulary : ℕ} (label : Fin vocabulary → Bool)
    (token coordinate : Fin vocabulary) :
    (transformer vocabulary label).embeddingScalarValue (oneHot token)
      ⟨0, by simp [architecture]⟩
      (positionCoordinate coordinate) = low := by
  rw [FixedPrecisionTransformer.embeddingScalarValue]
  rw [hiddenSplit_positionCoordinate]
  rfl

@[simp] theorem stateValue_embeddingValue
    {vocabulary : ℕ} (label : Fin vocabulary → Bool)
    (input : Bits (architecture vocabulary).inputBits)
    (position : Fin (architecture vocabulary).contextLength)
    (coordinate : Fin (architecture vocabulary).hiddenWidth) :
    (transformer vocabulary label).stateValue
        ((transformer vocabulary label).embeddingValue input)
        position coordinate =
      (transformer vocabulary label).embeddingScalarValue input position coordinate := by
  funext bit
  simp [FixedPrecisionTransformer.stateValue,
    FixedPrecisionTransformer.embeddingValue,
    FixedPrecisionTransformer.stateBlock]

theorem aggregateValues_eq_high_iff
    {vocabulary count : ℕ} (label : Fin vocabulary → Bool)
    (term : Fin count → Scalar) :
    (transformer vocabulary label).aggregateValues term = high ↔
      ∃ coordinate, term coordinate = high := by
  rw [FixedPrecisionTransformer.aggregateValues]
  change arithmetic.roundedSumWord
      (OrderedExpression.inputWord 1 count (ScalarCircuit.pack term)) = high ↔ _
  rw [roundedSumWord_eq_high_iff]
  simp [OrderedExpression.inputWord, ScalarCircuit.pack]

@[simp] theorem scalar_eq_high_iff (condition : Bool) :
    scalar condition = high ↔ condition = true := by
  cases condition <;> simp [scalar, low_ne_high]

@[simp] theorem readoutScalarValue_oneHot
    {vocabulary : ℕ} (label : Fin vocabulary → Bool)
    (token candidate : Fin vocabulary) :
    (transformer vocabulary label).readoutScalarValue
        ((transformer vocabulary label).embeddingValue (oneHot token))
        ⟨0, by simp [architecture]⟩ candidate =
      scalar (candidate = token) := by
  let T := transformer vocabulary label
  have hhigh :
      T.readoutScalarValue (T.embeddingValue (oneHot token))
          ⟨0, by simp [architecture]⟩ candidate = high ↔
        candidate = token := by
    rw [FixedPrecisionTransformer.readoutScalarValue]
    rw [aggregateValues_eq_high_iff]
    constructor
    · rintro ⟨coordinate, hcoordinate⟩
      change arithmetic.multiply (Fin.append
        ((transformer vocabulary label).readoutWeight candidate coordinate)
        ((transformer vocabulary label).stateValue
          ((transformer vocabulary label).embeddingValue (oneHot token))
          ⟨0, by simp [architecture]⟩ coordinate)) = high at hcoordinate
      rw [multiply_eq_high_iff] at hcoordinate
      rcases hcoordinate with ⟨hweight, hstate⟩
      rw [stateValue_embeddingValue] at hstate
      cases hsplit : FixedPrecisionTransformer.hiddenSplit coordinate with
      | inl embeddedToken =>
          simp only [transformer, lookupHiddenSplit, hsplit] at hweight
          simp only [FixedPrecisionTransformer.embeddingScalarValue, hsplit] at hstate
          change scalar (candidate = embeddedToken) = high at hweight
          change (transformer vocabulary label).tokenScalarValue
            (oneHot token) ⟨0, by simp [architecture]⟩ embeddedToken = high at hstate
          rw [tokenScalarValue_oneHot] at hstate
          have hw : candidate = embeddedToken := by
            simpa only [scalar_eq_high_iff, decide_eq_true_eq] using hweight
          have hs : token = embeddedToken := by
            by_contra hne
            have hlow : scalar (decide (token = embeddedToken)) = low := by
              simp [scalar, hne]
            exact low_ne_high (hlow.symm.trans hstate)
          exact hw.trans hs.symm
      | inr embeddedPosition =>
          simp only [transformer, lookupHiddenSplit, hsplit] at hweight
          change low = high at hweight
          exact (low_ne_high hweight).elim
    · intro hcandidate
      subst candidate
      refine ⟨tokenCoordinate token, ?_⟩
      change arithmetic.multiply (Fin.append
        ((transformer vocabulary label).readoutWeight token (tokenCoordinate token))
        ((transformer vocabulary label).stateValue
          ((transformer vocabulary label).embeddingValue (oneHot token))
          ⟨0, by simp [architecture]⟩ (tokenCoordinate token))) = high
      rw [multiply_eq_high_iff]
      constructor
      · simp [transformer, scalar]
      · rw [stateValue_embeddingValue]
        rw [embeddingScalarValue_oneHot_token]
        simp [scalar]
  rcases scalar_eq_low_or_high
      (T.readoutScalarValue (T.embeddingValue (oneHot token))
        ⟨0, by simp [architecture]⟩ candidate) with hlow | hvalue
  · rw [hlow]
    by_cases h : candidate = token
    · exact (low_ne_high (hlow.symm.trans (hhigh.mpr h))).elim
    · simp [scalar, h]
  · rw [hvalue]
    simp [scalar, hhigh.mp hvalue]

@[simp] theorem lessEqual_scalar (first second : Bool) :
    arithmetic.lessEqual (Fin.append (scalar first) (scalar second)) =
      (!first || second) := by
  cases first <;> cases second <;>
    simp [arithmetic, scalar, rank_low, rank_high]

theorem readoutWinnerValue_oneHot_iff
    {vocabulary : ℕ} (label : Fin vocabulary → Bool)
    (token candidate : Fin vocabulary) :
    (transformer vocabulary label).readoutWinnerValue
        ((transformer vocabulary label).embeddingValue (oneHot token))
        ⟨0, by simp [architecture]⟩ candidate = true ↔
      candidate = token := by
  rw [FixedPrecisionTransformer.readoutWinnerValue]
  simp only [decide_eq_true_eq]
  constructor
  · intro hwinner
    by_contra hcandidate
    have hcomparison := hwinner token
    simp only [FixedPrecisionTransformer.readoutComparisonValue,
      hcandidate, if_false] at hcomparison
    rw [readoutScalarValue_oneHot, readoutScalarValue_oneHot] at hcomparison
    by_cases horder : token < candidate <;>
      simp [horder, transformer, arithmetic, scalar, hcandidate] at hcomparison
  · intro hcandidate
    subst candidate
    intro challenger
    by_cases hchallenger : token = challenger
    · subst challenger
      simp [FixedPrecisionTransformer.readoutComparisonValue]
    · simp only [FixedPrecisionTransformer.readoutComparisonValue,
        hchallenger, if_false]
      rw [readoutScalarValue_oneHot, readoutScalarValue_oneHot]
      have hreverse : challenger ≠ token := Ne.symm hchallenger
      simp [hchallenger, hreverse, transformer, arithmetic, scalar]

/-- The input token is the unique greedy winner. -/
theorem run_oneHot
    {vocabulary : ℕ} (label : Fin vocabulary → Bool) (token : Fin vocabulary) :
    (transformer vocabulary label).run (oneHot token) = label token := by
  -- All components are finite and reduce to one-hot matching.  The matrix
  -- semantics is used directly; no circuit or realization theorem is assumed.
  classical
  simp only [FixedPrecisionTransformer.run, transformer, architecture,
    List.ofFn_zero, List.foldl_nil]
  unfold FixedPrecisionTransformer.readoutValue
  simp only [dif_pos (by omega : 0 < 1)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨candidate, hlabel, hwinner⟩
    have hcandidate : candidate = token :=
      (readoutWinnerValue_oneHot_iff label token candidate).mp hwinner
    simpa [hcandidate] using hlabel
  · intro hlabel
    exact ⟨token, hlabel,
      (readoutWinnerValue_oneHot_iff label token token).mpr rfl⟩

/-! ## Realizing arbitrary finite local maps -/

/-- Every Boolean-valued map on a finite type is realized by an actual
matrix-level fixed-precision Transformer.  The input is the canonical one-hot
encoding of the finite value. -/
def ofFiniteFunction (Input : Type*) [Fintype Input] (label : Input → Bool) :
    FixedPrecisionTransformer (architecture (Fintype.card Input)) :=
  transformer (Fintype.card Input) (fun index => label ((Fintype.equivFin Input).symm index))

theorem run_ofFiniteFunction
    (Input : Type*) [Fintype Input] (label : Input → Bool) (input : Input) :
    (ofFiniteFunction Input label).run
        (oneHot (Fintype.equivFin Input input)) = label input := by
  rw [ofFiniteFunction, run_oneHot]
  simp

/-- Bitwise form used by finite local transition maps: every output bit has a
concrete fixed-precision Transformer realization, with no realization
hypothesis attached to the abstract map. -/
theorem finiteMap_bits_realized
    (Input Output : Type*) [Fintype Input]
    (encode : Output → Bits width) (function : Input → Output) :
    ∀ bit : Fin width,
      ∃ model : FixedPrecisionTransformer (architecture (Fintype.card Input)),
        ∀ input : Input,
          model.run (oneHot (Fintype.equivFin Input input)) =
            encode (function input) bit := by
  intro bit
  refine ⟨ofFiniteFunction Input (fun input => encode (function input) bit), ?_⟩
  exact run_ofFiniteFunction Input _

end LookupTransformer

