import CanonicalArithmetic

/-!
# Exact numerical primitives for matrix simulation

These are operations of the actual signed fixed-point arithmetic, not
arbitrary Boolean lookup operations. Integer values round exactly within the
grid; bounded integer sums are exact; and rounded real exponentiation turns
scores `0` and `-1` into `1` and `0`, respectively. This supplies exact
one-hot softmax routing at fixed precision independent of context length.
-/

noncomputable section

namespace NumericalPrimitives

open TransformerAC0 CanonicalArithmetic

def Supports (bits offset : ℕ) (integer : ℤ) : Prop :=
  -(offset : ℤ) ≤ integer ∧ integer + offset < (2 ^ bits : ℕ)

def integerIndex (bits offset : ℕ) (integer : ℤ) (supported : Supports bits offset integer) :
    Fin (Fintype.card (Bits bits)) :=
  ⟨(integer + offset).toNat, by
    have hcard : Fintype.card (Bits bits) = 2 ^ bits := by simp [Bits]
    rw [hcard]
    have hlower := supported.1
    have hupper := supported.2
    omega⟩

theorem rankValue_integerIndex (bits offset : ℕ) (integer : ℤ) (supported : Supports bits offset integer) :
    rankValue 0 offset (integerIndex bits offset integer supported) = (integer : ℝ) := by
  have hnonnegative : 0 ≤ integer + offset := by have h := supported.1; omega
  have hindex : ((integer + offset).toNat : ℤ) = integer + offset := Int.toNat_of_nonneg hnonnegative
  have hreal : ((integer + offset).toNat : ℝ) = (integer : ℝ) + offset := by exact_mod_cast hindex
  simp only [rankValue, integerIndex, scale, pow_zero, div_one]
  rw [hreal]
  ring

theorem value_encode_integer (bits offset : ℕ) (integer : ℤ) (supported : Supports bits offset integer) :
    value bits 0 offset (encode bits 0 offset (integer : ℝ)) = (integer : ℝ) := by
  rw [← rankValue_integerIndex bits offset integer supported]
  simp only [value, encode, Equiv.apply_symm_apply, roundIndex_rankValue]

theorem add_integers (bits offset : ℕ) (first second : ℤ)
    (hfirst : Supports bits offset first) (hsecond : Supports bits offset second) :
    (arithmetic bits 0 offset).roundedAdd
      (Fin.append (encode bits 0 offset (first : ℝ)) (encode bits 0 offset (second : ℝ))) =
        encode bits 0 offset ((first + second : ℤ) : ℝ) := by
  simp only [arithmetic, first_append, second_append, value_encode_integer _ _ _ hfirst,
    value_encode_integer _ _ _ hsecond, Int.cast_add]

theorem multiply_integers (bits offset : ℕ) (first second : ℤ)
    (hfirst : Supports bits offset first) (hsecond : Supports bits offset second) :
    (arithmetic bits 0 offset).multiply
      (Fin.append (encode bits 0 offset (first : ℝ)) (encode bits 0 offset (second : ℝ))) =
        encode bits 0 offset ((first * second : ℤ) : ℝ) := by
  simp only [arithmetic, first_append, second_append, value_encode_integer _ _ _ hfirst,
    value_encode_integer _ _ _ hsecond, Int.cast_mul]

theorem divide_by_one (bits offset : ℕ) (integer : ℤ)
    (hinteger : Supports bits offset integer) (hone : Supports bits offset 1) :
    (arithmetic bits 0 offset).divide
      (Fin.append (encode bits 0 offset (integer : ℝ)) (encode bits 0 offset 1)) =
        encode bits 0 offset (integer : ℝ) := by
  have honeValue : value bits 0 offset (encode bits 0 offset 1) = 1 := by
    simpa using value_encode_integer bits offset 1 hone
  simp only [arithmetic, first_append, second_append, value_encode_integer _ _ _ hinteger,
    honeValue, div_one]

theorem relu_integer (bits offset : ℕ) (integer : ℤ) (supported : Supports bits offset integer) :
    (arithmetic bits 0 offset).relu (encode bits 0 offset (integer : ℝ)) =
      encode bits 0 offset ((max 0 integer : ℤ) : ℝ) := by
  simp only [arithmetic, value_encode_integer _ _ _ supported, Int.cast_max, Int.cast_zero]

/-- No overflow or saturation is assumed away: every intermediate prefix
sum is explicitly shown representable before the numerical fold is used. -/
theorem fold_integer_exact (bits offset : ℕ) (word : List ℤ) (accumulator : ℤ)
    (terms : ∀ integer ∈ word, Supports bits offset integer)
    (prefixes : ∀ front suffix : List ℤ, word = front ++ suffix →
      Supports bits offset (accumulator + front.sum)) :
    (word.map fun (integer : ℤ) => encode bits 0 offset (integer : ℝ)).foldl
      (fun before term => (arithmetic bits 0 offset).roundedAdd (Fin.append before term))
      (encode bits 0 offset (accumulator : ℝ)) =
        encode bits 0 offset ((accumulator + word.sum : ℤ) : ℝ) := by
  induction word generalizing accumulator with
  | nil => simp
  | cons head tail ih =>
      have haccumulator : Supports bits offset accumulator := by
        simpa using prefixes [] (head :: tail) rfl
      have hhead : Supports bits offset head := terms head (by simp)
      simp only [List.map_cons, List.foldl_cons]
      rw [add_integers bits offset accumulator head haccumulator hhead]
      have htailTerms : ∀ integer ∈ tail, Supports bits offset integer := fun integer h => terms integer (by simp [h])
      have htailPrefixes : ∀ front suffix : List ℤ, tail = front ++ suffix →
          Supports bits offset (accumulator + head + front.sum) := by
        intro front suffix heq
        have h := prefixes (head :: front) suffix (by simp [heq])
        simpa [List.sum_cons, add_assoc] using h
      rw [ih (accumulator + head) htailTerms htailPrefixes]
      simp [List.sum_cons, add_assoc]

theorem roundedSumWord_integer_exact (bits offset : ℕ) (word : List ℤ)
    (terms : ∀ integer ∈ word, Supports bits offset integer)
    (prefixes : ∀ front suffix : List ℤ, word = front ++ suffix → Supports bits offset front.sum) :
    (arithmetic bits 0 offset).roundedSumWord
      (word.map fun (integer : ℤ) => encode bits 0 offset (integer : ℝ)) =
        encode bits 0 offset (word.sum : ℝ) := by
  simpa only [FixedPrecisionArithmetic.roundedSumWord, arithmetic, Int.cast_zero, zero_add]
    using fold_integer_exact bits offset word 0 terms (by simpa only [zero_add] using prefixes)

theorem round_small_eq_zero (bits offset : ℕ) (x : ℝ) (hnonnegative : 0 ≤ x) (hsmall : x < 1 / 2) :
    encode bits 0 offset x = encode bits 0 offset 0 := by
  have hfloor : Nat.floor (x + offset + 1 / 2) = offset := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> linarith
  have hzero : Nat.floor ((0 : ℝ) + offset + 1 / 2) = offset := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> linarith
  unfold encode
  congr 1
  apply Fin.ext
  simp only [roundIndex, scale, pow_zero, mul_one, hfloor, hzero]

theorem exp_negative_one_lt_half : Real.exp (-1) < 1 / 2 := by
  have htwo : 2 < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) htwo

/-- Real exponentiation and nearest-point rounding, not an assigned lookup
table, give the exact score mask used by positional routing. -/
theorem exponentiate_negative_one (bits offset : ℕ) (supported : Supports bits offset (-1)) :
    (arithmetic bits 0 offset).exponentiate (encode bits 0 offset (-1)) = encode bits 0 offset 0 := by
  have hvalue : value bits 0 offset (encode bits 0 offset (-1)) = -1 := by
    simpa using value_encode_integer bits offset (-1) supported
  simp only [arithmetic, hvalue]
  exact round_small_eq_zero bits offset _ (Real.exp_pos _).le exp_negative_one_lt_half

theorem exponentiate_zero (bits offset : ℕ) (supported : Supports bits offset 0) :
    (arithmetic bits 0 offset).exponentiate (encode bits 0 offset 0) = encode bits 0 offset 1 := by
  have hvalue : value bits 0 offset (encode bits 0 offset 0) = 0 := by
    simpa using value_encode_integer bits offset 0 supported
  simp only [arithmetic, hvalue, Real.exp_zero]

theorem supports_nonnegative_interval (bits offset : ℕ) (bound integer : ℤ)
    (hbound : Supports bits offset bound) (hlower : 0 ≤ integer) (hupper : integer ≤ bound) :
    Supports bits offset integer := by
  have h := hbound.2
  unfold Supports
  constructor <;> omega

theorem roundedSumWord_nonnegative_exact (bits offset : ℕ) (word : List ℤ) (bound : ℤ)
    (hbound : Supports bits offset bound)
    (nonnegative : ∀ integer ∈ word, 0 ≤ integer) (sumBound : word.sum ≤ bound) :
    (arithmetic bits 0 offset).roundedSumWord
      (word.map fun (integer : ℤ) => encode bits 0 offset (integer : ℝ)) =
        encode bits 0 offset (word.sum : ℝ) := by
  apply roundedSumWord_integer_exact
  · intro integer hmem
    exact supports_nonnegative_interval bits offset bound integer hbound (nonnegative integer hmem)
      ((List.single_le_sum nonnegative integer hmem).trans sumBound)
  · intro front suffix heq
    have hfront : 0 ≤ front.sum := List.sum_nonneg (fun integer h =>
      nonnegative integer (by rw [heq]; exact List.mem_append_left _ h))
    have hsuffix : 0 ≤ suffix.sum := List.sum_nonneg (fun integer h =>
      nonnegative integer (by rw [heq]; exact List.mem_append_right _ h))
    have htotal : word.sum = front.sum + suffix.sum := by rw [heq, List.sum_append]
    apply supports_nonnegative_interval bits offset bound front.sum hbound hfront
    omega

def aggregate (bits offset : ℕ) (terms : Fin count → Bits bits) : Bits bits :=
  (arithmetic bits 0 offset).roundedSumWord (List.ofFn terms)

theorem aggregate_nonnegative_exact (bits offset : ℕ) (terms : Fin count → ℤ) (bound : ℤ)
    (hbound : Supports bits offset bound) (nonnegative : ∀ i, 0 ≤ terms i)
    (sumBound : ∑ i, terms i ≤ bound) :
    aggregate bits offset (fun i => encode bits 0 offset (terms i : ℝ)) =
      encode bits 0 offset ((∑ i, terms i : ℤ) : ℝ) := by
  have h := roundedSumWord_nonnegative_exact bits offset (List.ofFn terms) bound hbound
    (by intro integer hmem; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem; exact nonnegative i)
    (by simpa only [List.sum_ofFn] using sumBound)
  simpa only [aggregate, List.map_ofFn, Function.comp_apply, List.sum_ofFn] using h

private theorem nonpositive_sum (word : List ℤ) (terms : ∀ integer ∈ word, integer ≤ 0) : word.sum ≤ 0 := by
  induction word with
  | nil => simp
  | cons head tail ih =>
      have hh := terms head (by simp)
      have ht := ih (fun integer h => terms integer (by simp [h]))
      simp only [List.sum_cons]
      omega

private theorem nonpositive_sum_le_member (word : List ℤ) (terms : ∀ integer ∈ word, integer ≤ 0)
    (integer : ℤ) (hmem : integer ∈ word) : word.sum ≤ integer := by
  induction word with
  | nil => simp at hmem
  | cons head tail ih =>
      have hh := terms head (by simp)
      have htail : ∀ integer ∈ tail, integer ≤ 0 := fun integer h => terms integer (by simp [h])
      rcases List.mem_cons.mp hmem with rfl | hmem
      · have h := nonpositive_sum tail htail
        simp only [List.sum_cons]
        omega
      · have h := ih htail hmem
        simp only [List.sum_cons]
        omega

theorem supports_nonpositive_interval (bits offset : ℕ) (bound integer : ℤ)
    (hbound : Supports bits offset bound) (hzero : Supports bits offset 0)
    (hlower : bound ≤ integer) (hupper : integer ≤ 0) : Supports bits offset integer := by
  have hb := hbound.1
  have hz := hzero.2
  unfold Supports
  constructor <;> omega

theorem roundedSumWord_nonpositive_exact (bits offset : ℕ) (word : List ℤ) (bound : ℤ)
    (hbound : Supports bits offset bound) (hzero : Supports bits offset 0)
    (nonpositive : ∀ integer ∈ word, integer ≤ 0) (sumBound : bound ≤ word.sum) :
    (arithmetic bits 0 offset).roundedSumWord
      (word.map fun (integer : ℤ) => encode bits 0 offset (integer : ℝ)) =
        encode bits 0 offset (word.sum : ℝ) := by
  apply roundedSumWord_integer_exact
  · intro integer hmem
    exact supports_nonpositive_interval bits offset bound integer hbound hzero
      (sumBound.trans (nonpositive_sum_le_member word nonpositive integer hmem)) (nonpositive integer hmem)
  · intro front suffix heq
    have hfront : front.sum ≤ 0 := nonpositive_sum front (fun integer h =>
      nonpositive integer (by rw [heq]; exact List.mem_append_left _ h))
    have hsuffix : suffix.sum ≤ 0 := nonpositive_sum suffix (fun integer h =>
      nonpositive integer (by rw [heq]; exact List.mem_append_right _ h))
    have htotal : word.sum = front.sum + suffix.sum := by rw [heq, List.sum_append]
    apply supports_nonpositive_interval bits offset bound front.sum hbound hzero
    · omega
    · exact hfront

theorem aggregate_nonpositive_exact (bits offset : ℕ) (terms : Fin count → ℤ) (bound : ℤ)
    (hbound : Supports bits offset bound) (hzero : Supports bits offset 0) (nonpositive : ∀ i, terms i ≤ 0)
    (sumBound : bound ≤ ∑ i, terms i) :
    aggregate bits offset (fun i => encode bits 0 offset (terms i : ℝ)) =
      encode bits 0 offset ((∑ i, terms i : ℤ) : ℝ) := by
  have h := roundedSumWord_nonpositive_exact bits offset (List.ofFn terms) bound hbound hzero
    (by intro integer hmem; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem; exact nonpositive i)
    (by simpa only [List.sum_ofFn] using sumBound)
  simpa only [aggregate, List.map_ofFn, Function.comp_apply, List.sum_ofFn] using h

/-- This aggregate is exactly the scalar aggregate used by the independent
matrix semantics in `TransformerAC0`. -/
theorem aggregate_eq_matrix_aggregate (bits offset : ℕ) (terms : Fin count → Bits bits) :
    aggregate bits offset terms = (arithmetic bits 0 offset).roundedSum count (ScalarCircuit.pack terms) := by
  unfold aggregate FixedPrecisionArithmetic.roundedSum OrderedExpression.inputWord
  apply congrArg (arithmetic bits 0 offset).roundedSumWord
  apply congrArg List.ofFn
  funext position bit
  simp [ScalarCircuit.pack]

private theorem abs_list_sum_le (word : List ℤ) : |word.sum| ≤ (word.map (fun integer => |integer|)).sum := by
  induction word with
  | nil => simp
  | cons head tail ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add head tail.sum).trans (add_le_add_left ih _)

theorem supports_symmetric_interval (bits offset radius : ℕ) (integer : ℤ)
    (hnegative : Supports bits offset (-(radius : ℤ))) (hpositive : Supports bits offset (radius : ℤ))
    (habs : |integer| ≤ (radius : ℤ)) : Supports bits offset integer := by
  have hlower := (abs_le.mp habs).1
  have hupper := (abs_le.mp habs).2
  have hn := hnegative.1
  have hp := hpositive.2
  unfold Supports
  constructor <;> omega

/-- A signed sum is exact whenever the absolute sum of its terms fits the
signed lattice. This checks all intermediate accumulation prefixes too. -/
theorem roundedSumWord_signed_exact (bits offset radius : ℕ) (word : List ℤ)
    (hnegative : Supports bits offset (-(radius : ℤ))) (hpositive : Supports bits offset (radius : ℤ))
    (habs : (word.map (fun integer => |integer|)).sum ≤ (radius : ℤ)) :
    (arithmetic bits 0 offset).roundedSumWord
      (word.map fun (integer : ℤ) => encode bits 0 offset (integer : ℝ)) =
        encode bits 0 offset (word.sum : ℝ) := by
  apply roundedSumWord_integer_exact
  · intro integer hmem
    apply supports_symmetric_interval bits offset radius integer hnegative hpositive
    have hmem' : |integer| ∈ word.map (fun integer => |integer|) := List.mem_map.mpr ⟨integer, hmem, rfl⟩
    have hterms : ∀ a ∈ word.map (fun integer => |integer|), (0 : ℤ) ≤ a := by
      intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact abs_nonneg b
    exact (List.single_le_sum hterms _ hmem').trans habs
  · intro front suffix heq
    apply supports_symmetric_interval bits offset radius front.sum hnegative hpositive
    have hsuffix : 0 ≤ (suffix.map (fun integer => |integer|)).sum := by
      apply List.sum_nonneg
      intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact abs_nonneg b
    have hsum : (word.map (fun integer => |integer|)).sum =
        (front.map (fun integer => |integer|)).sum + (suffix.map (fun integer => |integer|)).sum := by
      rw [heq, List.map_append, List.sum_append]
    have hfront := abs_list_sum_le front
    omega

theorem aggregate_signed_exact (bits offset radius : ℕ) (terms : Fin count → ℤ)
    (hnegative : Supports bits offset (-(radius : ℤ))) (hpositive : Supports bits offset (radius : ℤ))
    (habs : ∑ i, |terms i| ≤ (radius : ℤ)) :
    aggregate bits offset (fun i => encode bits 0 offset (terms i : ℝ)) =
      encode bits 0 offset ((∑ i, terms i : ℤ) : ℝ) := by
  have h := roundedSumWord_signed_exact bits offset radius (List.ofFn terms) hnegative hpositive
    (by simpa only [List.map_ofFn, Function.comp_apply, List.sum_ofFn] using habs)
  simpa only [aggregate, List.map_ofFn, Function.comp_apply, List.sum_ofFn] using h

end NumericalPrimitives
