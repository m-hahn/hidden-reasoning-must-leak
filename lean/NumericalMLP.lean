import NumericalPrimitives

/-!
# Numerical finite local-map MLP

Each hidden row detects one Boolean feature pattern using signed weights
and a constant-coordinate bias. Rounded numerical inner products and ReLU
produce its exact indicator. A second numerical matrix maps that indicator
to the requested output token. Precision depends only on the finite feature
width, not on the tape capacity or the number of autoregressive steps.
-/

noncomputable section
open scoped BigOperators

namespace NumericalMLP

open TransformerAC0 CanonicalArithmetic NumericalPrimitives

def bitInteger (value : Bool) : ℤ := if value then 1 else 0
def slope (value : Bool) : ℤ := if value then 1 else -1

def bias (pattern : Bits features) : ℤ := 1 - ∑ i, bitInteger (pattern i)

def mismatchCount (pattern input : Bits features) : ℤ :=
  ∑ i, if input i = pattern i then 0 else 1

def integerTerms (pattern input : Bits features) : Fin (features + 1) → ℤ :=
  Fin.cases (bias pattern) (fun i => slope (pattern i) * bitInteger (input i))

def inputWeight (bits offset : ℕ) (pattern : Bits features) : Fin (features + 1) → Bits bits :=
  Fin.cases (encode bits 0 offset (bias pattern : ℝ))
    (fun i => encode bits 0 offset (slope (pattern i) : ℝ))

def inputValue (bits offset : ℕ) (input : Bits features) : Fin (features + 1) → Bits bits :=
  Fin.cases (encode bits 0 offset 1) (fun i => encode bits 0 offset (bitInteger (input i) : ℝ))

def inner (bits offset : ℕ) (pattern input : Bits features) : Bits bits :=
  aggregate bits offset (fun i => (arithmetic bits 0 offset).multiply
    (Fin.append (inputWeight bits offset pattern i) (inputValue bits offset input i)))

def hidden (bits offset : ℕ) (pattern input : Bits features) : Bits bits :=
  (arithmetic bits 0 offset).relu (inner bits offset pattern input)

theorem bitInteger_bounds (value : Bool) : 0 ≤ bitInteger value ∧ bitInteger value ≤ 1 := by
  cases value <;> norm_num [bitInteger]

theorem abs_slope_bit (pattern input : Bool) : |slope pattern * bitInteger input| ≤ 1 := by
  cases pattern <;> cases input <;> norm_num [slope, bitInteger]

theorem trueCount_bounds (pattern : Bits features) :
    0 ≤ (∑ i, bitInteger (pattern i)) ∧ (∑ i, bitInteger (pattern i)) ≤ (features : ℤ) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (bitInteger_bounds _).1)
  · calc
      _ ≤ ∑ _i : Fin features, (1 : ℤ) := Finset.sum_le_sum (fun i _ => (bitInteger_bounds _).2)
      _ = _ := by simp

theorem abs_bias_le (pattern : Bits features) : |bias pattern| ≤ (features : ℤ) + 1 := by
  have h := trueCount_bounds pattern
  rw [abs_le]
  unfold bias
  constructor <;> omega

theorem absolute_terms_bound (pattern input : Bits features) :
    ∑ i, |integerTerms pattern input i| ≤ (2 * features + 1 : ℕ) := by
  rw [Fin.sum_univ_succ]
  simp only [integerTerms, Fin.cases_zero, Fin.cases_succ]
  have hsum : (∑ i : Fin features, |slope (pattern i) * bitInteger (input i)|) ≤ (features : ℤ) := by
    calc
      _ ≤ ∑ _i : Fin features, (1 : ℤ) := Finset.sum_le_sum (fun i _ => abs_slope_bit _ _)
      _ = _ := by simp
  have hb := abs_bias_le pattern
  push_cast
  omega

theorem integerTerms_sum (pattern input : Bits features) :
    ∑ i, integerTerms pattern input i = 1 - mismatchCount pattern input := by
  have hcoordinate : ∀ i, slope (pattern i) * bitInteger (input i) - bitInteger (pattern i) =
      -(if input i = pattern i then 0 else 1 : ℤ) := by
    intro i
    cases hp : pattern i <;> cases hi : input i <;> norm_num [slope, bitInteger, hp, hi]
  have hsum : (∑ i, (slope (pattern i) * bitInteger (input i) - bitInteger (pattern i))) =
      ∑ i, -(if input i = pattern i then 0 else 1 : ℤ) :=
    Finset.sum_congr rfl (fun i _ => hcoordinate i)
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
  rw [Fin.sum_univ_succ]
  simp only [integerTerms, Fin.cases_zero, Fin.cases_succ, bias, mismatchCount]
  linarith

theorem neuron_margin (pattern input : Bits features) :
    max 0 (1 - mismatchCount pattern input) = if input = pattern then (1 : ℤ) else 0 := by
  by_cases heq : input = pattern
  · subst input
    simp [mismatchCount]
  · have hcoordinate : ∃ i, input i ≠ pattern i := by
      by_contra hnone
      apply heq
      funext i
      simpa using not_exists.mp hnone i
    obtain ⟨i, hi⟩ := hcoordinate
    have hsum : (1 : ℤ) ≤ mismatchCount pattern input := by
      have h := Finset.single_le_sum
        (s := Finset.univ) (f := fun j : Fin features => if input j = pattern j then (0 : ℤ) else 1)
        (fun j _ => by dsimp only; split_ifs <;> omega) (Finset.mem_univ i)
      simpa [mismatchCount, hi] using h
    simp [heq, max_eq_left (by omega : 1 - mismatchCount pattern input ≤ 0)]

theorem inner_exact (bits offset : ℕ) (pattern input : Bits features)
    (hnegative : Supports bits offset (-(2 * features + 1 : ℕ)))
    (hpositive : Supports bits offset (2 * features + 1 : ℕ)) :
    inner bits offset pattern input = encode bits 0 offset ((1 - mismatchCount pattern input : ℤ) : ℝ) := by
  have hradius : (1 : ℤ) ≤ (2 * features + 1 : ℕ) := by omega
  have hsupports (integer : ℤ) (habs : |integer| ≤ (2 * features + 1 : ℕ)) : Supports bits offset integer :=
    supports_symmetric_interval bits offset (2 * features + 1) integer hnegative hpositive habs
  have hterms : (fun i => (arithmetic bits 0 offset).multiply
      (Fin.append (inputWeight bits offset pattern i) (inputValue bits offset input i))) =
      (fun i => encode bits 0 offset (integerTerms pattern input i : ℝ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := multiply_integers bits offset (bias pattern) 1
        (hsupports _ (by have hb := abs_bias_le pattern; omega))
        (hsupports _ (by simpa using hradius))
      simpa only [inputWeight, inputValue, integerTerms, Fin.cases_zero, Int.cast_one, mul_one] using h
    · have hw := hsupports (slope (pattern j)) (by cases pattern j <;> norm_num [slope] <;> omega)
      have hx := hsupports (bitInteger (input j)) (by cases input j <;> norm_num [bitInteger] <;> omega)
      have h := multiply_integers bits offset (slope (pattern j)) (bitInteger (input j)) hw hx
      simpa only [inputWeight, inputValue, integerTerms, Fin.cases_succ] using h
  unfold inner
  rw [hterms, aggregate_signed_exact bits offset (2 * features + 1) _ hnegative hpositive
    (absolute_terms_bound pattern input), integerTerms_sum]

/-- Every finite Boolean pattern has an exact numerical ReLU indicator. -/
theorem hidden_exact (bits offset : ℕ) (pattern input : Bits features)
    (hnegative : Supports bits offset (-(2 * features + 1 : ℕ)))
    (hpositive : Supports bits offset (2 * features + 1 : ℕ)) :
    hidden bits offset pattern input = encode bits 0 offset (if input = pattern then 1 else 0) := by
  have hsum : Supports bits offset (1 - mismatchCount pattern input) := by
    rw [← integerTerms_sum]
    have h := absolute_terms_bound pattern input
    have habs : |∑ i, integerTerms pattern input i| ≤ ∑ i, |integerTerms pattern input i| :=
      Finset.abs_sum_le_sum_abs _ _
    exact supports_symmetric_interval bits offset (2 * features + 1) _ hnegative hpositive (habs.trans h)
  unfold hidden
  rw [inner_exact bits offset pattern input hnegative hpositive, relu_integer bits offset _ hsum, neuron_margin]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero]

def patternAt (features : ℕ) (index : Fin (Fintype.card (Bits features))) : Bits features :=
  (Fintype.equivFin (Bits features)).symm index

def outputWeight (bits offset : ℕ) (function : Bits features → Fin vocabulary)
    (token : Fin vocabulary) (index : Fin (Fintype.card (Bits features))) : Bits bits :=
  encode bits 0 offset (if function (patternAt features index) = token then 1 else 0)

def output (bits offset : ℕ) (function : Bits features → Fin vocabulary) (input : Bits features)
    (token : Fin vocabulary) : Bits bits :=
  aggregate bits offset (fun index => (arithmetic bits 0 offset).multiply
    (Fin.append (outputWeight bits offset function token index)
      (hidden bits offset (patternAt features index) input)))

/-- The second numerical matrix computes the complete one-hot output token
of any finite local map. It does not receive the function value as an input. -/
theorem output_exact (bits offset : ℕ) (function : Bits features → Fin vocabulary) (input : Bits features)
    (token : Fin vocabulary) (hnegative : Supports bits offset (-(2 * features + 1 : ℕ)))
    (hpositive : Supports bits offset (2 * features + 1 : ℕ)) :
    output bits offset function input token = encode bits 0 offset (if function input = token then 1 else 0) := by
  have hone : Supports bits offset 1 := supports_symmetric_interval bits offset (2 * features + 1) 1
    hnegative hpositive (by rw [abs_one]; exact_mod_cast (show 1 ≤ 2 * features + 1 by omega))
  have hzero : Supports bits offset 0 := supports_symmetric_interval bits offset (2 * features + 1) 0
    hnegative hpositive (by rw [abs_zero]; exact_mod_cast Nat.zero_le (2 * features + 1))
  let inputIndex := Fintype.equivFin (Bits features) input
  have hindex : ∀ index, input = patternAt features index ↔ index = inputIndex := by
    intro index
    simp only [patternAt, inputIndex, Equiv.eq_symm_apply]
    exact eq_comm
  have hterms : (fun index => (arithmetic bits 0 offset).multiply
      (Fin.append (outputWeight bits offset function token index)
        (hidden bits offset (patternAt features index) input))) =
      (fun index : Fin (Fintype.card (Bits features)) => encode bits 0 offset
        ((if index = inputIndex then (if function input = token then 1 else 0) else 0 : ℤ) : ℝ)) := by
    funext index
    rw [hidden_exact bits offset _ input hnegative hpositive]
    have hw : Supports bits offset (if function (patternAt features index) = token then 1 else 0) := by
      split_ifs <;> assumption
    have hh : Supports bits offset (if input = patternAt features index then 1 else 0) := by
      split_ifs <;> assumption
    have hm := multiply_integers bits offset
      (if function (patternAt features index) = token then 1 else 0)
      (if input = patternAt features index then 1 else 0) hw hh
    by_cases heq : index = inputIndex
    · subst index
      have hp : patternAt features inputIndex = input := by simp [patternAt, inputIndex]
      simpa [outputWeight, hp] using hm
    · have hp : input ≠ patternAt features index := fun hx => heq ((hindex index).mp hx)
      simpa [outputWeight, hp, heq] using hm
  have hsum : (∑ index : Fin (Fintype.card (Bits features)),
      if index = inputIndex then (if function input = token then 1 else 0) else 0 : ℤ) =
      if function input = token then 1 else 0 := by simp
  unfold output
  rw [hterms]
  have h := aggregate_nonnegative_exact bits offset
    (fun index : Fin (Fintype.card (Bits features)) =>
      if index = inputIndex then (if function input = token then (1 : ℤ) else 0) else 0)
    1 hone (by intro index; dsimp only; split_ifs <;> omega) (by rw [hsum]; split_ifs <;> omega)
  simpa only [hsum, Int.cast_ite, Int.cast_one, Int.cast_zero] using h

def radius (features : ℕ) : ℕ := 2 * features + 1
def precision (features : ℕ) : ℕ := 2 * radius features + 1

theorem grid_supports_negative (features : ℕ) :
    Supports (precision features) (radius features) (-(radius features : ℤ)) := by
  have hpower : 0 < 2 ^ precision features := Nat.pow_pos (by decide)
  unfold Supports
  constructor
  · exact le_rfl
  · simpa only [neg_add_cancel] using (show (0 : ℤ) < (2 ^ precision features : ℕ) by exact_mod_cast hpower)

theorem grid_supports_positive (features : ℕ) :
    Supports (precision features) (radius features) (radius features : ℤ) := by
  have hpower : precision features < 2 ^ precision features := Nat.lt_two_pow_self
  have hbound : 2 * radius features < 2 ^ precision features :=
    (Nat.lt_succ_self (2 * radius features)).trans hpower
  unfold Supports
  constructor
  · omega
  · rw [two_mul] at hbound
    exact_mod_cast hbound

/-- A concrete globally fixed signed grid realizes each fixed finite local
map for arbitrarily large execution/context lengths. -/
theorem fixed_grid_output (function : Bits features → Fin vocabulary) (input : Bits features)
    (token : Fin vocabulary) :
    output (precision features) (radius features) function input token =
      encode (precision features) 0 (radius features) (if function input = token then 1 else 0) := by
  exact output_exact _ _ function input token (grid_supports_negative features) (grid_supports_positive features)

theorem hidden_width (features : ℕ) : Fintype.card (Bits features) = 2 ^ features := by simp [Bits]

end NumericalMLP
