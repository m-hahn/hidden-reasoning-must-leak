import NumericalPrimitives

/-!
# Exact positional softmax attention at numerical fixed precision

The score of the selected position is zero and all others have score minus
one. Real exponentiation, rounding, the complete rounded denominator sum,
division, and the complete rounded weighted-value sum are all executed.
The head retrieves every Boolean value coordinate exactly, for arbitrarily
long contexts, without growing the scalar precision.
-/

noncomputable section
open scoped BigOperators

namespace NumericalAttention

open TransformerAC0 CanonicalArithmetic NumericalPrimitives

variable {count : ℕ}

def score (bits offset : ℕ) (target position : Fin count) : Bits bits :=
  encode bits 0 offset (if position = target then 0 else -1)

def weight (bits offset : ℕ) (target position : Fin count) : Bits bits :=
  (arithmetic bits 0 offset).exponentiate (score bits offset target position)

def denominator (bits offset : ℕ) (target : Fin count) : Bits bits :=
  aggregate bits offset (weight bits offset target)

def probability (bits offset : ℕ) (target position : Fin count) : Bits bits :=
  (arithmetic bits 0 offset).divide
    (Fin.append (weight bits offset target position) (denominator bits offset target))

def output (bits offset : ℕ) (target : Fin count) (values : Fin count → Bool) : Bits bits :=
  aggregate bits offset (fun position => (arithmetic bits 0 offset).multiply
    (Fin.append (probability bits offset target position)
      (encode bits 0 offset (if values position then 1 else 0))))

theorem zero_supported (bits offset : ℕ) (hone : Supports bits offset 1) : Supports bits offset 0 :=
  supports_nonnegative_interval bits offset 1 0 hone (by decide) (by decide)

theorem mask_supported (bits offset : ℕ) (hone : Supports bits offset 1) (condition : Bool) :
    Supports bits offset (if condition then 1 else 0) := by
  cases condition
  · exact zero_supported bits offset hone
  · exact hone

theorem weight_exact (bits offset : ℕ) (target position : Fin count)
    (hnegative : Supports bits offset (-1)) (hone : Supports bits offset 1) :
    weight bits offset target position = encode bits 0 offset (if position = target then 1 else 0) := by
  unfold weight score
  by_cases heq : position = target
  · simp only [heq, if_true]
    exact exponentiate_zero bits offset (zero_supported bits offset hone)
  · simp only [heq, if_false]
    exact exponentiate_negative_one bits offset hnegative

/-- The denominator does not lose precision as the context grows: precisely
one exponentiated score is one and every other summand is numerical zero. -/
theorem denominator_exact (bits offset : ℕ) (target : Fin count)
    (hnegative : Supports bits offset (-1)) (hone : Supports bits offset 1) :
    denominator bits offset target = encode bits 0 offset 1 := by
  have hweights : weight bits offset target =
      fun position => encode bits 0 offset (if position = target then 1 else 0) := by
    funext position
    exact weight_exact bits offset target position hnegative hone
  unfold denominator
  rw [hweights]
  have h := aggregate_nonnegative_exact bits offset
    (fun position : Fin count => if position = target then (1 : ℤ) else 0) 1 hone
    (by intro position; dsimp only; split_ifs <;> omega) (by simp)
  simpa using h

theorem probability_exact (bits offset : ℕ) (target position : Fin count)
    (hnegative : Supports bits offset (-1)) (hone : Supports bits offset 1) :
    probability bits offset target position = encode bits 0 offset (if position = target then 1 else 0) := by
  unfold probability
  rw [weight_exact bits offset target position hnegative hone, denominator_exact bits offset target hnegative hone]
  by_cases heq : position = target
  · simp only [heq, if_true]
    simpa using divide_by_one bits offset 1 hone hone
  · simp only [heq, if_false]
    simpa using divide_by_one bits offset 0 (zero_supported bits offset hone) hone

/-- A complete rounded softmax/value head is an exact selected-value lookup.
This theorem executes the numerical operations; lookup correctness is not a
field or an assumption on the model. -/
theorem output_exact (bits offset : ℕ) (target : Fin count) (values : Fin count → Bool)
    (hnegative : Supports bits offset (-1)) (hone : Supports bits offset 1) :
    output bits offset target values = encode bits 0 offset (if values target then 1 else 0) := by
  have hterms : (fun position => (arithmetic bits 0 offset).multiply
      (Fin.append (probability bits offset target position)
        (encode bits 0 offset (if values position then 1 else 0)))) =
      (fun position : Fin count => encode bits 0 offset
        ((if position = target then (if values position then 1 else 0) else 0 : ℤ) : ℝ)) := by
    funext position
    rw [probability_exact bits offset target position hnegative hone]
    have hfirst : Supports bits offset (if position = target then 1 else 0) := by
      by_cases heq : position = target
      · simp only [heq, if_true]; exact hone
      · simp only [heq, if_false]; exact zero_supported bits offset hone
    have hsecond := mask_supported bits offset hone (values position)
    have hmul := multiply_integers bits offset
      (if position = target then 1 else 0) (if values position then 1 else 0) hfirst hsecond
    simpa only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul] using hmul
  unfold output
  rw [hterms]
  have hsum : (∑ position : Fin count,
      if position = target then (if values position then 1 else 0) else 0 : ℤ) =
      if values target then 1 else 0 := by simp
  have h := aggregate_nonnegative_exact bits offset
    (fun position : Fin count => if position = target then (if values position then (1 : ℤ) else 0) else 0)
    1 hone (by intro position; dsimp only; split_ifs <;> omega) (by rw [hsum]; split_ifs <;> omega)
  simpa only [hsum, Int.cast_ite, Int.cast_one, Int.cast_zero] using h

/-- One globally fixed two-bit signed grid suffices for arbitrarily large
contexts. It has the representable values `-2,-1,0,1`. -/
theorem two_bit_output_exact (target : Fin count) (values : Fin count → Bool) :
    output 2 2 target values = encode 2 0 2 (if values target then 1 else 0) := by
  exact output_exact 2 2 target values (by norm_num [Supports]) (by norm_num [Supports])

def query (bits offset : ℕ) (target coordinate : Fin count) : Bits bits :=
  encode bits 0 offset (if coordinate = target then -1 else 0)

def key (bits offset : ℕ) (position coordinate : Fin count) : Bits bits :=
  encode bits 0 offset (if coordinate = position then 0 else 1)

/-- The score is computed by the complete rounded query/key inner product. -/
def dotScore (bits offset : ℕ) (target position : Fin count) : Bits bits :=
  aggregate bits offset (fun coordinate => (arithmetic bits 0 offset).multiply
    (Fin.append (query bits offset target coordinate) (key bits offset position coordinate)))

theorem dotScore_exact (bits offset : ℕ) (target position : Fin count)
    (hnegative : Supports bits offset (-1)) (hone : Supports bits offset 1) :
    dotScore bits offset target position = score bits offset target position := by
  have hzero := zero_supported bits offset hone
  have hterms : (fun coordinate => (arithmetic bits 0 offset).multiply
      (Fin.append (query bits offset target coordinate) (key bits offset position coordinate))) =
      (fun coordinate : Fin count => encode bits 0 offset
        ((if coordinate = target then (if coordinate = position then 0 else -1) else 0 : ℤ) : ℝ)) := by
    funext coordinate
    have hq : Supports bits offset (if coordinate = target then -1 else 0) := by
      by_cases heq : coordinate = target
      · simp only [heq, if_true]; exact hnegative
      · simp only [heq, if_false]; exact hzero
    have hk : Supports bits offset (if coordinate = position then 0 else 1) := by
      by_cases heq : coordinate = position
      · simp only [heq, if_true]; exact hzero
      · simp only [heq, if_false]; exact hone
    have hm := multiply_integers bits offset
      (if coordinate = target then -1 else 0) (if coordinate = position then 0 else 1) hq hk
    by_cases htarget : coordinate = target <;> by_cases hposition : coordinate = position <;>
      simpa [query, key, htarget, hposition] using hm
  have hsum : (∑ coordinate : Fin count,
      if coordinate = target then (if coordinate = position then 0 else -1) else 0 : ℤ) =
      if position = target then 0 else -1 := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases heq : position = target <;> simp [heq, Ne.symm]
  unfold dotScore
  rw [hterms]
  have h := aggregate_nonpositive_exact bits offset
    (fun coordinate : Fin count => if coordinate = target then (if coordinate = position then (0 : ℤ) else -1) else 0)
    (-1) hnegative hzero (by intro coordinate; dsimp only; split_ifs <;> omega)
    (by rw [hsum]; split_ifs <;> omega)
  simpa only [hsum, score, Int.cast_ite, Int.cast_zero, Int.cast_neg, Int.cast_one] using h

end NumericalAttention
