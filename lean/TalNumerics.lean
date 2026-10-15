import Tal

/-!
# Numerical steps in Tal's Fourier-tail proof

The probability-to-tail normalization (Claim 17) and the explicit constant
comparison in Theorem 18 are proved here, separately from the circuit and
random-restriction arguments assembled in `TalComplete`.
-/

namespace TalNumerics

/-- Tal's Claim 17: absorb a prefactor using the bound `X ≤ 1`. -/
theorem absorb_prefactor {X a b : ℝ} (hzero : 0 ≤ X) (hone : X ≤ 1)
    (ha : 1 ≤ a) (hbound : X ≤ (2 : ℝ) ^ (a - b)) :
    X ≤ (2 : ℝ) ^ (1 - b / a) := by
  have hapos : 0 < a := by linarith
  calc
    X ≤ X ^ (1 / a) := Real.self_le_rpow_of_le_one hzero hone
      ((div_le_iff₀ hapos).mpr (by simpa using ha))
    _ ≤ ((2 : ℝ) ^ (a - b)) ^ (1 / a) :=
      Real.rpow_le_rpow hzero hbound (by positivity)
    _ = (2 : ℝ) ^ (1 - b / a) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      field_simp

/-- The exact constant `60d · 192^(d-1)` fits inside the project's `216^d`. -/
theorem constant_bound (d : ℕ) : 60 * d * 192 ^ (d - 1) ≤ 216 ^ d := by
  by_cases hd : d < 8
  · interval_cases d <;> norm_num
  · have hd' : 8 ≤ d := by omega
    induction d, hd' using Nat.le_induction with
    | base => norm_num
    | succ d hd ih =>
        have hratio : 192 * (d + 1) ≤ 216 * d := by omega
        have hstep := Nat.mul_le_mul_right (192 ^ (d - 1)) hratio
        have hscaled := Nat.mul_le_mul_left 60 hstep
        have hind := Nat.mul_le_mul_right 216 (ih (by omega))
        have hexponent : d = (d - 1) + 1 := by omega
        have hpow : 192 ^ d = 192 ^ (d - 1) * 192 := by
          nth_rw 1 [hexponent]
          rw [pow_succ]
        rw [show d + 1 - 1 = d by omega, pow_succ]
        rw [hpow]
        nlinarith

theorem logb_size_ge_one (size : ℕ) (hsize : 1 < size) :
    1 ≤ Real.logb 2 size := by
  have htwo : (2 : ℝ) ≤ size := by exact_mod_cast (show 2 ≤ size by omega)
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) htwo
  simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

/-- The size simplification used at the end of Tal's Theorem 18. -/
theorem logb_double_size_le (size : ℕ) (hsize : 1 < size) :
    Real.logb 2 (2 * size : ℕ) ≤ 2 * Real.logb 2 size := by
  have hsize0 : (size : ℝ) ≠ 0 := by exact_mod_cast (show size ≠ 0 by omega)
  have hlog := logb_size_ge_one size hsize
  push_cast
  rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hsize0,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  linarith

/-- Compare the induction's denominator to the exact displayed Tal constant. -/
theorem denominator_bound (depth size : ℕ) (hsize : 1 < size) :
    60 * (depth : ℝ) * 96 ^ (depth - 1) *
        Real.logb 2 (2 * size : ℕ) ^ (depth - 1) ≤
      (216 : ℝ) ^ depth * Real.logb 2 size ^ (depth - 1) := by
  have hc : 60 * (depth : ℝ) * (192 : ℝ) ^ (depth - 1) ≤ (216 : ℝ) ^ depth := by
    exact_mod_cast constant_bound depth
  have hlog := logb_double_size_le size hsize
  have hlog0 : 0 ≤ Real.logb 2 (2 * size : ℕ) := by
    exact (Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 1 < 2 * size by omega))).le
  have hpower := pow_le_pow_left₀ hlog0 hlog (depth - 1)
  calc
    _ ≤ 60 * (depth : ℝ) * 96 ^ (depth - 1) *
        (2 * Real.logb 2 size) ^ (depth - 1) := by gcongr
    _ = (60 * (depth : ℝ) * 192 ^ (depth - 1)) *
        Real.logb 2 size ^ (depth - 1) := by
      rw [mul_pow]
      have hp : (96 : ℝ) ^ (depth - 1) * 2 ^ (depth - 1) = 192 ^ (depth - 1) := by
        rw [← mul_pow]
        norm_num
      calc
        _ = 60 * (depth : ℝ) * (96 ^ (depth - 1) * 2 ^ (depth - 1)) *
            Real.logb 2 size ^ (depth - 1) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc
      (pow_nonneg (le_trans zero_le_one (logb_size_ge_one size hsize)) _)

/-- Theorem 18's numerical reduction, once the actual depth induction is proved.

This is only an arithmetic implication; `hbound` is not supplied by a
switching-lemma proof in this module and is not substituted for Tal's premise.
-/
theorem raw_bound_to_tailBound {X : ℝ} (depth size degree : ℕ)
    (hdepth : 1 ≤ depth) (hsize : 1 < size) (hzero : 0 ≤ X) (hone : X ≤ 1)
    (hbound : X ≤ (2 : ℝ) ^ (3 * (depth : ℝ) -
      (degree : ℝ) / (20 * 96 ^ (depth - 1) * Real.logb 2 (2 * size : ℕ) ^ (depth - 1)))) :
    X ≤ Tal.tailBound depth size degree := by
  have hd : 0 < (depth : ℝ) := by exact_mod_cast (show 0 < depth by omega)
  have hl : 0 < Real.logb 2 (2 * size : ℕ) :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 1 < 2 * size by omega))
  have hden : 0 < 60 * (depth : ℝ) * 96 ^ (depth - 1) *
      Real.logb 2 (2 * size : ℕ) ^ (depth - 1) := by positivity
  have hnormalized := absorb_prefactor hzero hone
    (show 1 ≤ 3 * (depth : ℝ) by exact_mod_cast (show 1 ≤ 3 * depth by omega)) hbound
  have heq : ((degree : ℝ) /
      (20 * 96 ^ (depth - 1) * Real.logb 2 (2 * size : ℕ) ^ (depth - 1))) /
        (3 * (depth : ℝ)) =
      (degree : ℝ) / (60 * (depth : ℝ) * 96 ^ (depth - 1) *
        Real.logb 2 (2 * size : ℕ) ^ (depth - 1)) := by
    rw [div_div]
    congr 1
    ring
  rw [heq] at hnormalized
  have hratio := div_le_div_of_nonneg_left (Nat.cast_nonneg degree) hden
    (denominator_bound depth size hsize)
  calc
    X ≤ _ := hnormalized
    _ ≤ (2 : ℝ) ^ (1 - (degree : ℝ) /
        (216 ^ depth * Real.logb 2 size ^ (depth - 1))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = Tal.tailBound depth size degree := by
      unfold Tal.tailBound
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      congr 1
      rw [neg_div]

end TalNumerics
