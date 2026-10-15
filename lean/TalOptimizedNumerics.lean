import TalNumerics

/-!
# Constants for the second-moment version of Tal's induction

These are arithmetic lemmas, not circuit assumptions. The improved switching
advice count compensates for the factor-eight Fourier transfer. A factor-two
gate-normalization overhead is allowed while retaining the original `216^d`.
-/

namespace TalOptimizedNumerics

theorem half_pow_eq (k : ℕ) :
    (1 / 2 : ℝ) ^ k = (2 : ℝ) ^ (-(k : ℝ)) := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num [Real.rpow_neg_one],
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem eight_half_pow_floor_le (x : ℝ) :
    8 * (1 / 2 : ℝ) ^ ⌊x⌋₊ ≤ 16 * (2 : ℝ) ^ (-x) := by
  have hfloor := Nat.lt_floor_add_one x
  rw [half_pow_eq]
  calc
    _ ≤ 8 * (2 : ℝ) ^ (1 - x) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring

theorem constant_bound (d : ℕ) : 82 * d * 180 ^ (d - 1) ≤ 216 ^ d := by
  by_cases hd : d < 5
  · interval_cases d <;> norm_num
  · have hd' : 5 ≤ d := by omega
    induction d, hd' using Nat.le_induction with
    | base => norm_num
    | succ d hd ih =>
        have hratio : 180 * (d + 1) ≤ 216 * d := by omega
        have hstep := Nat.mul_le_mul_right (180 ^ (d - 1)) hratio
        have hscaled := Nat.mul_le_mul_left 82 hstep
        have hind := Nat.mul_le_mul_right 216 (ih (by omega))
        have hexponent : d = (d - 1) + 1 := by omega
        have hpow : 180 ^ d = 180 ^ (d - 1) * 180 := by
          nth_rw 1 [hexponent]
          rw [pow_succ]
        rw [show d + 1 - 1 = d by omega, pow_succ, hpow]
        nlinarith

theorem logb_four_size_le (size : ℕ) (hsize : 1 < size) :
    Real.logb 2 (4 * size : ℕ) ≤ 3 * Real.logb 2 size := by
  have hsize0 : (size : ℝ) ≠ 0 := by exact_mod_cast (show size ≠ 0 by omega)
  have hlog := TalNumerics.logb_size_ge_one size hsize
  have hfour : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  push_cast
  rw [Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0) hsize0, hfour]
  linarith

theorem logb_seventeen_le : Real.logb 2 (17 : ℝ) ≤ 41 / 10 := by
  have hpower : (17 : ℝ) ^ 10 ≤ (2 : ℝ) ^ 41 := by norm_num
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 17 ^ 10) hpower
  rw [← Real.rpow_natCast, ← Real.rpow_natCast,
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0 : ℝ) < 17),
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog
  norm_num at hlog
  linarith

theorem prefactor_bound (depth : ℕ) :
    (17 : ℝ) ^ depth ≤ (2 : ℝ) ^ ((41 / 10) * (depth : ℝ)) := by
  have hbase : (17 : ℝ) ≤ (2 : ℝ) ^ (41 / 10 : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 17)).mp logb_seventeen_le
  calc
    _ ≤ ((2 : ℝ) ^ (41 / 10 : ℝ)) ^ depth := pow_le_pow_left₀ (by norm_num) hbase _
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem denominator_bound (depth size : ℕ) (hsize : 1 < size) :
    82 * (depth : ℝ) * 60 ^ (depth - 1) *
        Real.logb 2 (4 * size : ℕ) ^ (depth - 1) ≤
      (216 : ℝ) ^ depth * Real.logb 2 size ^ (depth - 1) := by
  have hc : 82 * (depth : ℝ) * (180 : ℝ) ^ (depth - 1) ≤ (216 : ℝ) ^ depth := by
    exact_mod_cast constant_bound depth
  have hlog := logb_four_size_le size hsize
  have hlog0 : 0 ≤ Real.logb 2 (4 * size : ℕ) := by
    exact (Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 1 < 4 * size by omega))).le
  calc
    _ ≤ 82 * (depth : ℝ) * 60 ^ (depth - 1) *
        (3 * Real.logb 2 size) ^ (depth - 1) := by gcongr
    _ = (82 * (depth : ℝ) * 180 ^ (depth - 1)) *
        Real.logb 2 size ^ (depth - 1) := by
      rw [mul_pow]
      have hp : (60 : ℝ) ^ (depth - 1) * 3 ^ (depth - 1) = 180 ^ (depth - 1) := by
        rw [← mul_pow]
        norm_num
      calc
        _ = 82 * (depth : ℝ) * (60 ^ (depth - 1) * 3 ^ (depth - 1)) *
            Real.logb 2 size ^ (depth - 1) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc
      (pow_nonneg (le_trans zero_le_one (TalNumerics.logb_size_ge_one size hsize)) _)

/-- Arithmetic normalization only. `TalComplete` uses the all-block variant
in `TalBroadNumerics` with the raw bound proved in `TalNetworkFourier`. -/
theorem raw_bound_to_tailBound {X : ℝ} (depth size degree : ℕ)
    (hdepth : 1 ≤ depth) (hsize : 1 < size) (hzero : 0 ≤ X) (hone : X ≤ 1)
    (hbound : X ≤ (17 : ℝ) ^ depth * (2 : ℝ) ^
      (-(degree : ℝ) / (20 * 60 ^ (depth - 1) *
        Real.logb 2 (4 * size : ℕ) ^ (depth - 1)))) :
    X ≤ Tal.tailBound depth size degree := by
  have hd : 0 < (depth : ℝ) := by exact_mod_cast (show 0 < depth by omega)
  have hl : 0 < Real.logb 2 (4 * size : ℕ) :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 1 < 4 * size by omega))
  have hden : 0 < 82 * (depth : ℝ) * 60 ^ (depth - 1) *
      Real.logb 2 (4 * size : ℕ) ^ (depth - 1) := by positivity
  have hexponential : X ≤ (2 : ℝ) ^ ((41 / 10) * (depth : ℝ) -
      (degree : ℝ) / (20 * 60 ^ (depth - 1) *
        Real.logb 2 (4 * size : ℕ) ^ (depth - 1))) := by
    calc
      X ≤ _ := hbound
      _ ≤ (2 : ℝ) ^ ((41 / 10) * (depth : ℝ)) * (2 : ℝ) ^
          (-(degree : ℝ) / (20 * 60 ^ (depth - 1) *
            Real.logb 2 (4 * size : ℕ) ^ (depth - 1))) := by
        exact mul_le_mul_of_nonneg_right (prefactor_bound depth) (by positivity)
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
  have hnormalized := TalNumerics.absorb_prefactor hzero hone
    (show 1 ≤ (41 / 10 : ℝ) * depth by
      have : (1 : ℝ) ≤ depth := by exact_mod_cast hdepth
      linarith) hexponential
  have heq : ((degree : ℝ) / (20 * 60 ^ (depth - 1) *
      Real.logb 2 (4 * size : ℕ) ^ (depth - 1))) / ((41 / 10) * (depth : ℝ)) =
      (degree : ℝ) / (82 * (depth : ℝ) * 60 ^ (depth - 1) *
        Real.logb 2 (4 * size : ℕ) ^ (depth - 1)) := by
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

end TalOptimizedNumerics
