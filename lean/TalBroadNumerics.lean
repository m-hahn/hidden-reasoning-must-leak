import TalOptimizedNumerics

/-!
# Constants for the all-block family switching proof

The count `(3t)^D` allows arbitrary final-block differences. Signed wiring
avoids doubling the gate budget, so the `72 log_2(2m)` induction scale still
fits the unchanged `216^d` conclusion. The raw bound is an explicit hypothesis
of this arithmetic lemma; `TalComplete` supplies it from the proved circuit
induction in `TalNetworkFourier`.
-/

namespace TalBroadNumerics

theorem constant_bound (depth : ℕ) : 82 * depth * 144 ^ (depth - 1) ≤ 216 ^ depth := by
  calc
    _ ≤ 82 * depth * 180 ^ (depth - 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 144 ≤ 180) _)
    _ ≤ _ := TalOptimizedNumerics.constant_bound depth

theorem denominator_bound (depth size : ℕ) (hsize : 1 < size) :
    82 * (depth : ℝ) * 72 ^ (depth - 1) *
        Real.logb 2 (2 * size : ℕ) ^ (depth - 1) ≤
      (216 : ℝ) ^ depth * Real.logb 2 size ^ (depth - 1) := by
  have hc : 82 * (depth : ℝ) * (144 : ℝ) ^ (depth - 1) ≤ (216 : ℝ) ^ depth := by
    exact_mod_cast constant_bound depth
  have hlog := TalNumerics.logb_double_size_le size hsize
  have hlog0 : 0 ≤ Real.logb 2 (2 * size : ℕ) := by
    exact (Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 1 < 2 * size by omega))).le
  calc
    _ ≤ 82 * (depth : ℝ) * 72 ^ (depth - 1) *
        (2 * Real.logb 2 size) ^ (depth - 1) := by gcongr
    _ = (82 * (depth : ℝ) * 144 ^ (depth - 1)) *
        Real.logb 2 size ^ (depth - 1) := by
      rw [mul_pow]
      have hp : (72 : ℝ) ^ (depth - 1) * 2 ^ (depth - 1) = 144 ^ (depth - 1) := by
        rw [← mul_pow]
        norm_num
      calc
        _ = 82 * (depth : ℝ) * (72 ^ (depth - 1) * 2 ^ (depth - 1)) *
            Real.logb 2 size ^ (depth - 1) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc
      (pow_nonneg (le_trans zero_le_one (TalNumerics.logb_size_ge_one size hsize)) _)

/-- Arithmetic normalization, applied to the locally proved raw circuit bound
by `TalComplete.fourierTailTheorem`. -/
theorem raw_bound_to_tailBound {X : ℝ} (depth size degree : ℕ)
    (hdepth : 1 ≤ depth) (hsize : 1 < size) (hzero : 0 ≤ X) (hone : X ≤ 1)
    (hbound : X ≤ (17 : ℝ) ^ depth * (2 : ℝ) ^
      (-(degree : ℝ) / (20 * 72 ^ (depth - 1) *
        Real.logb 2 (2 * size : ℕ) ^ (depth - 1)))) :
    X ≤ Tal.tailBound depth size degree := by
  have hd : 0 < (depth : ℝ) := by exact_mod_cast (show 0 < depth by omega)
  have hl : 0 < Real.logb 2 (2 * size : ℕ) :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 1 < 2 * size by omega))
  have hden : 0 < 82 * (depth : ℝ) * 72 ^ (depth - 1) *
      Real.logb 2 (2 * size : ℕ) ^ (depth - 1) := by positivity
  have hexponential : X ≤ (2 : ℝ) ^ ((41 / 10) * (depth : ℝ) -
      (degree : ℝ) / (20 * 72 ^ (depth - 1) *
        Real.logb 2 (2 * size : ℕ) ^ (depth - 1))) := by
    calc
      X ≤ _ := hbound
      _ ≤ (2 : ℝ) ^ ((41 / 10) * (depth : ℝ)) * (2 : ℝ) ^
          (-(degree : ℝ) / (20 * 72 ^ (depth - 1) *
            Real.logb 2 (2 * size : ℕ) ^ (depth - 1))) := by
        exact mul_le_mul_of_nonneg_right (TalOptimizedNumerics.prefactor_bound depth) (by positivity)
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
  have hnormalized := TalNumerics.absorb_prefactor hzero hone
    (show 1 ≤ (41 / 10 : ℝ) * depth by
      have : (1 : ℝ) ≤ depth := by exact_mod_cast hdepth
      linarith) hexponential
  have heq : ((degree : ℝ) / (20 * 72 ^ (depth - 1) *
      Real.logb 2 (2 * size : ℕ) ^ (depth - 1))) / ((41 / 10) * (depth : ℝ)) =
      (degree : ℝ) / (82 * (depth : ℝ) * 72 ^ (depth - 1) *
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

end TalBroadNumerics
