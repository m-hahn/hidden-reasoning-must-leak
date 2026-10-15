import TalMultiSwitching
import TalBroadNumerics

/-!
# The constant-parameter common-tree switching estimate

These bounds apply to the actual bad event already proved in
`TalMultiSwitching`. They select `p=1/(30t)`, account for integer floors,
and absorb the family-size prefactor using the probability bound by one.
-/

noncomputable section
namespace TalSwitchingNumerics
open Algebraic AC0

def parameter (width : ℕ) : NNReal := 1 / (30 * width)

theorem parameter_small (width : ℕ) [NeZero width] : 30 * parameter width * width = 1 := by
  have hw : (width : NNReal) ≠ 0 := by exact_mod_cast NeZero.ne width
  unfold parameter
  field_simp [hw]

theorem geometric_pow_le (length : ℕ) :
    (5 / 6 : ℝ) ^ length ≤ (2 : ℝ) ^ (-(length : ℝ) / 4) := by
  have hfourth : (5 / 6 : ℝ) ^ (4 : ℝ) ≤ ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ (4 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_natCast, Real.rpow_neg_one]
  have hbase : (5 / 6 : ℝ) ≤ (2 : ℝ) ^ (-1 / 4 : ℝ) :=
    (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 4)).mp hfourth
  calc
    _ ≤ ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ length := pow_le_pow_left₀ (by norm_num) hbase length
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

theorem geometric_floor_le (width degree : ℕ) [NeZero width] :
    (5 / 6 : ℝ) ^ ⌊(degree : ℝ) / (360 * width)⌋₊ ≤
      2 * (2 : ℝ) ^ (-(degree : ℝ) / (1440 * width)) := by
  have hw : (0 : ℝ) < width := by exact_mod_cast NeZero.pos width
  have hfloor := Nat.lt_floor_add_one ((degree : ℝ) / (360 * width))
  have hratio : ((degree : ℝ) / (360 * width)) / 4 = (degree : ℝ) / (1440 * width) := by
    rw [div_div]
    congr 1
    ring
  calc
    _ ≤ (2 : ℝ) ^ (-((⌊(degree : ℝ) / (360 * width)⌋₊ : ℕ) : ℝ) / 4) := geometric_pow_le _
    _ ≤ (2 : ℝ) ^ (1 - (degree : ℝ) / (1440 * width)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [← hratio]
      linarith
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      congr 1
      rw [neg_div]

/-- Direct probability estimate before prefactor absorption. -/
theorem probability_bad_le_raw {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (hwidth : ∀ index, (family index).WidthAtMost width) (degree : ℕ) :
    TalRandomRestriction.probability (parameter width : ℝ)
        (TalMultiSwitching.Bad family (Nat.log 2 (2 * m)) ⌊(degree : ℝ) / (360 * width)⌋₊) ≤
      2 * m * (2 : ℝ) ^ (-(degree : ℝ) / (1440 * width)) := by
  have h := TalMultiSwitching.real_probability_bad_le_geometric family (Nat.log 2 (2 * m)) hwidth
    ⌊(degree : ℝ) / (360 * width)⌋₊ (TalMultiSwitching.default_shallow_indices m) (parameter width)
    (parameter_small width).le
  have hgeom := mul_le_mul_of_nonneg_left (geometric_floor_le width degree) (Nat.cast_nonneg m)
  exact h.trans (by simpa only [mul_left_comm, mul_assoc] using hgeom)

/-- Tal's size-prefactor absorption applied to the actual common-tree bad probability. -/
theorem probability_bad_le {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (hwidth : ∀ index, (family index).WidthAtMost width) (degree : ℕ) :
    TalRandomRestriction.probability (parameter width : ℝ)
        (TalMultiSwitching.Bad family (Nat.log 2 (2 * m)) ⌊(degree : ℝ) / (360 * width)⌋₊) ≤
      2 * (2 : ℝ) ^ (-(degree : ℝ) / (1440 * width * Real.logb 2 (2 * m : ℕ))) := by
  have hm : 1 < 2 * m := by have h := NeZero.pos m; omega
  have hmReal : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  have hlog := TalNumerics.logb_size_ge_one (2 * m) hm
  have hp := (TalMultiSwitching.small_parameter_base (parameter width) (parameter_small width).le).1
  have hzero := TalRandomRestriction.probability_nonneg (parameter width).coe_nonneg
    (NNReal.coe_le_coe.mpr hp.le)
    (TalMultiSwitching.Bad family (Nat.log 2 (2 * m)) ⌊(degree : ℝ) / (360 * width)⌋₊)
  have hone := TalRandomRestriction.probability_le_one (parameter width).coe_nonneg
    (NNReal.coe_le_coe.mpr hp.le)
    (TalMultiSwitching.Bad family (Nat.log 2 (2 * m)) ⌊(degree : ℝ) / (360 * width)⌋₊)
  have hraw := probability_bad_le_raw family hwidth degree
  have hexponential :
      2 * (m : ℝ) * (2 : ℝ) ^ (-(degree : ℝ) / (1440 * width)) =
        (2 : ℝ) ^ (Real.logb 2 (2 * m : ℕ) - (degree : ℝ) / (1440 * width)) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hmReal]
    push_cast
    congr 1
    rw [neg_div]
  rw [hexponential] at hraw
  have h := TalNumerics.absorb_prefactor hzero hone hlog hraw
  rw [div_div] at h
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      congr 1
      rw [neg_div]

/-- The degree retained after the two integer floors in the depth reduction. -/
theorem retained_degree_bound (width degree : ℕ) [NeZero width] :
    (degree : ℝ) / (72 * width) - 1 ≤
      ((⌊(degree : ℝ) / (60 * width)⌋₊ - ⌊(degree : ℝ) / (360 * width)⌋₊ : ℕ) : ℝ) := by
  have hw : (0 : ℝ) < width := by exact_mod_cast NeZero.pos width
  have hdegree : (0 : ℝ) ≤ degree := Nat.cast_nonneg degree
  have horder : (degree : ℝ) / (360 * width) ≤ (degree : ℝ) / (60 * width) :=
    div_le_div_of_nonneg_left hdegree (by positivity) (by nlinarith)
  rw [Nat.cast_sub (Nat.floor_mono horder)]
  have hlower := Nat.lt_floor_add_one ((degree : ℝ) / (60 * width))
  have hupper := Nat.floor_le (show 0 ≤ (degree : ℝ) / (360 * width) by positivity)
  have hratio : (degree : ℝ) / (60 * width) - (degree : ℝ) / (360 * width) =
      (degree : ℝ) / (72 * width) := by
    field_simp [ne_of_gt hw]
    ring
  linarith

end TalSwitchingNumerics
