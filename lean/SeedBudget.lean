import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Derived sublinear seed and stretch capacity

For k ≥ 1 and c₀ > k, choose c strictly between k and c₀. A rounded seed
of size C (N+1)^(k/c) has enough c₀-power stretch for any fixed multiple of
(N+1)^k (log₂(N+1)+1). The coefficient and all rounding/resource bounds are
derived here; pad capacity is not imported as an extra hypothesis.
-/

noncomputable section
namespace SeedBudget

def intermediate (k stretch : ℝ) : ℝ := (k + stretch) / 2
def seedExponent (k stretch : ℝ) : ℝ := k / intermediate k stretch
def slack (k stretch : ℝ) : ℝ := seedExponent k stretch * stretch - k
def logCoefficient (delta : ℝ) : ℝ := 1 / (delta * Real.log 2) + 1
def coefficient (degree stretch size : ℝ) : ℝ := max 1 (size * logCoefficient (slack degree stretch))
def length (degree stretch size : ℝ) (n : ℕ) : ℕ :=
  ⌈coefficient degree stretch size * (n + 1 : ℝ) ^ seedExponent degree stretch⌉₊

theorem intermediate_bounds {k stretch : ℝ} (hk : 0 < k) (hstretch : k < stretch) :
    k < intermediate k stretch ∧ intermediate k stretch < stretch ∧ 0 < intermediate k stretch := by
  unfold intermediate
  constructor
  · linarith
  · constructor <;> linarith

theorem exponent_bounds {k stretch : ℝ} (hk : 0 < k) (hstretch : k < stretch) :
    0 < seedExponent k stretch ∧ seedExponent k stretch < 1 := by
  have hc := intermediate_bounds hk hstretch
  exact ⟨div_pos hk hc.2.2, (div_lt_one hc.2.2).mpr hc.1⟩

theorem slack_positive {k stretch : ℝ} (hk : 0 < k) (hstretch : k < stretch) : 0 < slack k stretch := by
  have hc := intermediate_bounds hk hstretch
  have ha := (exponent_bounds hk hstretch).1
  have he : seedExponent k stretch * intermediate k stretch = k := by
    unfold seedExponent
    exact div_mul_cancel₀ k hc.2.2.ne'
  have h := mul_lt_mul_of_pos_left hc.2.1 ha
  unfold slack
  linarith

theorem logarithm_bound {delta : ℝ} (hdelta : 0 < delta) (n : ℕ) :
    (Nat.log 2 (n + 1) : ℝ) + 1 ≤ logCoefficient delta * (n + 1 : ℝ) ^ delta := by
  have hx : 1 ≤ (n + 1 : ℝ) := by norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnat := Real.natLog_le_logb (n + 1) 2
  have hlog := Real.log_le_rpow_div (x := (n + 1 : ℝ)) (by positivity) hdelta
  have hdiv := div_le_div_of_nonneg_right hlog hlog2.le
  have hpow := Real.one_le_rpow hx hdelta.le
  simp only [Real.logb, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hnat
  have hbound : (Nat.log 2 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ delta / (delta * Real.log 2) := by
    calc
      _ ≤ Real.log (n + 1 : ℝ) / Real.log 2 := hnat
      _ ≤ ((n + 1 : ℝ) ^ delta / delta) / Real.log 2 := hdiv
      _ = _ := by rw [div_div]
  unfold logCoefficient
  calc
    _ ≤ (n + 1 : ℝ) ^ delta / (delta * Real.log 2) + (n + 1 : ℝ) ^ delta := add_le_add hbound hpow
    _ = _ := by ring

/-- Global pad-capacity bound, including integer rounding. -/
theorem stretch_capacity {k stretch size : ℝ} (hk : 1 ≤ k) (hstretch : k < stretch) (hsize : 0 ≤ size) (n : ℕ) :
    size * (n + 1 : ℝ) ^ k * ((Nat.log 2 (n + 1) : ℝ) + 1) ≤ (length k stretch size n : ℝ) ^ stretch := by
  have hkpos : 0 < k := by linarith
  have hs := slack_positive hkpos hstretch
  have hx : 0 ≤ (n + 1 : ℝ) := by positivity
  have ha := Real.rpow_nonneg hx (seedExponent k stretch)
  have hcoef : 1 ≤ coefficient k stretch size := le_max_left _ _
  have hcoef0 : 0 ≤ coefficient k stretch size := by linarith
  have hcoefPow : coefficient k stretch size ≤ coefficient k stretch size ^ stretch := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hcoef (by linarith : (1 : ℝ) ≤ stretch)
  have hceil := Nat.le_ceil (coefficient k stretch size * (n + 1 : ℝ) ^ seedExponent k stretch)
  have hseed := Real.rpow_le_rpow (mul_nonneg hcoef0 ha) hceil (by linarith : 0 ≤ stretch)
  calc
    _ ≤ size * (n + 1 : ℝ) ^ k * (logCoefficient (slack k stretch) * (n + 1 : ℝ) ^ slack k stretch) :=
      mul_le_mul_of_nonneg_left (logarithm_bound hs n) (mul_nonneg hsize (Real.rpow_nonneg hx k))
    _ = (size * logCoefficient (slack k stretch)) * (n + 1 : ℝ) ^ (seedExponent k stretch * stretch) := by
      rw [show seedExponent k stretch * stretch = k + slack k stretch by unfold slack; ring, Real.rpow_add (by positivity)]
      ring
    _ ≤ coefficient k stretch size * (n + 1 : ℝ) ^ (seedExponent k stretch * stretch) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx _)
    _ ≤ coefficient k stretch size ^ stretch * (n + 1 : ℝ) ^ (seedExponent k stretch * stretch) :=
      mul_le_mul_of_nonneg_right hcoefPow (Real.rpow_nonneg hx _)
    _ = (coefficient k stretch size * (n + 1 : ℝ) ^ seedExponent k stretch) ^ stretch := by
      rw [Real.mul_rpow hcoef0 ha, ← Real.rpow_mul hx]
    _ ≤ _ := hseed

theorem seed_power_bound {k stretch size : ℝ} (hk : 0 < k) (hstretch : k < stretch) (n : ℕ) :
    (length k stretch size n : ℝ) ≤ (coefficient k stretch size + 1) * (n + 1 : ℝ) ^ seedExponent k stretch := by
  have hx : 1 ≤ (n + 1 : ℝ) := by norm_num
  have ha := Real.one_le_rpow hx (exponent_bounds hk hstretch).1.le
  have hc : 0 ≤ coefficient k stretch size := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have h := Nat.ceil_lt_add_one (a := coefficient k stretch size * (n + 1 : ℝ) ^ seedExponent k stretch)
    (mul_nonneg hc (Real.rpow_nonneg (x := (n + 1 : ℝ)) (by positivity) (seedExponent k stretch)))
  unfold length
  nlinarith

theorem seed_polynomial_bound {k stretch size : ℝ} (hk : 0 < k) (hstretch : k < stretch) (n : ℕ) :
    length k stretch size n ≤ ⌈coefficient k stretch size⌉₊ * (n + 1) := by
  have hx : 1 ≤ (n + 1 : ℝ) := by norm_num
  have ha : (n + 1 : ℝ) ^ seedExponent k stretch ≤ (n + 1 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx (exponent_bounds hk hstretch).2.le
  have hc : 0 ≤ coefficient k stretch size := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  unfold length
  apply Nat.ceil_le.mpr
  push_cast
  exact mul_le_mul (Nat.le_ceil _) ha (Real.rpow_nonneg (by positivity) _) (Nat.cast_nonneg _)

/-- A polynomial inverse bound for the chosen seed lengths. This is also
what permits seed-indexed PRG security to be reindexed by input length. -/
theorem seed_inverse_bound {k stretch size : ℝ} (hk : 0 < k) (hstretch : k < stretch) :
    ∃ degree : ℕ, 1 ≤ degree ∧ ∀ n : ℕ, n + 1 ≤ (length k stretch size n) ^ degree := by
  have ha := (exponent_bounds hk hstretch).1
  let degree : ℕ := ⌈1 / seedExponent k stretch⌉₊ + 1
  have hd : 1 ≤ degree := by dsimp [degree]; omega
  have hdreal : 1 / seedExponent k stretch ≤ (degree : ℝ) := by
    exact (Nat.le_ceil _).trans (by dsimp [degree]; push_cast; linarith)
  have hexponent : 1 ≤ seedExponent k stretch * (degree : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hdreal ha.le
    rw [mul_one_div_cancel ha.ne'] at h
    exact h
  refine ⟨degree, hd, ?_⟩
  intro n
  have hx : 1 ≤ (n + 1 : ℝ) := by norm_num
  have hx0 : 0 ≤ (n + 1 : ℝ) := by positivity
  have hp := Real.rpow_nonneg hx0 (seedExponent k stretch)
  have hseed : (n + 1 : ℝ) ^ seedExponent k stretch ≤ (length k stretch size n : ℝ) := by
    calc
      _ = 1 * (n + 1 : ℝ) ^ seedExponent k stretch := (one_mul _).symm
      _ ≤ coefficient k stretch size * (n + 1 : ℝ) ^ seedExponent k stretch :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hp
      _ ≤ _ := Nat.le_ceil _
  have hpow := Real.rpow_le_rpow hp hseed (Nat.cast_nonneg degree)
  rw [← Real.rpow_mul hx0, Real.rpow_natCast] at hpow
  have hbase : (n + 1 : ℝ) ≤ (n + 1 : ℝ) ^ (seedExponent k stretch * (degree : ℝ)) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hexponent
  exact_mod_cast hbase.trans hpow

theorem stretch_floor_capacity {k stretch size : ℝ} (hk : 1 ≤ k) (hstretch : k < stretch)
    (hsize : 0 ≤ size) (n payload : ℕ)
    (payload_bound : (payload : ℝ) ≤ size * (n + 1 : ℝ) ^ k * ((Nat.log 2 (n + 1) : ℝ) + 1)) :
    payload ≤ ⌊(length k stretch size n : ℝ) ^ stretch⌋₊ :=
  Nat.le_floor (payload_bound.trans (stretch_capacity hk hstretch hsize n))

/-- Explicitly choose the intermediate exponent, rather than supplying it
or the sufficient pad length as a realization certificate. -/
theorem sublinear_seed_and_capacity {k stretch size : ℝ} (hk : 1 ≤ k) (hstretch : k < stretch) (hsize : 0 ≤ size) :
    ∃ c : ℝ, k < c ∧ c < stretch ∧ 0 < k / c ∧ k / c < 1 ∧
      (∀ n : ℕ, (length k stretch size n : ℝ) ≤ (coefficient k stretch size + 1) * (n + 1 : ℝ) ^ (k / c)) ∧
      (∀ n : ℕ, size * (n + 1 : ℝ) ^ k * ((Nat.log 2 (n + 1) : ℝ) + 1) ≤ (length k stretch size n : ℝ) ^ stretch) := by
  have hp : 0 < k := by linarith
  have hc := intermediate_bounds hp hstretch
  have ha := exponent_bounds hp hstretch
  exact ⟨intermediate k stretch, hc.1, hc.2.1, ha.1, ha.2,
    seed_power_bound hp hstretch, stretch_capacity hk hstretch hsize⟩

end SeedBudget
