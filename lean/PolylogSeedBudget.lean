import SeedBudget

/-!
# Sublinear seeds for arbitrary fixed polylogarithmic overhead

A payload bounded by `size * (n + 1) * (log₂(n + 1) + 1)^power`
still needs only a sublinear seed for every stretch greater than one.
The logarithmic exponent is fixed before the input length is quantified.
No pad-capacity or reindexed-security premise is assumed.
-/

noncomputable section
namespace PolylogSeedBudget

def degree (stretch : ℝ) : ℝ := (1 + stretch) / 2
def delta (power : ℕ) (stretch : ℝ) : ℝ := (degree stretch - 1) / (power + 1 : ℝ)
def adjustedSize (power : ℕ) (stretch size : ℝ) : ℝ :=
  size * SeedBudget.logCoefficient (delta power stretch) ^ power
def length (power : ℕ) (stretch size : ℝ) : ℕ → ℕ :=
  SeedBudget.length (degree stretch) stretch (adjustedSize power stretch size)

theorem degree_bounds {stretch : ℝ} (h : 1 < stretch) :
    1 < degree stretch ∧ degree stretch < stretch := by
  unfold degree
  constructor <;> linarith

theorem delta_pos (power : ℕ) {stretch : ℝ} (h : 1 < stretch) :
    0 < delta power stretch := by
  unfold delta
  exact div_pos (by have hb := (degree_bounds h).1; linarith) (by positivity)

theorem logCoefficient_pos (power : ℕ) {stretch : ℝ} (h : 1 < stretch) :
    0 < SeedBudget.logCoefficient (delta power stretch) := by
  have hd := delta_pos power h
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold SeedBudget.logCoefficient
  positivity

theorem logarithm_power_bound (power : ℕ) {stretch : ℝ} (h : 1 < stretch) (n : ℕ) :
    ((Nat.log 2 (n + 1) : ℝ) + 1) ^ power ≤
      SeedBudget.logCoefficient (delta power stretch) ^ power *
        (n + 1 : ℝ) ^ (degree stretch - 1) := by
  have hd := delta_pos power h
  have hc := logCoefficient_pos power h
  have hlog := SeedBudget.logarithm_bound hd n
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) + 1) hlog power
  have hmargin : delta power stretch * (power : ℝ) ≤ degree stretch - 1 := by
    have heq : delta power stretch * (power + 1 : ℝ) = degree stretch - 1 := by
      unfold delta
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hpower : ((n + 1 : ℝ) ^ delta power stretch) ^ power ≤
      (n + 1 : ℝ) ^ (degree stretch - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hmargin
  calc
    _ ≤ SeedBudget.logCoefficient (delta power stretch) ^ power *
        ((n + 1 : ℝ) ^ delta power stretch) ^ power := by simpa only [mul_pow] using hs
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

theorem capacity (power : ℕ) {stretch size : ℝ}
    (hstretch : 1 < stretch) (hsize : 0 ≤ size) (n : ℕ) :
    size * (n + 1 : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + 1) ^ power ≤
      (length power stretch size n : ℝ) ^ stretch := by
  have hb := degree_bounds hstretch
  have hc := logCoefficient_pos power hstretch
  have hbound := SeedBudget.stretch_capacity hb.1.le hb.2
    (show 0 ≤ adjustedSize power stretch size by unfold adjustedSize; positivity) n
  have hlog := mul_le_mul_of_nonneg_left (logarithm_power_bound power hstretch n)
    (show 0 ≤ size * (n + 1 : ℝ) by positivity)
  have hpower : (n + 1 : ℝ) * (n + 1 : ℝ) ^ (degree stretch - 1) =
      (n + 1 : ℝ) ^ degree stretch := by
    calc
      _ = (n + 1 : ℝ) ^ (1 : ℝ) * (n + 1 : ℝ) ^ (degree stretch - 1) := by simp
      _ = (n + 1 : ℝ) ^ (1 + (degree stretch - 1)) := (Real.rpow_add (by positivity) _ _).symm
      _ = _ := by congr 1; ring
  have hscaled : size * (n + 1 : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + 1) ^ power ≤
      adjustedSize power stretch size * (n + 1 : ℝ) ^ degree stretch := by
    apply hlog.trans
    rw [adjustedSize, ← hpower]
    ring_nf
    exact le_rfl
  have hl : (1 : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) := Nat.cast_nonneg _
    linarith
  exact hscaled.trans ((le_mul_of_one_le_right (by unfold adjustedSize; positivity) hl).trans hbound)

theorem floor_capacity (power : ℕ) {stretch size : ℝ}
    (hstretch : 1 < stretch) (hsize : 0 ≤ size) (n count : ℕ)
    (bounded : (count : ℝ) ≤ size * (n + 1 : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + 1) ^ power) :
    count ≤ ⌊(length power stretch size n : ℝ) ^ stretch⌋₊ :=
  Nat.le_floor (bounded.trans (capacity power hstretch hsize n))

theorem sublinear (power : ℕ) {stretch size : ℝ} (hstretch : 1 < stretch) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∀ n : ℕ,
      (length power stretch size n : ℝ) ≤
        (SeedBudget.coefficient (degree stretch) stretch (adjustedSize power stretch size) + 1) *
          (n + 1 : ℝ) ^ alpha := by
  have hb := degree_bounds hstretch
  exact ⟨SeedBudget.seedExponent (degree stretch) stretch,
    (SeedBudget.exponent_bounds (by linarith) hb.2).1,
    (SeedBudget.exponent_bounds (by linarith) hb.2).2,
    SeedBudget.seed_power_bound (by linarith) hb.2⟩

theorem inverse_bound (power : ℕ) {stretch size : ℝ} (hstretch : 1 < stretch) :
    ∃ exponent : ℕ, 1 ≤ exponent ∧ ∀ n : ℕ, n + 1 ≤ length power stretch size n ^ exponent :=
  SeedBudget.seed_inverse_bound (by have h := (degree_bounds hstretch).1; linarith)
    (degree_bounds hstretch).2

end PolylogSeedBudget
