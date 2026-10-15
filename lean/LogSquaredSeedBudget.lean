import SeedBudget

/-!
# Sublinear seeds for near-linear log-squared reasoning

Every stretch exponent greater than one suffices. The logarithmic overhead
is absorbed by a strictly positive exponent margin, without replacing the
source time by a quadratic bound or requiring stretch greater than two.
-/

noncomputable section
namespace LogSquaredSeedBudget

def degree (stretch : ℝ) := (1 + stretch) / 2
def delta (stretch : ℝ) := (degree stretch - 1) / 2
def adjustedSize (stretch size : ℝ) := size * SeedBudget.logCoefficient (delta stretch) ^ 2
def length (stretch size : ℝ) := SeedBudget.length (degree stretch) stretch (adjustedSize stretch size)

theorem degree_bounds {stretch : ℝ} (h : 1 < stretch) : 1 < degree stretch ∧ degree stretch < stretch := by
  unfold degree
  constructor <;> linarith

theorem log_squared_bound {stretch : ℝ} (h : 1 < stretch) (n : ℕ) :
    ((Nat.log 2 (n + 1) : ℝ) + 1) ^ 2 ≤
      SeedBudget.logCoefficient (delta stretch) ^ 2 * (n + 1 : ℝ) ^ (degree stretch - 1) := by
  have hd : 0 < delta stretch := by unfold delta; have hb := (degree_bounds h).1; linarith
  have hlog := SeedBudget.logarithm_bound hd n
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) + 1) hlog 2
  have hpower : ((n + 1 : ℝ) ^ delta stretch) ^ 2 = (n + 1 : ℝ) ^ (degree stretch - 1) := by
    calc
      _ = ((n + 1 : ℝ) ^ delta stretch) ^ (2 : ℝ) := by simp
      _ = (n + 1 : ℝ) ^ (delta stretch * 2) := (Real.rpow_mul (by positivity) _ _).symm
      _ = _ := by congr 1; unfold delta; ring
  simpa only [mul_pow, hpower] using hs

theorem capacity {stretch size : ℝ} (hstretch : 1 < stretch) (hsize : 0 ≤ size) (n : ℕ) :
    size * (n + 1 : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + 1) ^ 2 ≤ (length stretch size n : ℝ) ^ stretch := by
  have hb := degree_bounds hstretch
  have hbound := SeedBudget.stretch_capacity hb.1.le hb.2
    (show 0 ≤ adjustedSize stretch size by unfold adjustedSize; positivity) n
  have hlog := mul_le_mul_of_nonneg_left (log_squared_bound hstretch n)
    (show 0 ≤ size * (n + 1 : ℝ) by positivity)
  have hpower : (n + 1 : ℝ) * (n + 1 : ℝ) ^ (degree stretch - 1) = (n + 1 : ℝ) ^ degree stretch := by
    calc
      _ = (n + 1 : ℝ) ^ (1 : ℝ) * (n + 1 : ℝ) ^ (degree stretch - 1) := by simp
      _ = (n + 1 : ℝ) ^ (1 + (degree stretch - 1)) := (Real.rpow_add (by positivity) _ _).symm
      _ = _ := by congr 1; ring
  have hscaled : size * (n + 1 : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + 1) ^ 2 ≤
      adjustedSize stretch size * (n + 1 : ℝ) ^ degree stretch := by
    apply hlog.trans
    rw [adjustedSize, ← hpower]
    ring_nf
    exact le_rfl
  have hl : (1 : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) + 1 := by
    nlinarith [(Nat.cast_nonneg (Nat.log 2 (n + 1)) : (0 : ℝ) ≤ Nat.log 2 (n + 1))]
  exact hscaled.trans ((le_mul_of_one_le_right (by unfold adjustedSize; positivity) hl).trans hbound)

theorem floor_capacity {stretch size : ℝ} (hstretch : 1 < stretch) (hsize : 0 ≤ size)
    (n count : ℕ) (bounded : (count : ℝ) ≤ size * (n + 1 : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + 1) ^ 2) :
    count ≤ ⌊(length stretch size n : ℝ) ^ stretch⌋₊ :=
  Nat.le_floor (bounded.trans (capacity hstretch hsize n))

theorem sublinear {stretch size : ℝ} (hstretch : 1 < stretch) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∀ n : ℕ,
      (length stretch size n : ℝ) ≤
        (SeedBudget.coefficient (degree stretch) stretch (adjustedSize stretch size) + 1) * (n + 1 : ℝ) ^ alpha := by
  have hb := degree_bounds hstretch
  exact ⟨SeedBudget.seedExponent (degree stretch) stretch,
    (SeedBudget.exponent_bounds (by linarith) hb.2).1,
    (SeedBudget.exponent_bounds (by linarith) hb.2).2,
    SeedBudget.seed_power_bound (by linarith) hb.2⟩

theorem inverse_bound {stretch size : ℝ} (hstretch : 1 < stretch) :
    ∃ exponent : ℕ, 1 ≤ exponent ∧ ∀ n : ℕ, n + 1 ≤ length stretch size n ^ exponent :=
  SeedBudget.seed_inverse_bound (by have h := (degree_bounds hstretch).1; linarith) (degree_bounds hstretch).2

end LogSquaredSeedBudget
