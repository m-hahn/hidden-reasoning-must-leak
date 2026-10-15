import PolylogSourceUpper
import Mathlib.Data.Nat.Size

/-! A coarse log-squared envelope for the explicit classical multiplier
cost. This is arithmetic on the proved cost formula, not an assumed
arithmetic primitive or multiplication complexity theorem. -/

namespace SchonhageRuntime

def operandWidth (n : ℕ) : ℕ := max 1 n
def time (coefficient n : ℕ) : ℕ :=
  coefficient * (4 * operandWidth n + 1) * (Nat.size (4 * operandWidth n) + 1) *
    (3 * Nat.size (Nat.size (4 * operandWidth n)) + 1) + 2400 * operandWidth n + 50001
def boundCoefficient (coefficient : ℕ) : ℕ := 240 * coefficient + 52401

theorem operandWidth_bound (n : ℕ) : operandWidth n ≤ n + 1 := by
  unfold operandWidth
  omega

theorem size_le_self (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))

theorem size_bound (n : ℕ) : Nat.size (4 * operandWidth n) + 1 ≤
    4 * PolylogSourceUpper.logFactor n := by
  have hn := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 1)
  have hw := operandWidth_bound n
  have hpow : 4 * operandWidth n < 2 ^ (Nat.log 2 (n + 1) + 3) := by
    calc
      _ ≤ 4 * (n + 1) := Nat.mul_le_mul_left _ hw
      _ < 4 * 2 ^ (Nat.log 2 (n + 1) + 1) := Nat.mul_lt_mul_of_pos_left hn (by decide)
      _ = _ := by
        rw [show Nat.log 2 (n + 1) + 3 = (Nat.log 2 (n + 1) + 1) + 2 by omega, pow_add]
        ring
  have hs := Nat.size_le.mpr hpow
  unfold PolylogSourceUpper.logFactor
  omega

theorem time_bound (coefficient n : ℕ) : time coefficient n ≤
    boundCoefficient coefficient * (n + 1) * PolylogSourceUpper.logFactor n ^ 2 := by
  let L := PolylogSourceUpper.logFactor n
  have hL : 1 ≤ L := PolylogSourceUpper.logFactor_positive n
  have hw := operandWidth_bound n
  have hs := size_bound n
  have hss := size_le_self (Nat.size (4 * operandWidth n))
  have hfirst : 4 * operandWidth n + 1 ≤ 5 * (n + 1) := by omega
  have hsecond : Nat.size (4 * operandWidth n) + 1 ≤ 4 * L := hs
  have hthird : 3 * Nat.size (Nat.size (4 * operandWidth n)) + 1 ≤ 12 * L := by nlinarith
  have hproduct := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul_left coefficient hfirst) hsecond) hthird
  have hlinear : 2400 * operandWidth n + 50001 ≤ 52401 * (n + 1) * L ^ 2 := by
    have hL2 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ hL
    have hscale : n + 1 ≤ (n + 1) * L ^ 2 := by nlinarith
    nlinarith
  unfold time boundCoefficient
  change _ ≤ (240 * coefficient + 52401) * (n + 1) * L ^ 2
  nlinarith [show coefficient * (5 * (n + 1)) * (4 * L) * (12 * L) =
    240 * coefficient * (n + 1) * L ^ 2 by ring]

end SchonhageRuntime
