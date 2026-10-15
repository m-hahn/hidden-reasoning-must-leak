import MultitapeMatrix

/-!
# Numerical simulation bounds for a fixed polylogarithmic source overhead

The source machine's actual local runtime is charged. The checked oblivious
compiler adds one logarithmic factor. This lemma makes no multiplication
algorithm or arithmetic-unit-cost assumption.
-/

noncomputable section
namespace PolylogSourceUpper
open TransformerAC0 ObliviousPhase

def logFactor (n : ℕ) : ℕ := Nat.log 2 (n + 1) + 1
def timeHorizon (time : ℕ) : ℕ := max 1 time
def logConstant (power coefficient : ℕ) : ℕ :=
  Nat.log 2 ((coefficient + 1) * 2 ^ power) + power + 3
def traceConstant (tapes power coefficient : ℕ) : ℕ :=
  (4 * (248 * tapes + 1)) * (coefficient + 1) * logConstant power coefficient

theorem logFactor_positive (n : ℕ) : 1 ≤ logFactor n := by unfold logFactor; omega

theorem source_polynomial (power coefficient n time : ℕ)
    (bounded : time ≤ coefficient * (n + 1) * logFactor n ^ power) :
    time ≤ (coefficient * 2 ^ power) * (n + 1) ^ (power + 1) := by
  have hl : logFactor n ≤ 2 * (n + 1) := by
    unfold logFactor
    have h := Nat.log_le_self 2 (n + 1)
    omega
  calc
    _ ≤ coefficient * (n + 1) * logFactor n ^ power := bounded
    _ ≤ coefficient * (n + 1) * (2 * (n + 1)) ^ power :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl power)
    _ = _ := by rw [Nat.mul_pow, pow_succ]; ring

theorem horizon_time_bound (power coefficient n time : ℕ)
    (bounded : time ≤ coefficient * (n + 1) * logFactor n ^ power) :
    timeHorizon time ≤ (coefficient + 1) * (n + 1) * logFactor n ^ power := by
  have hpow := Nat.one_le_pow power (logFactor n) (logFactor_positive n)
  have hp : 1 ≤ (n + 1) * logFactor n ^ power := by nlinarith
  unfold timeHorizon
  apply max_le <;> nlinarith

theorem log_time_bound (power coefficient n time : ℕ)
    (bounded : time ≤ (coefficient + 1) * (n + 1) * logFactor n ^ power) :
    Nat.log 2 time + 1 ≤ logConstant power coefficient * logFactor n := by
  have hpoly := source_polynomial power (coefficient + 1) n time bounded
  have hn : n + 1 ≤ 2 ^ logFactor n :=
    (Nat.lt_pow_succ_log_self (by decide) (n + 1)).le
  have hc : (coefficient + 1) * 2 ^ power ≤
      2 ^ (Nat.log 2 ((coefficient + 1) * 2 ^ power) + 1) :=
    (Nat.lt_pow_succ_log_self (by decide) _).le
  have hpow : time ≤
      2 ^ ((Nat.log 2 ((coefficient + 1) * 2 ^ power) + 1) + logFactor n * (power + 1)) := by
    calc
      _ ≤ ((coefficient + 1) * 2 ^ power) * (n + 1) ^ (power + 1) := hpoly
      _ ≤ 2 ^ (Nat.log 2 ((coefficient + 1) * 2 ^ power) + 1) *
          (2 ^ logFactor n) ^ (power + 1) := Nat.mul_le_mul hc (Nat.pow_le_pow_left hn _)
      _ = _ := by rw [← Nat.pow_mul, ← Nat.pow_add]
  have hl := Nat.log_mono_right (b := 2) hpow
  rw [Nat.log_pow (by decide)] at hl
  have hp := logFactor_positive n
  unfold logConstant
  nlinarith

theorem trace_bound {tapes : ℕ} {State Symbol : Type*}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (power coefficient n time : ℕ)
    (bounded : time ≤ coefficient * (n + 1) * logFactor n ^ power) :
    MultitapeMatrix.eventSteps machine anchor (horizonLevel (timeHorizon time)) ≤
      traceConstant tapes power coefficient * (n + 1) * logFactor n ^ (power + 1) := by
  have ht := horizon_time_bound power coefficient n time bounded
  have hl := log_time_bound power coefficient n (timeHorizon time) ht
  calc
    _ ≤ (4 * (248 * tapes + 1)) * timeHorizon time *
        (Nat.log 2 (timeHorizon time) + 1) :=
      MultitapeMatrix.transcript_count_bound machine anchor (timeHorizon time) (Nat.le_max_left _ _)
    _ ≤ (4 * (248 * tapes + 1)) * ((coefficient + 1) * (n + 1) * logFactor n ^ power) *
        (logConstant power coefficient * logFactor n) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hl
    _ = _ := by unfold traceConstant; rw [pow_succ]; ring

end PolylogSourceUpper
