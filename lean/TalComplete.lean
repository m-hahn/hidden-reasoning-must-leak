import TalSharedCircuit
import TalNetworkFourier

/-!
# Tal's Fourier-tail theorem, proved locally

The proof compiles the original shared circuit, uses the unconditional ranked
network induction, and applies the checked `216^d` constant normalization.
No Tal, switching, encoder, normalization, raw-bound, or induction premise is
an argument of the result.
-/

noncomputable section
namespace TalComplete
open TransformerAC0 TalRestriction TalGateNetwork TalNetworkFourier

theorem fourierTailTheorem : Tal.FourierTailTheorem := by
  intro n circuit depth size degree hdepth hsize hsizePositive
  by_cases hzeroDepth : depth = 0
  · subst depth
    exact TalSignedCircuit.zero_depth_tailBound circuit size degree (Nat.eq_zero_of_le_zero hdepth)
  · have hdepthPositive : 1 ≤ depth := by omega
    letI : NeZero size := ⟨by omega⟩
    obtain ⟨model, reference, hranks, hcomputes⟩ := TalSharedCircuit.exists_model circuit depth size hdepth hsize
    have heval : (fun input => Tal.boolSign (reference.eval model.functions input)) = Tal.circuitSign circuit := by
      funext input
      rw [hcomputes]
      rfl
    have hraw := raw_tail_bound (depth - 1) model hranks reference degree
    rw [heval] at hraw
    have hprefactor : prefactor (depth - 1) ≤ (17 : ℝ) ^ depth := by
      have hpow : (17 : ℝ) ^ depth = 17 * 17 ^ (depth - 1) := by
        nth_rw 1 [show depth = (depth - 1) + 1 by omega]
        rw [pow_succ']
      rw [hpow]
      unfold prefactor
      exact mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 17) (pow_nonneg (by norm_num) _)
    have hdenominator : denominator (depth - 1) 1 size =
        20 * (72 : ℝ) ^ (depth - 1) * Real.logb 2 (2 * size : ℕ) ^ (depth - 1) := by
      unfold denominator scale
      rw [Nat.cast_one, mul_one, mul_pow]
      ring
    have hbound : Tal.tailWeight (Tal.circuitSign circuit) degree ≤ (17 : ℝ) ^ depth * (2 : ℝ) ^
        (-(degree : ℝ) / (20 * 72 ^ (depth - 1) * Real.logb 2 (2 * size : ℕ) ^ (depth - 1))) := by
      unfold rawBound at hraw
      rw [hdenominator] at hraw
      exact hraw.trans (mul_le_mul_of_nonneg_right hprefactor (Real.rpow_nonneg (by norm_num) _))
    exact TalBroadNumerics.raw_bound_to_tailBound depth size degree hdepthPositive hsizePositive
      (tailWeight_nonneg _ _) (tailWeight_le_one_of_sign (fun input => circuit.eval input 0) degree) hbound

end TalComplete
