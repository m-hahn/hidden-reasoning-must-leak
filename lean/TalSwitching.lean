import TalSecondMoment
import TalDecisionTree
import TalOptimizedNumerics
import Complexitylib

/-!
# Connecting checked switching bounds to the local Fourier transform

Both finite random-restriction distributions are identified pointwise. The
single-formula switching theorem therefore bounds the expected Fourier tail
of an actual restricted DNF or CNF, not an abstract spectral certificate.
-/

open scoped BigOperators ENNReal
noncomputable section
namespace TalSwitching
open TransformerAC0 TalRandomRestriction
open Algebraic AC0

theorem coordinateWeight_coe (p : NNReal) (hone : p ≤ 1) (value : Option Bool) :
    (RandomRestriction.coordinateWeight p value : ℝ) = coordinateMass (p : ℝ) value := by
  cases value with
  | none => rfl
  | some value =>
      simp only [RandomRestriction.coordinateWeight, RandomRestriction.fixedWeight,
        NNReal.coe_div, NNReal.coe_sub hone, NNReal.coe_one, NNReal.coe_ofNat,
        coordinateMass]

theorem weight_eq_ofReal_mass {n : ℕ} (p : NNReal) (hone : p ≤ 1) (rho : Restriction n) :
    RandomRestriction.weight p rho = ENNReal.ofReal (mass (p : ℝ) rho) := by
  unfold RandomRestriction.weight mass
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    coordinateMass_nonneg p.coe_nonneg (NNReal.coe_le_coe.mpr hone) (rho i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [← coordinateWeight_coe p hone]
  exact ENNReal.ofReal_coe_nnreal.symm

theorem ofReal_probability {n : ℕ} (p : NNReal) (hone : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    ENNReal.ofReal (probability (p : ℝ) event) =
      RandomRestriction.probability n p hone event := by
  classical
  unfold probability expectation RandomRestriction.probability
  rw [ENNReal.ofReal_sum_of_nonneg (by
    intro rho _
    exact mul_nonneg (mass_nonneg p.coe_nonneg (NNReal.coe_le_coe.mpr hone) rho)
      (by dsimp; split_ifs <;> norm_num))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases h : event rho
  · simp only [if_pos h, mul_one, RandomRestriction.distribution_apply]
    exact (weight_eq_ofReal_mass p hone rho).symm
  · simp [h]

theorem tailWeight_eq_zero_of_not_depthAtLeast {n : ℕ} (f : Bits n → Bool) (degree : ℕ)
    (hdepth : ¬DecisionTree.DepthAtLeast f degree) :
    Tal.tailWeight (fun input => Tal.boolSign (f input)) degree = 0 := by
  classical
  obtain ⟨tree, htree⟩ := not_forall.mp hdepth
  obtain ⟨hcomputes, hshallow⟩ := _root_.not_imp.mp htree
  exact TalDecisionTree.tailWeight_eq_zero_of_depthAtMost f tree.depth degree
    ⟨tree, hcomputes, le_rfl⟩ (lt_of_not_ge hshallow)

theorem expected_tailWeight_le_probability {n : ℕ} {p : ℝ}
    (hzero : 0 ≤ p) (hone : p ≤ 1) (f : Bits n → Bool) (degree : ℕ) :
    expectation p (fun rho => Tal.tailWeight
      (restrict (fun input => Tal.boolSign (f input)) rho) degree) ≤
      probability p (fun rho => DecisionTree.DepthAtLeast (ScalarFunction.restrict f rho) degree) := by
  classical
  unfold probability
  apply expectation_mono hzero hone
  intro rho
  have heval : restrict (fun input => Tal.boolSign (f input)) rho =
      fun input => Tal.boolSign ((ScalarFunction.restrict f rho) input) := rfl
  rw [heval]
  by_cases h : DecisionTree.DepthAtLeast (ScalarFunction.restrict f rho) degree
  · rw [if_pos h]
    exact TalRestriction.tailWeight_le_one_of_sign (ScalarFunction.restrict f rho) degree
  · rw [if_neg h, tailWeight_eq_zero_of_not_depthAtLeast _ degree h]

/-- The checked semantic switching bound in the local real-valued probability API. -/
theorem probability_dnf_depthAtLeast_le {n : ℕ} (formula : DNF n) (width degree : ℕ)
    (hwidth : formula.WidthAtMost width) (p : NNReal) (hone : p ≤ 1) :
    probability (p : ℝ) (fun rho => DecisionTree.DepthAtLeast
      (formula.restrict rho).eval degree) ≤ (5 * (p : ℝ) * width) ^ degree := by
  classical
  have hp : 0 ≤ (p : ℝ) := p.coe_nonneg
  have h := RandomRestriction.probability_depthAtLeast_restrict_le_five
    formula hwidth degree p hone
  rw [← ofReal_probability p hone] at h
  have hright : ((5 : ENNReal) * (p : ENNReal) * (width : ENNReal)) ^ degree =
      ENNReal.ofReal ((5 * (p : ℝ) * width) ^ degree) := by
    rw [ENNReal.ofReal_pow (mul_nonneg (mul_nonneg (by norm_num) hp) (Nat.cast_nonneg width)),
      ENNReal.ofReal_mul (mul_nonneg (by norm_num) hp),
      ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [hright] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

theorem expected_dnf_tailWeight_le {n : ℕ} (formula : DNF n) (width degree : ℕ)
    (hwidth : formula.WidthAtMost width) (p : NNReal) (hone : p ≤ 1) :
    expectation (p : ℝ) (fun rho => Tal.tailWeight
      (restrict (fun input => Tal.boolSign (formula.eval input)) rho) degree) ≤
      (5 * (p : ℝ) * width) ^ degree := by
  have h := expected_tailWeight_le_probability p.coe_nonneg (NNReal.coe_le_coe.mpr hone)
    formula.eval degree
  have hevent : (fun rho : Restriction n =>
      DecisionTree.DepthAtLeast (ScalarFunction.restrict formula.eval rho) degree) =
      fun rho => DecisionTree.DepthAtLeast (formula.restrict rho).eval degree := by
    funext rho
    have heval : ScalarFunction.restrict formula.eval rho = (formula.restrict rho).eval := by
      funext input
      exact (formula.restrict_sound rho input).symm
    rw [heval]
  rw [hevent] at h
  exact h.trans (probability_dnf_depthAtLeast_le formula width degree hwidth p hone)

theorem probability_cnf_depthAtLeast_le {n : ℕ} (formula : CNF n) (width degree : ℕ)
    (hwidth : formula.WidthAtMost width) (p : NNReal) (hone : p ≤ 1) :
    probability (p : ℝ) (fun rho => DecisionTree.DepthAtLeast
      (formula.restrict rho).eval degree) ≤ (5 * (p : ℝ) * width) ^ degree := by
  classical
  have hp : 0 ≤ (p : ℝ) := p.coe_nonneg
  have h := RandomRestriction.probability_cnf_depthAtLeast_restrict_le_five
    formula hwidth degree p hone
  rw [← ofReal_probability p hone] at h
  have hright : ((5 : ENNReal) * (p : ENNReal) * (width : ENNReal)) ^ degree =
      ENNReal.ofReal ((5 * (p : ℝ) * width) ^ degree) := by
    rw [ENNReal.ofReal_pow (mul_nonneg (mul_nonneg (by norm_num) hp) (Nat.cast_nonneg width)),
      ENNReal.ofReal_mul (mul_nonneg (by norm_num) hp),
      ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [hright] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

theorem expected_cnf_tailWeight_le {n : ℕ} (formula : CNF n) (width degree : ℕ)
    (hwidth : formula.WidthAtMost width) (p : NNReal) (hone : p ≤ 1) :
    expectation (p : ℝ) (fun rho => Tal.tailWeight
      (restrict (fun input => Tal.boolSign (formula.eval input)) rho) degree) ≤
      (5 * (p : ℝ) * width) ^ degree := by
  have h := expected_tailWeight_le_probability p.coe_nonneg (NNReal.coe_le_coe.mpr hone)
    formula.eval degree
  have hevent : (fun rho : Restriction n =>
      DecisionTree.DepthAtLeast (ScalarFunction.restrict formula.eval rho) degree) =
      fun rho => DecisionTree.DepthAtLeast (formula.restrict rho).eval degree := by
    funext rho
    have heval : ScalarFunction.restrict formula.eval rho = (formula.restrict rho).eval := by
      funext input
      exact (formula.restrict_sound rho input).symm
    rw [heval]
  rw [hevent] at h
  exact h.trans (probability_cnf_depthAtLeast_le formula width degree hwidth p hone)

/-- A numerical/spectral helper for the already-proved single-switching estimate. -/
theorem tailWeight_le_of_expected_switching {n : ℕ} (f : Bits n → Bool)
    (width degree : ℕ) (hwidth : 0 < width)
    (hexpect : ∀ (p : NNReal) (_hone : p ≤ 1) (threshold : ℕ),
      expectation (p : ℝ) (fun rho => Tal.tailWeight
        (restrict (fun input => Tal.boolSign (f input)) rho) threshold) ≤
        (5 * (p : ℝ) * width) ^ threshold) :
    Tal.tailWeight (fun input => Tal.boolSign (f input)) degree ≤
      16 * (2 : ℝ) ^ (-(degree : ℝ) / (20 * width)) := by
  let p : NNReal := 1 / (10 * width)
  have hw : (0 : ℝ) < width := by exact_mod_cast hwidth
  have hwone : (1 : ℝ) ≤ width := by exact_mod_cast hwidth
  have hpr : (p : ℝ) = 1 / (10 * (width : ℝ)) := by simp [p]
  have hpone : p ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    rw [hpr]
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num only [NNReal.coe_one, one_mul]
    linarith
  have hone : (p : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hpone
  have hratio : (degree : ℝ) * (p : ℝ) / 2 = (degree : ℝ) / (20 * width) := by
    rw [hpr]
    ring
  have hbase : 5 * (p : ℝ) * width = (1 / 2 : ℝ) := by
    rw [hpr]
    field_simp
    ring
  by_cases hmean : 1 ≤ (degree : ℝ) * (p : ℝ)
  · have htransfer := TalSecondMoment.tailWeight_le_eight_expectation
      p.coe_nonneg hone (fun input => Tal.boolSign (f input)) degree hmean
    have hswitch := hexpect p hpone ⌊(degree : ℝ) * (p : ℝ) / 2⌋₊
    rw [hbase] at hswitch
    have hcombined := htransfer.trans (mul_le_mul_of_nonneg_left hswitch (by norm_num))
    rw [hratio] at hcombined
    exact hcombined.trans (by
      simpa only [neg_div] using TalOptimizedNumerics.eight_half_pow_floor_le
        ((degree : ℝ) / (20 * width)))
  · have hsmall : (degree : ℝ) / (20 * width) ≤ 1 := by
      rw [← hratio]
      linarith [lt_of_not_ge hmean]
    calc
      _ ≤ 1 := TalRestriction.tailWeight_le_one_of_sign f degree
      _ ≤ 16 * (2 : ℝ) ^ (-1 : ℝ) := by norm_num [Real.rpow_neg_one]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [neg_div]; linarith)

/-- The width-bounded DNF Fourier-tail base case, with no Tal premise. -/
theorem dnf_tailWeight_le {n : ℕ} (formula : DNF n) (width degree : ℕ)
    (hwidth : formula.WidthAtMost width) (hpositive : 0 < width) :
    Tal.tailWeight (fun input => Tal.boolSign (formula.eval input)) degree ≤
      16 * (2 : ℝ) ^ (-(degree : ℝ) / (20 * width)) := by
  apply tailWeight_le_of_expected_switching formula.eval width degree hpositive
  exact fun p hone threshold => expected_dnf_tailWeight_le formula width threshold hwidth p hone

/-- The dual CNF base case has the identical quantitative bound. -/
theorem cnf_tailWeight_le {n : ℕ} (formula : CNF n) (width degree : ℕ)
    (hwidth : formula.WidthAtMost width) (hpositive : 0 < width) :
    Tal.tailWeight (fun input => Tal.boolSign (formula.eval input)) degree ≤
      16 * (2 : ℝ) ^ (-(degree : ℝ) / (20 * width)) := by
  apply tailWeight_le_of_expected_switching formula.eval width degree hpositive
  exact fun p hone threshold => expected_cnf_tailWeight_le formula width threshold hwidth p hone

end TalSwitching
