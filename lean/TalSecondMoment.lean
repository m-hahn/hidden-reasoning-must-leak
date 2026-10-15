import TalRandomRestriction

/-!
# A self-contained second-moment transfer bound

The finite weighted Cauchy--Schwarz argument avoids importing a binomial
median theorem. The probability bound below is proved for the actual
independent restriction distribution defined in `TalRandomRestriction`.
-/

open scoped BigOperators
noncomputable section
namespace TalSecondMoment
open TransformerAC0 TalRandomRestriction

def indicator {n : ℕ} (event : Restriction n → Prop) (rho : Restriction n) : ℝ := by
  classical
  exact if event rho then 1 else 0

/-- Cauchy--Schwarz for a conditional expectation under the restriction law. -/
theorem conditional_cauchy {n : ℕ} {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (value : Restriction n → ℝ) (event : Restriction n → Prop) :
    expectation p (fun rho => indicator event rho * value rho) ^ 2 ≤
      probability p event * expectation p (fun rho => value rho ^ 2) := by
  classical
  let a := fun rho : Restriction n => Real.sqrt (mass p rho) * indicator event rho
  let b := fun rho : Restriction n => Real.sqrt (mass p rho) * value rho
  have hroot (rho : Restriction n) : Real.sqrt (mass p rho) ^ 2 = mass p rho :=
    Real.sq_sqrt (mass_nonneg hzero hone rho)
  have hproduct : (∑ rho, a rho * b rho) =
      expectation p (fun rho => indicator event rho * value rho) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro rho _
    dsimp [a, b]
    calc
      _ = Real.sqrt (mass p rho) ^ 2 * (indicator event rho * value rho) := by ring
      _ = _ := by rw [hroot]
  have ha : (∑ rho, a rho ^ 2) = probability p event := by
    unfold probability expectation
    apply Finset.sum_congr rfl
    intro rho _
    by_cases h : event rho <;> simp [a, indicator, h, mul_pow, hroot]
  have hb : (∑ rho, b rho ^ 2) = expectation p (fun rho => value rho ^ 2) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro rho _
    simp only [b, mul_pow, hroot]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rwa [hproduct, ha, hb] at h

/-- A positive-mean random variable with second moment at most twice the
squared mean exceeds half its mean with probability at least `1/8`. -/
theorem probability_ge_half_mean {n : ℕ} {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (value : Restriction n → ℝ)
    (hmean : 0 < expectation p value)
    (hsecond : expectation p (fun rho => value rho ^ 2) ≤ 2 * expectation p value ^ 2) :
    (1 / 8 : ℝ) ≤ probability p (fun rho => expectation p value / 2 ≤ value rho) := by
  classical
  let mu := expectation p value
  let event := fun rho => mu / 2 ≤ value rho
  let complement := fun rho => ¬event rho
  have hsplit : mu = expectation p (fun rho => indicator event rho * value rho) +
      expectation p (fun rho => indicator complement rho * value rho) := by
    have hpoint : value = fun rho => indicator event rho * value rho +
        indicator complement rho * value rho := by
      funext rho
      by_cases h : event rho <;> simp [indicator, complement, h]
    change expectation p value = _
    conv_lhs => rw [hpoint]
    unfold expectation
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
  have hcomplement : expectation p (fun rho => indicator complement rho * value rho) ≤ mu / 2 := by
    calc
      _ ≤ expectation p (fun _ : Restriction n => mu / 2) := by
        apply expectation_mono hzero hone
        intro rho
        by_cases h : event rho
        · simp only [indicator, complement, h, not_true_eq_false, if_false, zero_mul]
          exact (div_pos hmean (by norm_num)).le
        · have hlt : value rho < mu / 2 := lt_of_not_ge h
          simp only [indicator, complement, h, not_false_eq_true, if_true, one_mul]
          exact hlt.le
      _ = _ := expectation_const n p _
  have hconditional : mu / 2 ≤ expectation p (fun rho => indicator event rho * value rho) := by
    linarith
  have hcauchy := conditional_cauchy hzero hone value event
  have hprob := probability_nonneg hzero hone event
  have hupper := mul_le_mul_of_nonneg_left hsecond hprob
  have hmu : 0 < mu := hmean
  change (1 / 8 : ℝ) ≤ probability p event
  apply (mul_le_mul_right (show 0 < mu ^ 2 by positivity)).mp
  nlinarith

def aliveIndicator {n : ℕ} (i : Fin n) (rho : Restriction n) : ℝ :=
  if rho i = none then 1 else 0

def aliveCount {n : ℕ} (U : Finset (Fin n)) (rho : Restriction n) : ℝ :=
  (aliveSet U rho).card

theorem character_self_as_alive_product {n : ℕ} (U : Finset (Fin n)) (rho : Restriction n) :
    characterCoefficient U U rho = ∏ i ∈ U, aliveIndicator i rho := by
  classical
  unfold characterCoefficient
  have hterm (i : Fin n) : localCoefficient (decide (i ∈ U)) (decide (i ∈ U)) (rho i) =
      if i ∈ U then aliveIndicator i rho else 1 := by
    by_cases hi : i ∈ U <;> cases h : rho i <;>
      simp [localCoefficient, aliveIndicator, hi, h, Option.some_ne_none]
  simp_rw [hterm]
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp

theorem expectation_alive_product {n : ℕ} (p : ℝ) (U : Finset (Fin n)) :
    expectation p (fun rho => ∏ i ∈ U, aliveIndicator i rho) = p ^ U.card := by
  have h := character_first_moment p U U
  simp only [if_true] at h
  have hpoint : characterCoefficient U U = fun rho => ∏ i ∈ U, aliveIndicator i rho := by
    funext rho
    exact character_self_as_alive_product U rho
  rwa [hpoint] at h

theorem expectation_aliveIndicator {n : ℕ} (p : ℝ) (i : Fin n) :
    expectation p (aliveIndicator i) = p := by
  simpa only [Finset.prod_singleton, Finset.card_singleton, pow_one] using
    expectation_alive_product p {i}

theorem expectation_aliveIndicator_pair {n : ℕ} (p : ℝ) (i j : Fin n) :
    expectation p (fun rho => aliveIndicator i rho * aliveIndicator j rho) =
      if i = j then p else p ^ 2 := by
  classical
  by_cases hij : i = j
  · subst j
    have hpoint : (fun rho : Restriction n => aliveIndicator i rho * aliveIndicator i rho) =
        aliveIndicator i := by
      funext rho
      unfold aliveIndicator
      split_ifs <;> norm_num
    rw [hpoint, expectation_aliveIndicator, if_pos rfl]
  · have h := expectation_alive_product p ({i, j} : Finset (Fin n))
    simpa [hij] using h

theorem expectation_finset_sum {n : ℕ} {I : Type*} (p : ℝ) (indices : Finset I)
    (values : I → Restriction n → ℝ) :
    expectation p (fun rho => ∑ index ∈ indices, values index rho) =
      ∑ index ∈ indices, expectation p (values index) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem aliveCount_eq_sum {n : ℕ} (U : Finset (Fin n)) (rho : Restriction n) :
    aliveCount U rho = ∑ i ∈ U, aliveIndicator i rho := by
  unfold aliveCount aliveSet aliveIndicator
  rw [Finset.natCast_card_filter]

theorem expectation_aliveCount {n : ℕ} (p : ℝ) (U : Finset (Fin n)) :
    expectation p (aliveCount U) = U.card * p := by
  have hpoint : aliveCount U = fun rho => ∑ i ∈ U, aliveIndicator i rho := by
    funext rho
    exact aliveCount_eq_sum U rho
  rw [hpoint, expectation_finset_sum]
  simp [expectation_aliveIndicator, nsmul_eq_mul]

/-- The exact second moment of the number of surviving coordinates. -/
theorem second_moment_aliveCount {n : ℕ} (p : ℝ) (U : Finset (Fin n)) :
    expectation p (fun rho => aliveCount U rho ^ 2) =
      (U.card : ℝ) * p + (U.card : ℝ) * ((U.card : ℝ) - 1) * p ^ 2 := by
  classical
  have hpoint : (fun rho : Restriction n => aliveCount U rho ^ 2) =
      fun rho => ∑ i ∈ U, ∑ j ∈ U, aliveIndicator i rho * aliveIndicator j rho := by
    funext rho
    rw [aliveCount_eq_sum, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hpoint, expectation_finset_sum]
  simp_rw [expectation_finset_sum, expectation_aliveIndicator_pair]
  have hrow (i : Fin n) (hi : i ∈ U) :
      (∑ j ∈ U, if i = j then p else p ^ 2) = p + ((U.card : ℝ) - 1) * p ^ 2 := by
    rw [← Finset.sum_erase_add _ _ hi]
    have hterm : (∑ j ∈ U.erase i, if i = j then p else p ^ 2) =
        ∑ _j ∈ U.erase i, p ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj).symm]
    rw [hterm]
    simp only [if_pos rfl, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hi]
    rw [Nat.cast_sub (Finset.one_le_card.mpr ⟨i, hi⟩)]
    norm_num
    ring
  calc
    _ = ∑ _i ∈ U, (p + ((U.card : ℝ) - 1) * p ^ 2) := by
      apply Finset.sum_congr rfl
      exact fun i hi => hrow i hi
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem second_moment_aliveCount_le {n : ℕ} {p : ℝ}
    (U : Finset (Fin n)) :
    expectation p (fun rho => aliveCount U rho ^ 2) ≤
      expectation p (aliveCount U) ^ 2 + expectation p (aliveCount U) := by
  rw [second_moment_aliveCount, expectation_aliveCount]
  have hnonneg : 0 ≤ (U.card : ℝ) * p ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  nlinarith

theorem probability_aliveCount_ge_half_mean {n : ℕ} {p : ℝ}
    (hzero : 0 ≤ p) (hone : p ≤ 1) (U : Finset (Fin n))
    (hmean : 1 ≤ (U.card : ℝ) * p) :
    (1 / 8 : ℝ) ≤ probability p (fun rho => ((U.card : ℝ) * p) / 2 ≤ aliveCount U rho) := by
  have hmean' : 1 ≤ expectation p (aliveCount U) := by rwa [expectation_aliveCount]
  have hsecond := second_moment_aliveCount_le (p := p) U
  have hbounded : expectation p (fun rho => aliveCount U rho ^ 2) ≤
      2 * expectation p (aliveCount U) ^ 2 := by nlinarith
  have h := probability_ge_half_mean hzero hone (aliveCount U) (by linarith) hbounded
  simpa only [expectation_aliveCount] using h

theorem probability_mono {n : ℕ} {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (event other : Restriction n → Prop) (himp : ∀ rho, event rho → other rho) :
    probability p event ≤ probability p other := by
  classical
  unfold probability
  apply expectation_mono hzero hone
  intro rho
  by_cases h : event rho
  · simp [h, himp rho h]
  · by_cases hother : other rho <;> simp [h, hother]

/-- A numerical binomial-tail lower bound, derived from the actual finite law. -/
theorem binomialTail_ge_eighth {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (trials threshold : ℕ) (hmean : 1 ≤ (trials : ℝ) * p)
    (hthreshold : (threshold : ℝ) ≤ (trials : ℝ) * p / 2) :
    (1 / 8 : ℝ) ≤ binomialTail p trials threshold := by
  have hhalf := probability_aliveCount_ge_half_mean hzero hone
    (Finset.univ : Finset (Fin trials)) (by simpa using hmean)
  have hmono := probability_mono hzero hone
    (fun rho : Restriction trials =>
      ((Finset.univ : Finset (Fin trials)).card : ℝ) * p / 2 ≤ aliveCount Finset.univ rho)
    (fun rho : Restriction trials => threshold ≤ (aliveSet Finset.univ rho).card)
    (by
      intro rho h
      have hreal : (threshold : ℝ) ≤ ((aliveSet Finset.univ rho).card : ℝ) := by
        dsimp [aliveCount] at h
        simp only [Finset.card_univ, Fintype.card_fin] at h
        exact hthreshold.trans h
      exact_mod_cast hreal)
  simpa only [probability_aliveSet_card, Finset.card_univ, Fintype.card_fin] using
    hhalf.trans hmono

/-- The uniform lower bound required by the Fourier transfer identity. -/
theorem binomialTail_floor_half_ge_eighth {p : ℝ}
    (hzero : 0 ≤ p) (hone : p ≤ 1) (degree trials : ℕ)
    (hmean : 1 ≤ (degree : ℝ) * p) (htrials : degree ≤ trials) :
    (1 / 8 : ℝ) ≤ binomialTail p trials ⌊(degree : ℝ) * p / 2⌋₊ := by
  have hcast : (degree : ℝ) ≤ trials := by exact_mod_cast htrials
  have hproduct := mul_le_mul_of_nonneg_right hcast hzero
  apply binomialTail_ge_eighth hzero hone trials _ (hmean.trans hproduct)
  exact (Nat.floor_le (by positivity : 0 ≤ (degree : ℝ) * p / 2)).trans
    (div_le_div_of_nonneg_right hproduct (by norm_num))

/-- A fully proved replacement for the median-based transfer lemma.

The factor is eight instead of two. The numerical normalization for retaining
`216^depth` is checked separately in `TalBroadNumerics`; the complete circuit
induction is proved in `TalNetworkFourier`.
-/
theorem tailWeight_le_eight_expectation {n : ℕ} {p : ℝ}
    (hzero : 0 ≤ p) (hone : p ≤ 1) (f : Bits n → ℝ) (degree : ℕ)
    (hmean : 1 ≤ (degree : ℝ) * p) :
    Tal.tailWeight f degree ≤ 8 * expectation p
      (fun rho => Tal.tailWeight (restrict f rho) ⌊(degree : ℝ) * p / 2⌋₊) := by
  have h := tailWeight_le_expectation_of_binomial_bound hzero hone f degree
    ⌊(degree : ℝ) * p / 2⌋₊
    (fun trials htrials => binomialTail_floor_half_ge_eighth
      hzero hone degree trials hmean htrials)
  linarith

end TalSecondMoment
