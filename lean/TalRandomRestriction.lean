import TalRestriction

/-!
# Independent random restrictions and Fourier coefficients

Finite product-distribution semantics for Tal's random restrictions. Each
coordinate is left alive with probability `p`, otherwise it is fixed to a
uniform Boolean bit. Fourier analysis retains the original dimension; a
fixed coordinate simply becomes irrelevant to the restricted function.
-/

open scoped BigOperators
noncomputable section
namespace TalRandomRestriction
open TransformerAC0

abbrev Restriction (n : ℕ) := Fin n → Option Bool

def applyRestriction {n : ℕ} (rho : Restriction n) (input : Bits n) : Bits n :=
  fun i => (rho i).getD (input i)

def restrict {n : ℕ} (f : Bits n → ℝ) (rho : Restriction n) : Bits n → ℝ :=
  fun input => f (applyRestriction rho input)

def coordinateMass (p : ℝ) : Option Bool → ℝ
  | none => p
  | some _ => (1 - p) / 2

def mass {n : ℕ} (p : ℝ) (rho : Restriction n) : ℝ :=
  ∏ i, coordinateMass p (rho i)

def expectation {n : ℕ} (p : ℝ) (value : Restriction n → ℝ) : ℝ :=
  ∑ rho, mass p rho * value rho

def probability {n : ℕ} (p : ℝ) (event : Restriction n → Prop) : ℝ :=
  by classical exact expectation p fun rho => if event rho then 1 else 0

theorem coordinateMass_nonneg {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (value : Option Bool) : 0 ≤ coordinateMass p value := by
  cases value <;> dsimp [coordinateMass] <;> linarith

theorem mass_nonneg {n : ℕ} {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (rho : Restriction n) : 0 ≤ mass p rho :=
  Finset.prod_nonneg fun i _ => coordinateMass_nonneg hzero hone (rho i)

theorem expectation_nonneg {n : ℕ} {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (value : Restriction n → ℝ) (hvalue : ∀ rho, 0 ≤ value rho) :
    0 ≤ expectation p value :=
  Finset.sum_nonneg fun rho _ => mul_nonneg (mass_nonneg hzero hone rho) (hvalue rho)

theorem expectation_mono {n : ℕ} {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (f g : Restriction n → ℝ) (hfg : ∀ rho, f rho ≤ g rho) :
    expectation p f ≤ expectation p g :=
  Finset.sum_le_sum fun rho _ => mul_le_mul_of_nonneg_left (hfg rho) (mass_nonneg hzero hone rho)

@[simp] theorem sum_coordinateMass (p : ℝ) :
    (∑ value : Option Bool, coordinateMass p value) = 1 := by
  rw [Fintype.sum_option, Fintype.sum_bool]
  simp only [coordinateMass]
  ring

@[simp] theorem sum_mass (n : ℕ) (p : ℝ) :
    (∑ rho : Restriction n, mass p rho) = 1 := by
  unfold mass
  rw [← Fintype.prod_sum]
  simp only [sum_coordinateMass, Finset.prod_const_one]

/-- Product expectations factor into the individual coordinate expectations. -/
theorem expectation_prod {n : ℕ} (p : ℝ) (g : Fin n → Option Bool → ℝ) :
    expectation p (fun rho => ∏ i, g i (rho i)) =
      ∏ i, ∑ value : Option Bool, coordinateMass p value * g i value := by
  unfold expectation mass
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i value => coordinateMass p value * g i value)).symm

/-- The uniform Boolean cube is itself a product distribution. -/
theorem uniformExpectation_prod {n : ℕ} (g : Fin n → Bool → ℝ) :
    Tal.uniformExpectation (fun input => ∏ i, g i (input i)) =
      ∏ i, (g i false + g i true) / 2 := by
  unfold Tal.uniformExpectation
  rw [← Fintype.prod_sum]
  simp_rw [Fintype.sum_bool]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_cast
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact add_comm _ _

/-- Local contribution to a restricted Walsh character coefficient. -/
def localCoefficient (inOriginal inCoefficient : Bool) : Option Bool → ℝ
  | none => if inOriginal = inCoefficient then 1 else 0
  | some value => if inCoefficient then 0 else if inOriginal then Tal.boolSign value else 1

def characterCoefficient {n : ℕ} (U S : Finset (Fin n)) (rho : Restriction n) : ℝ :=
  ∏ i, localCoefficient (decide (i ∈ U)) (decide (i ∈ S)) (rho i)

theorem walsh_as_coordinate_product {n : ℕ} (U : Finset (Fin n)) (input : Bits n) :
    Tal.walshCharacter U input = ∏ i : Fin n, if i ∈ U then Tal.boolSign (input i) else 1 := by
  rw [Tal.walshCharacter, ← Finset.prod_filter]
  congr 1
  ext i
  simp

/-- Restricted-character Fourier coefficients have an explicit product formula. -/
theorem coefficient_restricted_character {n : ℕ} (U S : Finset (Fin n))
    (rho : Restriction n) :
    Tal.fourierCoefficient (restrict (Tal.walshCharacter U) rho) S =
      characterCoefficient U S rho := by
  unfold Tal.fourierCoefficient restrict
  simp_rw [walsh_as_coordinate_product]
  simp_rw [← Finset.prod_mul_distrib]
  unfold applyRestriction
  rw [uniformExpectation_prod (fun i value =>
    (if i ∈ U then Tal.boolSign ((rho i).getD value) else 1) *
      (if i ∈ S then Tal.boolSign value else 1))]
  unfold characterCoefficient
  apply Finset.prod_congr rfl
  intro i _
  cases h : rho i with
  | none =>
      by_cases hU : i ∈ U <;> by_cases hS : i ∈ S <;>
        norm_num [applyRestriction, h, hU, hS, localCoefficient]
  | some value =>
      cases value <;> by_cases hU : i ∈ U <;> by_cases hS : i ∈ S <;>
        norm_num [applyRestriction, h, hU, hS, localCoefficient]

/-- Linearity of normalized Fourier coefficients across a finite sum. -/
theorem coefficient_sum {n : ℕ} {I : Type*} [Fintype I]
    (a : I → ℝ) (functions : I → Bits n → ℝ) (S : Finset (Fin n)) :
    Tal.fourierCoefficient (fun input => ∑ index, a index * functions index input) S =
      ∑ index, a index * Tal.fourierCoefficient (functions index) S := by
  unfold Tal.fourierCoefficient Tal.uniformExpectation
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index _
  calc
    _ = (a index * ∑ input : Bits n,
        functions index input * Tal.walshCharacter S input) / (2 ^ n : ℕ) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _
      ring
    _ = _ := by ring

/-- Restricting the original Fourier expansion yields the restricted coefficients. -/
theorem coefficient_restrict {n : ℕ} (f : Bits n → ℝ) (rho : Restriction n)
    (S : Finset (Fin n)) :
    Tal.fourierCoefficient (restrict f rho) S =
      ∑ U : Finset (Fin n), Tal.fourierCoefficient f U * characterCoefficient U S rho := by
  have hexpand : restrict f rho = fun input =>
      ∑ U : Finset (Fin n), Tal.fourierCoefficient f U *
        restrict (Tal.walshCharacter U) rho input := by
    funext input
    exact (FourierCorrelation.fourier_inversion f (applyRestriction rho input)).symm
  rw [hexpand, coefficient_sum]
  simp_rw [coefficient_restricted_character]

/-- Cross-moments vanish at every coordinate on which `U` and `V` differ. -/
theorem local_cross_moment_zero (p : ℝ) (inU inV inS : Bool) (hne : inU ≠ inV) :
    (∑ value : Option Bool, coordinateMass p value *
      (localCoefficient inU inS value * localCoefficient inV inS value)) = 0 := by
  rw [Fintype.sum_option, Fintype.sum_bool]
  cases inU <;> cases inV <;> cases inS <;>
    simp_all [coordinateMass, localCoefficient, Tal.boolSign]

/-- Distinct original Walsh characters have zero restricted-coefficient cross-moment. -/
theorem character_cross_moment_zero {n : ℕ} (p : ℝ) (U V S : Finset (Fin n))
    (hne : U ≠ V) :
    expectation p (fun rho => characterCoefficient U S rho * characterCoefficient V S rho) = 0 := by
  unfold characterCoefficient
  simp_rw [← Finset.prod_mul_distrib]
  rw [expectation_prod p (fun i value =>
    localCoefficient (decide (i ∈ U)) (decide (i ∈ S)) value *
      localCoefficient (decide (i ∈ V)) (decide (i ∈ S)) value)]
  have hdifferent : ∃ i : Fin n, decide (i ∈ U) ≠ decide (i ∈ V) := by
    by_contra! hsame
    apply hne
    ext i
    have h := hsame i
    by_cases hU : i ∈ U <;> by_cases hV : i ∈ V <;> simp_all
  obtain ⟨i, hi⟩ := hdifferent
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact local_cross_moment_zero p _ _ _ hi

/-- Original character coordinates which remain alive after restriction. -/
def aliveSet {n : ℕ} (U : Finset (Fin n)) (rho : Restriction n) : Finset (Fin n) :=
  U.filter fun i => rho i = none

/-- A restricted-character coefficient has unit squared magnitude precisely on its alive set. -/
theorem characterCoefficient_sq {n : ℕ} (U S : Finset (Fin n)) (rho : Restriction n) :
    characterCoefficient U S rho ^ 2 = if aliveSet U rho = S then 1 else 0 := by
  unfold characterCoefficient
  rw [← Finset.prod_pow]
  have hlocal : ∀ i : Fin n,
      localCoefficient (decide (i ∈ U)) (decide (i ∈ S)) (rho i) ^ 2 =
        if (i ∈ aliveSet U rho ↔ i ∈ S) then 1 else 0 := by
    intro i
    cases h : rho i with
    | none =>
        by_cases hU : i ∈ U <;> by_cases hS : i ∈ S <;>
          norm_num [localCoefficient, aliveSet, h, hU, hS]
    | some value =>
        cases value <;> by_cases hU : i ∈ U <;> by_cases hS : i ∈ S <;>
          norm_num [localCoefficient, aliveSet, h, hU, hS] <;>
            simp [Option.some_ne_none]
  simp_rw [hlocal]
  by_cases heq : aliveSet U rho = S
  · simp [heq]
  · rw [if_neg heq]
    have hdifferent : ∃ i : Fin n, ¬(i ∈ aliveSet U rho ↔ i ∈ S) := by
      exact not_forall.mp (fun hsame => heq (Finset.ext hsame))
    obtain ⟨i, hi⟩ := hdifferent
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [if_neg hi]

theorem expectation_sum {n : ℕ} {I : Type*} [Fintype I]
    (p : ℝ) (functions : I → Restriction n → ℝ) :
    expectation p (fun rho => ∑ index, functions index rho) =
      ∑ index, expectation p (functions index) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expectation_const_mul {n : ℕ} (p a : ℝ) (value : Restriction n → ℝ) :
    expectation p (fun rho => a * value rho) = a * expectation p value := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _
  ring

@[simp] theorem expectation_zero (n : ℕ) (p : ℝ) :
    expectation p (fun _ : Restriction n => 0) = 0 := by simp [expectation]

@[simp] theorem expectation_const (n : ℕ) (p value : ℝ) :
    expectation p (fun _ : Restriction n => value) = value := by
  unfold expectation
  rw [← Finset.sum_mul, sum_mass, one_mul]

theorem probability_nonneg {n : ℕ} {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (event : Restriction n → Prop) : 0 ≤ probability p event := by
  classical
  apply expectation_nonneg hzero hone
  intro rho
  split_ifs <;> norm_num

theorem probability_le_one {n : ℕ} {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (event : Restriction n → Prop) : probability p event ≤ 1 := by
  classical
  calc
    probability p event ≤ expectation p (fun _ : Restriction n => 1) :=
      expectation_mono hzero hone _ _ (fun rho => by split_ifs <;> norm_num)
    _ = 1 := expectation_const n p 1

/-- Diagonal restricted-character moments are exactly the alive-set probabilities. -/
theorem character_diagonal_moment {n : ℕ} (p : ℝ) (U S : Finset (Fin n)) :
    expectation p (fun rho => characterCoefficient U S rho * characterCoefficient U S rho) =
      probability p (fun rho => aliveSet U rho = S) := by
  simp_rw [← pow_two, characterCoefficient_sq]
  unfold probability
  congr 1
  funext rho
  by_cases h : aliveSet U rho = S <;> simp [h]

/-- Tal's Fact 6: the second moment of each restricted Fourier coefficient.

This is an exact identity for the actual finite independent restriction
distribution, not a spectral proxy or an assumed transfer rule.
-/
theorem coefficient_second_moment {n : ℕ} (p : ℝ) (f : Bits n → ℝ)
    (S : Finset (Fin n)) :
    expectation p (fun rho => Tal.fourierCoefficient (restrict f rho) S ^ 2) =
      ∑ U : Finset (Fin n), Tal.fourierCoefficient f U ^ 2 *
        probability p (fun rho => aliveSet U rho = S) := by
  let a := Tal.fourierCoefficient f
  calc
    _ = expectation p (fun rho => ∑ U : Finset (Fin n), ∑ V : Finset (Fin n),
        (a U * a V) * (characterCoefficient U S rho * characterCoefficient V S rho)) := by
      congr 1
      funext rho
      rw [coefficient_restrict, pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      apply Finset.sum_congr rfl
      intro V _
      dsimp [a]
      ring
    _ = ∑ U : Finset (Fin n), ∑ V : Finset (Fin n),
        (a U * a V) * expectation p
          (fun rho => characterCoefficient U S rho * characterCoefficient V S rho) := by
      rw [expectation_sum]
      apply Finset.sum_congr rfl
      intro U _
      rw [expectation_sum]
      apply Finset.sum_congr rfl
      intro V _
      exact expectation_const_mul p _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro U _
      rw [Finset.sum_eq_single U]
      · rw [character_diagonal_moment]
        simp only [a, pow_two]
      · intro V _ hVU
        rw [character_cross_moment_zero p U V S hVU.symm, mul_zero]
      · simp

/-- Expected upper-tail weight is obtained by thinning every original spectral set. -/
theorem tailWeight_transfer {n : ℕ} (p : ℝ) (f : Bits n → ℝ) (k : ℕ) :
    expectation p (fun rho => Tal.tailWeight (restrict f rho) k) =
      ∑ U : Finset (Fin n), Tal.fourierCoefficient f U ^ 2 *
        probability p (fun rho => k ≤ (aliveSet U rho).card) := by
  classical
  unfold Tal.tailWeight
  rw [expectation_sum]
  have hterm : ∀ S : Finset (Fin n),
      expectation p (fun rho => if k ≤ S.card then
        Tal.fourierCoefficient (restrict f rho) S ^ 2 else 0) =
      ∑ U : Finset (Fin n), Tal.fourierCoefficient f U ^ 2 *
        (if k ≤ S.card then probability p (fun rho => aliveSet U rho = S) else 0) := by
    intro S
    by_cases hk : k ≤ S.card
    · simp only [if_pos hk]
      exact coefficient_second_moment p f S
    · simp [hk]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _
  rw [← Finset.mul_sum]
  congr 1
  unfold probability
  dsimp only
  have hexpect : (∑ S : Finset (Fin n),
      if k ≤ S.card then expectation p (fun rho => if aliveSet U rho = S then 1 else 0) else 0) =
      expectation p (fun rho => ∑ S : Finset (Fin n),
        if k ≤ S.card then (if aliveSet U rho = S then 1 else 0) else 0) := by
    rw [expectation_sum]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hk : k ≤ S.card <;> simp [hk]
  convert hexpect.trans ?_ using 1
  · apply Finset.sum_congr rfl
    intro S _
    by_cases hk : k ≤ S.card
    · simp only [if_pos hk]
      congr 1
      funext rho
      by_cases h : aliveSet U rho = S <;> simp [h]
    · simp [hk]
  · congr 1
    funext rho
    rw [Finset.sum_eq_single (aliveSet U rho)]
    · simp
    · intro S _ hS
      have hne : aliveSet U rho ≠ S := hS.symm
      simp [hne]
    · simp

/-- The exact diagonal coordinate moment. -/
theorem local_diagonal_moment (p : ℝ) (inU inS : Bool) :
    (∑ value : Option Bool, coordinateMass p value *
      (localCoefficient inU inS value * localCoefficient inU inS value)) =
      if inS then (if inU then p else 0) else (if inU then 1 - p else 1) := by
  rw [Fintype.sum_option, Fintype.sum_bool]
  cases inU <;> cases inS <;>
    simp [coordinateMass, localCoefficient, Tal.boolSign]

/-- Every alive subset has the exact independent Bernoulli probability. -/
theorem probability_aliveSet_eq {n : ℕ} (p : ℝ) (U S : Finset (Fin n)) :
    probability p (fun rho => aliveSet U rho = S) =
      if S ⊆ U then p ^ S.card * (1 - p) ^ (U.card - S.card) else 0 := by
  classical
  rw [← character_diagonal_moment]
  unfold characterCoefficient
  simp_rw [← Finset.prod_mul_distrib]
  rw [expectation_prod p (fun i value =>
    localCoefficient (decide (i ∈ U)) (decide (i ∈ S)) value *
      localCoefficient (decide (i ∈ U)) (decide (i ∈ S)) value)]
  simp_rw [local_diagonal_moment]
  by_cases hsubset : S ⊆ U
  · rw [if_pos hsubset]
    have hterm : ∀ i : Fin n,
        (if decide (i ∈ S) then (if decide (i ∈ U) then p else 0)
          else (if decide (i ∈ U) then 1 - p else 1)) =
        (if i ∈ S then p else 1) * (if i ∈ U \ S then 1 - p else 1) := by
      intro i
      by_cases hS : i ∈ S
      · have hU := hsubset hS
        simp [hS, hU]
      · by_cases hU : i ∈ U <;> simp [hS, hU]
    simp_rw [hterm]
    rw [Finset.prod_mul_distrib, ← Finset.prod_filter, ← Finset.prod_filter]
    have hfilter (T : Finset (Fin n)) : Finset.univ.filter (fun i => i ∈ T) = T := by
      ext i
      simp
    rw [hfilter, hfilter]
    simp only [Finset.prod_const, Finset.card_sdiff hsubset]
  · rw [if_neg hsubset]
    obtain ⟨i, hiS, hiU⟩ : ∃ i, i ∈ S ∧ i ∉ U := by
      have hnot : ¬∀ i : Fin n, i ∈ S → i ∈ U := hsubset
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      have hpair := _root_.not_imp.mp hi
      exact ⟨i, hpair.1, hpair.2⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hiS, hiU]

/-- The binomial mass associated with independently surviving coordinates. -/
def binomialMass (p : ℝ) (trials successes : ℕ) : ℝ :=
  (trials.choose successes : ℝ) * p ^ successes * (1 - p) ^ (trials - successes)

def binomialTail (p : ℝ) (trials threshold : ℕ) : ℝ :=
  ∑ successes ∈ Finset.range (trials + 1),
    if threshold ≤ successes then binomialMass p trials successes else 0

/-- Finite pushforward formula for any event on a finite-valued statistic. -/
theorem probability_pushforward {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℝ) (statistic : Restriction n → I) (event : I → Prop) [DecidablePred event] :
    probability p (fun rho => event (statistic rho)) =
      ∑ index : I, if event index then probability p (fun rho => statistic rho = index) else 0 := by
  classical
  unfold probability
  calc
    _ = expectation p (fun rho => ∑ index : I,
        if event index then (if statistic rho = index then 1 else 0) else 0) := by
      congr 1
      funext rho
      rw [Finset.sum_eq_single (statistic rho)]
      · simp
      · intro index _ hindex
        simp [hindex.symm]
      · simp
    _ = _ := by
      rw [expectation_sum]
      apply Finset.sum_congr rfl
      intro index _
      by_cases h : event index
      · simp only [if_pos h]
        congr 1
        funext rho
        by_cases hstat : statistic rho = index <;> simp [hstat]
      · simp [h]

/-- Surviving coordinates of each original spectral set have the binomial law. -/
theorem probability_aliveSet_card {n : ℕ} (p : ℝ) (U : Finset (Fin n)) (threshold : ℕ) :
    probability p (fun rho => threshold ≤ (aliveSet U rho).card) =
      binomialTail p U.card threshold := by
  classical
  rw [probability_pushforward p (aliveSet U) (fun S => threshold ≤ S.card)]
  simp_rw [probability_aliveSet_eq]
  have hsum : (∑ S : Finset (Fin n),
      if threshold ≤ S.card then
        (if S ⊆ U then p ^ S.card * (1 - p) ^ (U.card - S.card) else 0) else 0) =
      ∑ S ∈ U.powerset,
        (if threshold ≤ S.card then p ^ S.card * (1 - p) ^ (U.card - S.card) else 0) := by
    rw [show U.powerset = Finset.univ.filter (fun S => S ⊆ U) by ext S; simp,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> rfl
  rw [hsum, Finset.sum_powerset]
  simp_rw [Finset.sum_powersetCard _ U (fun count =>
    if threshold ≤ count then p ^ count * (1 - p) ^ (U.card - count) else 0)]
  unfold binomialTail binomialMass
  apply Finset.sum_congr rfl
  intro successes _
  by_cases h : threshold ≤ successes <;> simp [h, nsmul_eq_mul, mul_assoc]

/-- Tal's Fact 7 in upper-tail form, for every real-valued Boolean-cube function. -/
theorem tailWeight_binomial_transfer {n : ℕ} (p : ℝ) (f : Bits n → ℝ) (threshold : ℕ) :
    expectation p (fun rho => Tal.tailWeight (restrict f rho) threshold) =
      ∑ U : Finset (Fin n), Tal.fourierCoefficient f U ^ 2 *
        binomialTail p U.card threshold := by
  rw [tailWeight_transfer]
  simp_rw [probability_aliveSet_card]

/-- First moments of the local restricted-character coefficients. -/
theorem local_first_moment (p : ℝ) (inU inS : Bool) :
    (∑ value : Option Bool, coordinateMass p value * localCoefficient inU inS value) =
      if inU = inS then (if inS then p else 1) else 0 := by
  rw [Fintype.sum_option, Fintype.sum_bool]
  cases inU <;> cases inS <;> simp [coordinateMass, localCoefficient, Tal.boolSign]

theorem character_first_moment {n : ℕ} (p : ℝ) (U S : Finset (Fin n)) :
    expectation p (characterCoefficient U S) = if U = S then p ^ S.card else 0 := by
  classical
  unfold characterCoefficient
  rw [expectation_prod p (fun i value => localCoefficient (decide (i ∈ U)) (decide (i ∈ S)) value)]
  simp_rw [local_first_moment]
  by_cases heq : U = S
  · subst U
    simp only [if_true]
    simp only [Bool.decide_coe, decide_eq_true_eq]
    rw [← Finset.prod_filter]
    have hfilter : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
    rw [hfilter]
    simp
  · rw [if_neg heq]
    have hdifferent : ∃ i : Fin n, ¬(i ∈ U ↔ i ∈ S) :=
      not_forall.mp (fun h => heq (Finset.ext h))
    obtain ⟨i, hi⟩ := hdifferent
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hU : i ∈ U <;> by_cases hS : i ∈ S <;> simp_all

/-- Tal's Fact 6, first-moment form. -/
theorem coefficient_first_moment {n : ℕ} (p : ℝ) (f : Bits n → ℝ) (S : Finset (Fin n)) :
    expectation p (fun rho => Tal.fourierCoefficient (restrict f rho) S) =
      p ^ S.card * Tal.fourierCoefficient f S := by
  classical
  simp_rw [coefficient_restrict]
  rw [expectation_sum]
  simp_rw [expectation_const_mul, character_first_moment]
  rw [Finset.sum_eq_single S]
  · simp [mul_comm]
  · intro U _ hU
    simp [hU]
  · simp

theorem binomialTail_nonneg {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (trials threshold : ℕ) : 0 ≤ binomialTail p trials threshold := by
  have h := probability_nonneg hzero hone
    (fun rho : Restriction trials => threshold ≤ (aliveSet Finset.univ rho).card)
  simpa only [probability_aliveSet_card, Finset.card_univ, Fintype.card_fin] using h

theorem binomialTail_le_one {p : ℝ} (hzero : 0 ≤ p) (hone : p ≤ 1)
    (trials threshold : ℕ) : binomialTail p trials threshold ≤ 1 := by
  have h := probability_le_one hzero hone
    (fun rho : Restriction trials => threshold ≤ (aliveSet Finset.univ rho).card)
  simpa only [probability_aliveSet_card, Finset.card_univ, Fintype.card_fin] using h

/-- Transfer any proved binomial lower-tail estimate to Fourier tails.

`hbinomial` is an ordinary numerical inequality. `TalSecondMoment` discharges
it by a finite second-moment proof; no median or global circuit theorem is
assumed here.
-/
theorem tailWeight_le_expectation_of_binomial_bound {n : ℕ} {p c : ℝ}
    (hzero : 0 ≤ p) (hone : p ≤ 1) (f : Bits n → ℝ)
    (degree threshold : ℕ)
    (hbinomial : ∀ trials : ℕ, degree ≤ trials → c ≤ binomialTail p trials threshold) :
    c * Tal.tailWeight f degree ≤
      expectation p (fun rho => Tal.tailWeight (restrict f rho) threshold) := by
  rw [tailWeight_binomial_transfer]
  unfold Tal.tailWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U _
  by_cases hdegree : degree ≤ U.card
  · simp only [if_pos hdegree]
    calc
      _ = Tal.fourierCoefficient f U ^ 2 * c := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbinomial U.card hdegree) (sq_nonneg _)
  · simp only [if_neg hdegree, mul_zero]
    exact mul_nonneg (sq_nonneg _) (binomialTail_nonneg hzero hone U.card threshold)

end TalRandomRestriction
