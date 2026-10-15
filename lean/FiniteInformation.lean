import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite Shannon information

This file supplies the finite probability theory used by the paper.  A
distribution is an explicit probability mass function on a finite type.
Random variables are ordinary functions.  Entropy, joint entropy, conditional
entropy, and mutual information are definitions, not fields of an abstract
certificate.

The principal structural result is `entropy_mono_of_comp`: deterministic
post-processing cannot increase entropy.  It is proved directly by grouping
the finite probability masses.  This gives the entropy identities and
inequalities needed by the public-input and private-randomness arguments.
-/

open scoped BigOperators

noncomputable section

namespace FiniteInformation

/-- An explicit probability distribution on a finite type. -/
structure Distribution (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonnegative : ∀ ω, 0 ≤ mass ω
  sum_one : ∑ ω, mass ω = 1

namespace Distribution

variable {Ω A B C : Type*}
variable [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

/-- Probability of an event. -/
def probability (D : Distribution Ω) (event : Ω → Prop) [DecidablePred event] : ℝ :=
  ∑ ω, if event ω then D.mass ω else 0

/-- The pushforward mass of a finite random variable. -/
def pushMass (D : Distribution Ω) (X : Ω → A) [DecidableEq A] (a : A) : ℝ :=
  ∑ ω, if X ω = a then D.mass ω else 0

/-- Shannon entropy (in bits) of a finite random variable. -/
def entropy (D : Distribution Ω) (X : Ω → A) [DecidableEq A] : ℝ :=
  ∑ a, Real.negMulLog (D.pushMass X a) / Real.log 2

/-- Joint entropy. -/
def jointEntropy (D : Distribution Ω) (X : Ω → A) (Y : Ω → B)
    [DecidableEq A] [DecidableEq B] : ℝ :=
  D.entropy fun ω => (X ω, Y ω)

/-- Conditional entropy, defined by the finite chain rule. -/
def conditionalEntropy (D : Distribution Ω) (X : Ω → A) (Y : Ω → B)
    [DecidableEq A] [DecidableEq B] : ℝ :=
  D.jointEntropy X Y - D.entropy Y

/-- Shannon mutual information. -/
def mutualInformation (D : Distribution Ω) (X : Ω → A) (Y : Ω → B)
    [DecidableEq A] [DecidableEq B] : ℝ :=
  D.entropy X + D.entropy Y - D.jointEntropy X Y

/-- Expectation of a real-valued function. -/
def expectation (D : Distribution Ω) (value : Ω → ℝ) : ℝ :=
  ∑ ω, D.mass ω * value ω

theorem pushMass_nonnegative (D : Distribution Ω) (X : Ω → A)
    [DecidableEq A] (a : A) : 0 ≤ D.pushMass X a := by
  unfold pushMass
  exact Finset.sum_nonneg fun ω _ => by
    split <;> simp_all [D.nonnegative]

theorem sum_pushMass (D : Distribution Ω) (X : Ω → A) [DecidableEq A] :
    ∑ a, D.pushMass X a = 1 := by
  classical
  unfold pushMass
  calc
    (∑ a : A, ∑ ω : Ω, if X ω = a then D.mass ω else 0) =
        ∑ ω : Ω, ∑ a : A, if X ω = a then D.mass ω else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ ω : Ω, D.mass ω := by
          apply Finset.sum_congr rfl
          intro ω _
          simp
    _ = 1 := D.sum_one

theorem pushMass_le_one (D : Distribution Ω) (X : Ω → A)
    [DecidableEq A] (a : A) : D.pushMass X a ≤ 1 := by
  calc
    D.pushMass X a ≤ ∑ a', D.pushMass X a' :=
      Finset.single_le_sum (fun a' _ => D.pushMass_nonnegative X a') (by simp)
    _ = 1 := D.sum_pushMass X

theorem entropy_nonnegative (D : Distribution Ω) (X : Ω → A)
    [DecidableEq A] : 0 ≤ D.entropy X := by
  unfold entropy
  apply Finset.sum_nonneg
  intro a _
  exact div_nonneg
    (Real.negMulLog_nonneg (D.pushMass_nonnegative X a) (D.pushMass_le_one X a))
    (Real.log_nonneg (by norm_num))

/-- Shannon entropy is at least the min-entropy implied by a point-mass cap. -/
theorem neg_log_le_entropy_of_pushMass_le
    (D : Distribution Ω) (X : Ω → A) [DecidableEq A]
    {bound : ℝ} (hbound : 0 < bound)
    (hmax : ∀ a, D.pushMass X a ≤ bound) :
    -Real.logb 2 bound ≤ D.entropy X := by
  have hterm : ∀ a,
      D.pushMass X a * (-Real.logb 2 bound) ≤
        Real.negMulLog (D.pushMass X a) / Real.log 2 := by
    intro a
    by_cases hp : D.pushMass X a = 0
    · simp [hp]
    · have hp0 : 0 < D.pushMass X a :=
        lt_of_le_of_ne (D.pushMass_nonnegative X a) (Ne.symm hp)
      have hlog : Real.logb 2 (D.pushMass X a) ≤ Real.logb 2 bound :=
        (Real.logb_le_logb (by norm_num) hp0 hbound).2 (hmax a)
      simp only [Real.negMulLog, Real.logb]
      have hlogtwo : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hraw : Real.log (D.pushMass X a) ≤ Real.log bound :=
        (div_le_div_iff_of_pos_right hlogtwo).1 hlog
      have hmul := mul_le_mul_of_nonneg_left hraw hp0.le
      rw [show D.pushMass X a * -(Real.log bound / Real.log 2) =
        (-(D.pushMass X a * Real.log bound)) / Real.log 2 by ring]
      apply (div_le_div_iff_of_pos_right hlogtwo).2
      convert neg_le_neg hmul using 1 <;> ring
  calc
    -Real.logb 2 bound =
        (∑ a, D.pushMass X a) * (-Real.logb 2 bound) := by
          rw [D.sum_pushMass X, one_mul]
    _ = ∑ a, D.pushMass X a * (-Real.logb 2 bound) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ a, Real.negMulLog (D.pushMass X a) / Real.log 2 :=
      Finset.sum_le_sum fun a _ => hterm a
    _ = D.entropy X := rfl

/-- Entropy of a finite random variable is at most the logarithm of the
cardinality of its codomain. -/
theorem entropy_le_log_card (D : Distribution Ω) (X : Ω → A)
    [DecidableEq A] [Nonempty A] :
    D.entropy X ≤ Real.logb 2 (Fintype.card A) := by
  let card : ℝ := Fintype.card A
  have hcard : 0 < card := by
    dsimp [card]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hweights : ∑ _a : A, (1 / card : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    change (Fintype.card A : ℝ) * (1 / card) = 1
    field_simp [card, hcard.ne']
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset A))
    (w := fun _ => (1 / card : ℝ))
    (p := fun a => card * D.pushMass X a)
    (fun _ _ => by positivity) hweights
    (fun a _ => Set.mem_Ici.mpr
      (mul_nonneg hcard.le (D.pushMass_nonnegative X a)))
  have hcenter :
      (∑ a : A, (1 / card : ℝ) • (card * D.pushMass X a)) = 1 := by
    simp only [smul_eq_mul]
    calc
      (∑ a : A, (1 / card) * (card * D.pushMass X a)) =
          ∑ a : A, D.pushMass X a := by
            apply Finset.sum_congr rfl
            intro a _
            field_simp [hcard.ne']
      _ = 1 := D.sum_pushMass X
  rw [hcenter, Real.negMulLog_one] at hjensen
  have hexpand :
      (∑ a : A, (1 / card : ℝ) •
          Real.negMulLog (card * D.pushMass X a)) =
        -Real.log card + ∑ a : A, Real.negMulLog (D.pushMass X a) := by
    simp only [smul_eq_mul, Real.negMulLog_mul]
    calc
      (∑ a : A, (1 / card) *
          (D.pushMass X a * Real.negMulLog card +
            card * Real.negMulLog (D.pushMass X a))) =
          ∑ a : A,
            ((1 / card) * D.pushMass X a * Real.negMulLog card +
              Real.negMulLog (D.pushMass X a)) := by
                apply Finset.sum_congr rfl
                intro a _
                field_simp [hcard.ne']
                ring
      _ = (1 / card) * Real.negMulLog card *
            (∑ a : A, D.pushMass X a) +
          ∑ a : A, Real.negMulLog (D.pushMass X a) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = -Real.log card + ∑ a : A, Real.negMulLog (D.pushMass X a) := by
            rw [D.sum_pushMass X, mul_one, Real.negMulLog]
            field_simp [hcard.ne']
            ring
  rw [hexpand] at hjensen
  unfold entropy Real.logb
  rw [← Finset.sum_div]
  have hlogtwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  apply (div_le_div_iff_of_pos_right hlogtwo).2
  linarith

theorem expectation_comp_eq_pushMass
    (D : Distribution Ω) (X : Ω → A) [DecidableEq A] (value : A → ℝ) :
    D.expectation (fun ω => value (X ω)) =
      ∑ a, D.pushMass X a * value a := by
  classical
  unfold expectation pushMass
  calc
    (∑ ω : Ω, D.mass ω * value (X ω)) =
        ∑ ω : Ω, ∑ a : A,
          if X ω = a then D.mass ω * value a else 0 := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [Finset.sum_eq_single (X ω)]
            · simp
            · intro a _ hne
              simp [hne.symm]
            · simp
    _ = ∑ a : A, ∑ ω : Ω,
          if X ω = a then D.mass ω * value a else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ a : A, (∑ ω : Ω,
          if X ω = a then D.mass ω else 0) * value a := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro ω _
            split <;> simp_all

/-- The finite Kraft/source-coding inequality.  `length` is a code length
function and `kraft` is the Kraft inequality, which is proved from
prefix-freeness for terminated traces below. -/
theorem entropy_le_expectedLength_of_kraft
    (D : Distribution Ω) (X : Ω → A) [DecidableEq A]
    (length : A → ℕ) (alphabetCard : ℕ)
    (halphabet : 1 < alphabetCard)
    (kraft : ∑ a : A,
      1 / (alphabetCard : ℝ) ^ length a ≤ 1) :
    D.entropy X ≤
      D.expectation (fun ω => (length (X ω) : ℝ)) *
        Real.logb 2 (alphabetCard : ℝ) := by
  classical
  let support : Finset A := Finset.univ.filter fun a => D.pushMass X a ≠ 0
  let q : ℝ := alphabetCard
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast halphabet
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hsupportMass : ∑ a ∈ support, D.pushMass X a = 1 := by
    rw [← D.sum_pushMass X]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simpa [not_not] using ha
  have hpositive : ∀ a ∈ support, 0 < D.pushMass X a := by
    intro a ha
    have hne : D.pushMass X a ≠ 0 := by
      simpa [support] using ha
    exact lt_of_le_of_ne (D.pushMass_nonnegative X a) (Ne.symm hne)
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := support)
    (w := fun a => D.pushMass X a)
    (p := fun a => (1 / q ^ length a) / D.pushMass X a)
    (fun a ha => (D.pushMass_nonnegative X a)) hsupportMass
    (fun a ha => Set.mem_Ioi.mpr (div_pos (by positivity) (hpositive a ha)))
  have hcenter :
      (∑ a ∈ support, D.pushMass X a •
          ((1 / q ^ length a) / D.pushMass X a)) =
        ∑ a ∈ support, 1 / q ^ length a := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [smul_eq_mul]
    field_simp [(hpositive a ha).ne']
    ring
  rw [hcenter] at hjensen
  have hkSupport : ∑ a ∈ support, 1 / q ^ length a ≤ 1 := by
    calc
      (∑ a ∈ support, 1 / q ^ length a) ≤
          ∑ a : A, 1 / q ^ length a := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro a _ _
            positivity
      _ ≤ 1 := by simpa [q] using kraft
  have hkPositive : 0 < ∑ a ∈ support, 1 / q ^ length a := by
    have hnonempty : support.Nonempty := by
      rcases support.eq_empty_or_nonempty with hempty | hnonempty
      · rw [hempty] at hsupportMass
        simp at hsupportMass
      · exact hnonempty
    obtain ⟨a, ha⟩ := hnonempty
    exact (show 0 < 1 / q ^ length a by positivity).trans_le
      (Finset.single_le_sum (f := fun b => 1 / q ^ length b)
        (fun b _ => by positivity) ha)
  have hlogCenter : Real.log (∑ a ∈ support,
      1 / q ^ length a) ≤ 0 := by
    simpa using (Real.log_nonpos hkPositive.le hkSupport)
  have hweighted :
      ∑ a ∈ support, D.pushMass X a *
          Real.log ((1 / q ^ length a) / D.pushMass X a) ≤ 0 := by
    exact hjensen.trans hlogCenter
  have hexpand :
      ∑ a ∈ support, D.pushMass X a *
          Real.log ((1 / q ^ length a) / D.pushMass X a) =
        (∑ a : A, Real.negMulLog (D.pushMass X a)) -
          (∑ a : A, D.pushMass X a * (length a : ℝ)) * Real.log q := by
    calc
      (∑ a ∈ support, D.pushMass X a *
          Real.log ((1 / q ^ length a) / D.pushMass X a)) =
          ∑ a ∈ support,
            (Real.negMulLog (D.pushMass X a) -
              D.pushMass X a * (length a : ℝ) * Real.log q) := by
                apply Finset.sum_congr rfl
                intro a ha
                have hp := hpositive a ha
                rw [Real.log_div (by positivity : 1 / q ^ length a ≠ 0) hp.ne',
                  Real.log_div one_ne_zero (pow_ne_zero _ hq0.ne'), Real.log_one,
                  Real.log_pow]
                rw [Real.negMulLog]
                ring
      _ = ∑ a : A,
            (Real.negMulLog (D.pushMass X a) -
              D.pushMass X a * (length a : ℝ) * Real.log q) := by
                apply Finset.sum_subset (Finset.filter_subset _ _)
                intro a _ ha
                have hz : D.pushMass X a = 0 := by
                  simpa [support] using ha
                simp [hz]
      _ = (∑ a : A, Real.negMulLog (D.pushMass X a)) -
          (∑ a : A, D.pushMass X a * (length a : ℝ)) * Real.log q := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = (∑ a : A, Real.negMulLog (D.pushMass X a)) -
          (∑ a : A, D.pushMass X a * (length a : ℝ)) * Real.log q := by rfl
  rw [hexpand] at hweighted
  rw [show D.expectation (fun ω => (length (X ω) : ℝ)) =
      ∑ a, D.pushMass X a * (length a : ℝ) from
    D.expectation_comp_eq_pushMass X (fun a => (length a : ℝ))]
  unfold entropy Real.logb
  rw [← Finset.sum_div]
  have hlogtwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [show (∑ a, D.pushMass X a * (length a : ℝ)) *
      (Real.log (alphabetCard : ℝ) / Real.log 2) =
      ((∑ a, D.pushMass X a * (length a : ℝ)) *
        Real.log (alphabetCard : ℝ)) / Real.log 2 by ring]
  apply (div_le_div_iff_of_pos_right hlogtwo).2
  dsimp [q] at hweighted
  nlinarith

/-- The uniform distribution on a nonempty finite type. -/
def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Distribution Ω where
  mass := fun _ => 1 / (Fintype.card Ω : ℝ)
  nonnegative := fun _ => by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    field_simp [show (Fintype.card Ω : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero]

theorem uniform_pushMass_id (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (ω : Ω) :
    (uniform Ω).pushMass id ω = 1 / (Fintype.card Ω : ℝ) := by
  unfold pushMass uniform
  simp

/-- Pushforward of a uniform distribution is normalized fiber cardinality. -/
theorem uniform_pushMass_eq_card
    [Nonempty Ω] [DecidableEq A] (X : Ω → A) (a : A) :
    (uniform Ω).pushMass X a =
      ((Finset.univ.filter fun ω => X ω = a).card : ℝ) / Fintype.card Ω := by
  classical
  unfold pushMass uniform
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_div]
  simp only [Finset.sum_filter]

/-- Uniform probabilities are preserved by a bijective change of sample
space. -/
theorem uniform_pushMass_equiv
    [Nonempty Ω] [Nonempty B] [DecidableEq A]
    (e : Ω ≃ B) (X : B → A) (a : A) :
    (uniform Ω).pushMass (fun ω => X (e ω)) a = (uniform B).pushMass X a := by
  unfold pushMass uniform
  dsimp only
  rw [Fintype.card_congr e]
  exact Equiv.sum_comp e (fun b => if X b = a then 1 / (Fintype.card B : ℝ) else 0)

theorem uniform_entropy_equiv
    [Nonempty Ω] [Nonempty B] [DecidableEq A]
    (e : Ω ≃ B) (X : B → A) :
    (uniform Ω).entropy (fun ω => X (e ω)) = (uniform B).entropy X := by
  unfold entropy
  simp_rw [uniform_pushMass_equiv]

/-- Entropy of the uniform variable on a finite type. -/
theorem uniform_entropy_id (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] :
    (uniform Ω).entropy id = Real.logb 2 (Fintype.card Ω) := by
  apply le_antisymm
  · exact (uniform Ω).entropy_le_log_card id
  · have h := (uniform Ω).neg_log_le_entropy_of_pushMass_le id
        (show 0 < 1 / (Fintype.card Ω : ℝ) by positivity)
        (fun ω => le_of_eq (uniform_pushMass_id Ω ω))
    have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    simp only [Real.logb] at h ⊢
    rw [show 1 / (Fintype.card Ω : ℝ) = (Fintype.card Ω : ℝ)⁻¹ by ring,
      Real.log_inv] at h
    convert h using 1 <;> ring

private theorem negMulLog_sum_le_sum_negMulLog
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a ≤ 1) :
    Real.negMulLog (∑ a, p a) ≤ ∑ a, Real.negMulLog (p a) := by
  by_cases hzero : ∑ a, p a = 0
  · have hall : ∀ a, p a = 0 := by
      intro a
      have hle : p a ≤ ∑ a', p a' :=
        Finset.single_le_sum (fun a' _ => hp a') (by simp)
      exact le_antisymm (by simpa [hzero] using hle) (hp a)
    simp [hzero, hall]
  · have htotal : 0 < ∑ a, p a :=
      lt_of_le_of_ne (Finset.sum_nonneg fun a _ => hp a) (Ne.symm hzero)
    have hterm : ∀ a, -(p a) * Real.log (∑ a', p a') ≤
          Real.negMulLog (p a) := by
      intro a
      by_cases ha : p a = 0
      · simp [ha]
      · have hpa : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm ha)
        have hle : p a ≤ ∑ a', p a' :=
          Finset.single_le_sum (fun a' _ => hp a') (by simp)
        have hlog : Real.log (p a) ≤ Real.log (∑ a', p a') :=
          Real.log_le_log hpa hle
        have hmul := mul_le_mul_of_nonneg_left hlog hpa.le
        have hneg := neg_le_neg hmul
        simpa [Real.negMulLog] using hneg
    calc
      Real.negMulLog (∑ a, p a) =
          ∑ a, -(p a) * Real.log (∑ a', p a') := by
            rw [Real.negMulLog, ← Finset.sum_mul]
            rw [Finset.sum_neg_distrib]
      _ ≤ ∑ a, Real.negMulLog (p a) :=
        Finset.sum_le_sum fun a _ => hterm a

private theorem pushMass_comp
    (D : Distribution Ω) (X : Ω → A) (f : A → B)
    [DecidableEq A] [DecidableEq B] (b : B) :
    D.pushMass (fun ω => f (X ω)) b =
      ∑ a, if f a = b then D.pushMass X a else 0 := by
  classical
  unfold pushMass
  calc
    (∑ ω : Ω, if f (X ω) = b then D.mass ω else 0) =
        ∑ ω : Ω, ∑ a : A,
          if X ω = a ∧ f a = b then D.mass ω else 0 := by
            apply Finset.sum_congr rfl
            intro ω _
            by_cases h : f (X ω) = b
            · rw [Finset.sum_eq_single (X ω)]
              · simp [h]
              · intro a _ hne
                simp [hne.symm]
              · simp
            · simp only [h, if_false]
              symm
              apply Finset.sum_eq_zero
              intro a _
              by_cases ha : X ω = a
              · subst a
                simp [h]
              · simp [ha]
    _ = ∑ a : A, ∑ ω : Ω,
          if X ω = a ∧ f a = b then D.mass ω else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ a, if f a = b then D.pushMass X a else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : f a = b
          · simp [h, pushMass]
          · simp [h]

/-- Deterministic post-processing cannot increase finite Shannon entropy. -/
theorem entropy_comp_le (D : Distribution Ω) (X : Ω → A) (f : A → B)
    [DecidableEq A] [DecidableEq B] :
    D.entropy (fun ω => f (X ω)) ≤ D.entropy X := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hgroup : ∀ b : B,
      Real.negMulLog (D.pushMass (fun ω => f (X ω)) b) ≤
        ∑ a, if f a = b then Real.negMulLog (D.pushMass X a) else 0 := by
    intro b
    rw [pushMass_comp]
    let p : A → ℝ := fun a => if f a = b then D.pushMass X a else 0
    have hp : ∀ a, 0 ≤ p a := by
      intro a
      dsimp [p]
      split <;> simp_all [D.pushMass_nonnegative X]
    have hsum : ∑ a, p a ≤ 1 := by
      calc
        (∑ a, p a) ≤ ∑ a, D.pushMass X a := by
          apply Finset.sum_le_sum
          intro a _
          dsimp [p]
          split <;> simp_all [D.pushMass_nonnegative X]
        _ = 1 := D.sum_pushMass X
    calc
      Real.negMulLog (∑ a, if f a = b then D.pushMass X a else 0) =
          Real.negMulLog (∑ a, p a) := by rfl
      _ ≤ ∑ a, Real.negMulLog (p a) :=
        negMulLog_sum_le_sum_negMulLog p hp hsum
      _ = ∑ a, if f a = b then Real.negMulLog (D.pushMass X a) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp [p]
        split <;> simp_all
  unfold entropy
  rw [← Finset.sum_div, ← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hlog).2
  calc
    (∑ b, Real.negMulLog (D.pushMass (fun ω => f (X ω)) b)) ≤
        ∑ b, ∑ a, if f a = b then Real.negMulLog (D.pushMass X a) else 0 :=
      Finset.sum_le_sum fun b _ => hgroup b
    _ = ∑ a, Real.negMulLog (D.pushMass X a) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp

/-- If `X` is determined by `Y`, then `H(X) ≤ H(Y)`. -/
theorem entropy_mono_of_comp (D : Distribution Ω) (X : Ω → A) (Y : Ω → B)
    [DecidableEq A] [DecidableEq B]
    (decode : B → A) (hdecode : ∀ ω, decode (Y ω) = X ω) :
    D.entropy X ≤ D.entropy Y := by
  have h := D.entropy_comp_le Y decode
  simpa only [hdecode] using h

/-- Two mutually deterministic variables have equal entropy. -/
theorem entropy_eq_of_comp (D : Distribution Ω) (X : Ω → A) (Y : Ω → B)
    [DecidableEq A] [DecidableEq B]
    (decodeX : B → A) (hdecodeX : ∀ ω, decodeX (Y ω) = X ω)
    (decodeY : A → B) (hdecodeY : ∀ ω, decodeY (X ω) = Y ω) :
    D.entropy X = D.entropy Y :=
  le_antisymm
    (D.entropy_mono_of_comp X Y decodeX hdecodeX)
    (D.entropy_mono_of_comp Y X decodeY hdecodeY)

/-- Adjoining another finite variable cannot decrease entropy. -/
theorem entropy_le_jointEntropy (D : Distribution Ω) (X : Ω → A) (Y : Ω → B)
    [DecidableEq A] [DecidableEq B] :
    D.entropy X ≤ D.jointEntropy X Y := by
  exact D.entropy_mono_of_comp X (fun ω => (X ω, Y ω)) Prod.fst (fun _ => rfl)

theorem jointEntropy_comm (D : Distribution Ω) (X : Ω → A) (Y : Ω → B)
    [DecidableEq A] [DecidableEq B] :
    D.jointEntropy X Y = D.jointEntropy Y X := by
  apply D.entropy_eq_of_comp
      (fun ω => (X ω, Y ω)) (fun ω => (Y ω, X ω))
      (fun pair => (pair.2, pair.1)) (fun _ => rfl)
      (fun pair => (pair.2, pair.1)) (fun _ => rfl)

/-- Recovering `X` from `Y` makes the joint entropy equal to `H(Y)`. -/
theorem jointEntropy_eq_right_of_recoverable
    (D : Distribution Ω) (X : Ω → A) (Y : Ω → B)
    [DecidableEq A] [DecidableEq B]
    (decode : B → A) (hdecode : ∀ ω, decode (Y ω) = X ω) :
    D.jointEntropy X Y = D.entropy Y := by
  apply D.entropy_eq_of_comp
      (fun ω => (X ω, Y ω)) Y (fun y => (decode y, y))
      (fun ω => by simpa using congrArg (fun x => (x, Y ω)) (hdecode ω)) Prod.snd
  intro ω
  rfl

/-- The mutual information of a deterministic trace with its complete input
equals the trace entropy. -/
theorem mutualInformation_id_eq_entropy
    [DecidableEq Ω] (D : Distribution Ω) (X : Ω → A) [DecidableEq A] :
    D.mutualInformation id X = D.entropy X := by
  have hjoint : D.jointEntropy id X = D.entropy id := by
    apply D.entropy_eq_of_comp (fun ω => (ω, X ω)) id
      (fun ω => (ω, X ω)) (fun _ => rfl) Prod.fst (fun _ => rfl)
  unfold mutualInformation
  rw [hjoint]
  ring

/-- Adjoining a value recoverable from the observation leaves mutual
information unchanged. -/
theorem mutualInformation_recoverable_pair
    (D : Distribution Ω) (X : Ω → A) (public : Ω → B) (trace : Ω → C)
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (decode : C → B) (recoverable : ∀ ω, decode (trace ω) = public ω) :
    D.mutualInformation X (fun ω => (public ω, trace ω)) = D.mutualInformation X trace := by
  have hpair := D.jointEntropy_eq_right_of_recoverable public trace decode recoverable
  have hjoint : D.jointEntropy X (fun ω => (public ω, trace ω)) = D.jointEntropy X trace := by
    apply D.entropy_eq_of_comp
      (fun ω => (X ω, (public ω, trace ω))) (fun ω => (X ω, trace ω))
      (fun value => (value.1, (decode value.2, value.2)))
      (fun ω => by simp [recoverable ω])
      (fun value => (value.1, value.2.2)) (fun _ => rfl)
  unfold mutualInformation
  change D.entropy X + D.jointEntropy public trace -
      D.jointEntropy X (fun ω => (public ω, trace ω)) =
    D.entropy X + D.entropy trace - D.jointEntropy X trace
  rw [hpair, hjoint]

/-- The concrete finite entropy tradeoff used in the length-tax theorem. -/
theorem entropy_tradeoff
    (D : Distribution Ω) (covert : Ω → A) (public : Ω → B) (trace : Ω → C)
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (decodePublic : C → B) (recoverable : ∀ ω, decodePublic (trace ω) = public ω) :
    D.entropy public +
        D.mutualInformation covert (fun ω => (public ω, trace ω)) -
        D.mutualInformation covert public ≤
      D.entropy trace := by
  have hrecover : D.jointEntropy public trace = D.entropy trace :=
    D.jointEntropy_eq_right_of_recoverable public trace decodePublic recoverable
  have hrefine : D.jointEntropy covert public ≤
      D.entropy (fun ω => (covert ω, (public ω, trace ω))) := by
    exact D.entropy_mono_of_comp
      (fun ω => (covert ω, public ω))
      (fun ω => (covert ω, (public ω, trace ω)))
      (fun value => (value.1, value.2.1)) (fun _ => rfl)
  change D.entropy public +
      (D.entropy covert + D.jointEntropy public trace -
        D.entropy (fun ω => (covert ω, (public ω, trace ω)))) -
      (D.entropy covert + D.entropy public - D.jointEntropy covert public) ≤
    D.entropy trace
  rw [hrecover]
  linarith

/-- Entropy of a random variable with a uniform marginal. -/
theorem entropy_of_uniform_pushMass
    (D : Distribution Ω) (X : Ω → A) [DecidableEq A] [Nonempty A]
    (uniformMarginal : ∀ a, D.pushMass X a = 1 / (Fintype.card A : ℝ)) :
    D.entropy X = Real.logb 2 (Fintype.card A) := by
  rw [← uniform_entropy_id A]
  unfold entropy
  apply Finset.sum_congr rfl
  intro a _
  rw [uniformMarginal, uniform_pushMass_id]

/-- Entropy concavity for a finite mixture, directly from concavity of
`-p log p`. -/
theorem entropy_mixture_ge
    {Index : Type*} [Fintype Index]
    (D : Distribution Ω) (X : Ω → A) [DecidableEq A]
    (weights : Distribution Index) (component : Index → Distribution Ω)
    (mixture : ∀ a, D.pushMass X a =
      ∑ i, weights.mass i * (component i).pushMass X a) :
    (∑ i, weights.mass i * (component i).entropy X) ≤ D.entropy X := by
  unfold entropy
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    (∑ i, weights.mass i *
        ∑ a, Real.negMulLog ((component i).pushMass X a) / Real.log 2) =
      ∑ a, (∑ i, weights.mass i *
        Real.negMulLog ((component i).pushMass X a)) / Real.log 2 := by
        simp_rw [Finset.mul_sum, ← mul_div_assoc]
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_div]
    _ ≤ ∑ a, Real.negMulLog (D.pushMass X a) / Real.log 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply (div_le_div_iff_of_pos_right hlog).2
      rw [mixture a]
      simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
        (t := (Finset.univ : Finset Index))
        (w := weights.mass) (p := fun i => (component i).pushMass X a)
        (fun i _ => weights.nonnegative i) weights.sum_one
        (fun i _ => Set.mem_Ici.mpr ((component i).pushMass_nonnegative X a))

/-- Uniform independent inputs on a finite product. -/
theorem uniform_product_pushMass_fst
    [Nonempty A] [Nonempty B] [DecidableEq A] (a : A) :
    (uniform (A × B)).pushMass Prod.fst a = 1 / (Fintype.card A : ℝ) := by
  unfold pushMass uniform
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod]
  push_cast
  have ha : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

theorem uniform_product_pushMass_snd
    [Nonempty A] [Nonempty B] [DecidableEq B] (b : B) :
    (uniform (A × B)).pushMass Prod.snd b = 1 / (Fintype.card B : ℝ) := by
  unfold pushMass uniform
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Fintype.card_prod]
  push_cast
  have ha : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Lift a fixed-seed input distribution to the product sample space. -/
def fixedRight [Nonempty A] [DecidableEq B] (b : B) : Distribution (A × B) where
  mass := fun pair => if pair.2 = b then (uniform A).mass pair.1 else 0
  nonnegative := by
    intro pair
    split <;> simp_all [(uniform A).nonnegative]
  sum_one := by
    rw [Fintype.sum_prod_type]
    simpa using (uniform A).sum_one

/-- Fixed-seed pushforward masses are exactly those of the input distribution. -/
theorem fixedRight_pushMass [Nonempty A] [DecidableEq B] [DecidableEq C]
    (X : A × B → C) (b : B) (c : C) :
    (fixedRight b).pushMass X c = (uniform A).pushMass (fun a => X (a, b)) c := by
  unfold pushMass fixedRight
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hne
    simp [hne]
  · simp

theorem fixedRight_entropy [Nonempty A] [DecidableEq B] [DecidableEq C]
    (X : A × B → C) (b : B) :
    (fixedRight b).entropy X = (uniform A).entropy (fun a => X (a, b)) := by
  unfold entropy
  simp_rw [fixedRight_pushMass]

/-- Uniform joint sampling is a mixture over the fixed right-hand variable. -/
theorem uniform_product_mixture
    [Nonempty A] [Nonempty B] [DecidableEq B] [DecidableEq C]
    (X : A × B → C) (c : C) :
    (uniform (A × B)).pushMass X c =
      ∑ b, (uniform B).mass b * (fixedRight b).pushMass X c := by
  simp_rw [fixedRight_pushMass]
  unfold pushMass uniform
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Fintype.card_prod]
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp_all [div_mul_div_comm, mul_comm]

theorem uniform_product_entropy_ge_lower
    [Nonempty A] [Nonempty B] [DecidableEq B] [DecidableEq C]
    (trace : A × B → C) (lower : ℝ)
    (fixedSeedLower : ∀ b,
      lower ≤ (uniform A).entropy (fun a => trace (a, b))) :
    lower ≤ (uniform (A × B)).entropy trace := by
  have havg : lower ≤ ∑ b, (uniform B).mass b * (fixedRight b).entropy trace := by
    calc
      lower = ∑ b, (uniform B).mass b * lower := by
        rw [← Finset.sum_mul, (uniform B).sum_one, one_mul]
      _ ≤ ∑ b, (uniform B).mass b * (fixedRight b).entropy trace := by
        apply Finset.sum_le_sum
        intro b _
        rw [fixedRight_entropy]
        exact mul_le_mul_of_nonneg_left (fixedSeedLower b) ((uniform B).nonnegative b)
  exact havg.trans ((uniform (A × B)).entropy_mixture_ge trace (uniform B) fixedRight
    (uniform_product_mixture trace))

/-- A private seed can reduce the information carried by a deterministic
trace by at most the logarithm of the seed alphabet. -/
theorem private_randomness_information_lower_bound
    [Nonempty A] [Nonempty B] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (trace : A × B → C) (lower : ℝ)
    (fixedSeedLower : ∀ b,
      lower ≤ (uniform A).entropy (fun a => trace (a, b))) :
    lower - Real.logb 2 (Fintype.card B) ≤
      (uniform (A × B)).mutualInformation Prod.fst trace := by
  let D := uniform (A × B)
  have hinput : D.entropy Prod.fst = Real.logb 2 (Fintype.card A) :=
    D.entropy_of_uniform_pushMass Prod.fst uniform_product_pushMass_fst
  have htrace : lower ≤ D.entropy trace :=
    uniform_product_entropy_ge_lower trace lower fixedSeedLower
  have hjoint : D.jointEntropy Prod.fst trace ≤
      Real.logb 2 (Fintype.card A) + Real.logb 2 (Fintype.card B) := by
    have hle := D.entropy_comp_le id (fun pair : A × B => (pair.1, trace pair))
    rw [uniform_entropy_id] at hle
    rw [Fintype.card_prod, Nat.cast_mul, Real.logb_mul
      (by exact_mod_cast Fintype.card_ne_zero)
      (by exact_mod_cast Fintype.card_ne_zero)] at hle
    exact hle
  unfold mutualInformation
  rw [hinput]
  linarith

end Distribution

/-! ## Kraft's inequality for separator-terminated traces -/

namespace TerminatedCode

/-- All payload words of length at most `bound`.  The terminal separator is
implicit and is not an element of `Fin dataCard`. -/
def payloads (dataCard : ℕ) : ℕ → Finset (List (Fin dataCard))
  | 0 => {[]}
  | bound + 1 =>
      {[]} ∪ ((Finset.univ.product (payloads dataCard bound)).image
        fun pair => pair.1 :: pair.2)

@[simp] theorem mem_payloads (word : List (Fin dataCard)) (bound : ℕ) :
    word ∈ payloads dataCard bound ↔ word.length ≤ bound := by
  induction bound generalizing word with
  | zero =>
      simp [payloads, List.length_eq_zero]
  | succ bound ih =>
      cases word with
      | nil => simp [payloads]
      | cons head tail =>
          simp [payloads, ih]

/-- Kraft weight after appending one separator token. -/
def weight (dataCard : ℕ) (word : List (Fin dataCard)) : ℝ :=
  1 / (dataCard + 1 : ℕ) ^ (word.length + 1)

@[simp] theorem weight_nil (dataCard : ℕ) :
    weight dataCard [] = 1 / (dataCard + 1 : ℕ) := by
  simp [weight]

theorem weight_cons (head : Fin dataCard) (tail : List (Fin dataCard)) :
    weight dataCard (head :: tail) =
      (1 / (dataCard + 1 : ℕ)) * weight dataCard tail := by
  unfold weight
  push_cast
  rw [pow_succ]
  have hq : (dataCard + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hq]
  ring

private theorem prepend_injective : Function.Injective
    (fun pair : Fin dataCard × List (Fin dataCard) => pair.1 :: pair.2) := by
  intro left right heq
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only [Prod.mk.injEq]
          simpa using List.cons.inj heq

private theorem nil_not_mem_prepend_image (bound : ℕ) :
    [] ∉ ((Finset.univ.product (payloads dataCard bound)).image
      fun pair => pair.1 :: pair.2) := by
  simp

/-- The Kraft sum of every separator-terminated payload of bounded length is
at most one. -/
theorem sum_payloads_weight_le_one (dataCard bound : ℕ) :
    ∑ word ∈ payloads dataCard bound, weight dataCard word ≤ 1 := by
  induction bound with
  | zero =>
      simp only [payloads, Finset.sum_singleton, weight_nil]
      simp only [Nat.cast_add, Nat.cast_one, one_div]
      apply (inv_le_one₀ (show (0 : ℝ) < dataCard + 1 by positivity)).2
      exact le_add_of_nonneg_left (Nat.cast_nonneg dataCard)
  | succ bound ih =>
      let rest : Finset (List (Fin dataCard)) :=
        (Finset.univ.product (payloads dataCard bound)).image
          fun pair => pair.1 :: pair.2
      have hdisjoint : Disjoint ({[]} : Finset (List (Fin dataCard))) rest := by
        rw [Finset.disjoint_singleton_left]
        exact nil_not_mem_prepend_image bound
      rw [payloads, Finset.sum_union hdisjoint]
      simp only [Finset.sum_singleton, weight_nil]
      have hrest :
          (∑ word ∈ rest, weight dataCard word) =
            (dataCard : ℝ) *
              ((1 / (dataCard + 1 : ℕ)) *
                ∑ word ∈ payloads dataCard bound, weight dataCard word) := by
        dsimp [rest]
        rw [Finset.sum_image]
        · rw [Finset.sum_product]
          simp_rw [weight_cons]
          rw [Finset.mul_sum]
          simp
        · intro left _ right _ heq
          exact prepend_injective heq
      rw [hrest]
      have hq : (0 : ℝ) < dataCard + 1 := by positivity
      have hinner :
          (1 / (dataCard + 1 : ℕ) : ℝ) *
              (∑ word ∈ payloads dataCard bound, weight dataCard word) ≤
            (1 / (dataCard + 1 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      have houter :
          (dataCard : ℝ) *
              ((1 / (dataCard + 1 : ℕ)) *
                ∑ word ∈ payloads dataCard bound, weight dataCard word) ≤
            (dataCard : ℝ) * ((1 / (dataCard + 1 : ℕ)) * 1) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      calc
        (1 / (dataCard + 1 : ℕ) : ℝ) +
            (dataCard : ℝ) *
              ((1 / (dataCard + 1 : ℕ)) *
                ∑ word ∈ payloads dataCard bound, weight dataCard word) ≤
          (1 / (dataCard + 1 : ℕ) : ℝ) +
            (dataCard : ℝ) * (1 / (dataCard + 1 : ℕ)) * 1 := by
              exact add_le_add_left (by simpa [mul_assoc] using houter) _
        _ = 1 := by
          field_simp [hq.ne']
          ring

/-- Kraft's inequality for any finite injectively represented collection of
separator-terminated traces. -/
theorem kraft
    {Trace : Type*} [Fintype Trace]
    (payload : Trace → List (Fin dataCard))
    (injective : Function.Injective payload) :
    ∑ trace : Trace, 1 / (dataCard + 1 : ℝ) ^ (payload trace).length.succ ≤ 1 := by
  classical
  let bound := Finset.univ.sup fun trace : Trace => (payload trace).length
  let image : Finset (List (Fin dataCard)) := Finset.univ.image payload
  have himage : image ⊆ payloads dataCard bound := by
    intro word hword
    obtain ⟨trace, _, rfl⟩ := Finset.mem_image.mp hword
    rw [mem_payloads]
    exact Finset.le_sup (s := (Finset.univ : Finset Trace))
      (f := fun trace => (payload trace).length) (by simp)
  calc
    (∑ trace : Trace, 1 / (dataCard + 1 : ℝ) ^ (payload trace).length.succ) =
        ∑ word ∈ image, weight dataCard word := by
          dsimp [image]
          rw [Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro trace _
            simp [weight]
          · intro left _ right _ heq
            exact injective heq
    _ ≤ ∑ word ∈ payloads dataCard bound, weight dataCard word := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro word _ _
      unfold weight
      positivity
    _ ≤ 1 := sum_payloads_weight_le_one dataCard bound

/-- Complete variable-length source-coding bound for traces whose unique
separator is represented separately from their payload. -/
theorem entropy_le_expected_terminated_length
    {Ω Trace : Type*} [Fintype Ω] [Fintype Trace]
    (D : Distribution Ω) (trace : Ω → Trace) [DecidableEq Trace]
    (dataCard : ℕ) (hdata : 0 < dataCard)
    (payload : Trace → List (Fin dataCard))
    (injective : Function.Injective payload) :
    D.entropy trace ≤
      D.expectation (fun ω => ((payload (trace ω)).length + 1 : ℕ)) *
        Real.logb 2 (dataCard + 1 : ℕ) := by
  apply D.entropy_le_expectedLength_of_kraft trace
    (fun t => (payload t).length + 1) (dataCard + 1) (by omega)
  simpa [Nat.succ_eq_add_one] using kraft payload injective

end TerminatedCode

end FiniteInformation

