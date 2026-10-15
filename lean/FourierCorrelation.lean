import TaskFootprint
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# From complementary Fourier tails to correlation

This file proves the Boolean Fourier bookkeeping used for multiplication:
Parseval, the Fourier expansion of a correlation, and the Cauchy--Schwarz
bound which combines a target's low-degree mass with a circuit's high-degree
mass.  Tal's theorem can then be supplied only at the final high-tail step.
-/

open scoped BigOperators

noncomputable section

namespace FourierCorrelation

open TransformerAC0

@[simp] theorem boolSign_sq (bit : Bool) : Tal.boolSign bit ^ 2 = 1 := by
  cases bit <;> norm_num [Tal.boolSign]

theorem walshCharacter_mul (left right : Bits n) (set : Finset (Fin n)) :
    Tal.walshCharacter set left * Tal.walshCharacter set right =
      ∏ index ∈ set, Tal.boolSign (left index) * Tal.boolSign (right index) := by
  simp only [Tal.walshCharacter, Finset.prod_mul_distrib]

/-- Completeness/orthogonality of all Walsh characters. -/
theorem sum_walshCharacter_mul (left right : Bits n) :
    (∑ set : Finset (Fin n),
      Tal.walshCharacter set left * Tal.walshCharacter set right) =
        if left = right then (2 ^ n : ℕ) else 0 := by
  classical
  have hexpand :
      (∑ set : Finset (Fin n),
          ∏ index ∈ set,
            Tal.boolSign (left index) * Tal.boolSign (right index)) =
        ∏ index : Fin n,
          (Tal.boolSign (left index) * Tal.boolSign (right index) + 1) := by
    have hprod := Finset.prod_add
      (fun index : Fin n => Tal.boolSign (left index) * Tal.boolSign (right index))
      (fun _index : Fin n => (1 : ℝ)) Finset.univ
    simpa using hprod.symm
  rw [show (∑ set : Finset (Fin n),
      Tal.walshCharacter set left * Tal.walshCharacter set right) =
      ∑ set : Finset (Fin n),
        ∏ index ∈ set,
          Tal.boolSign (left index) * Tal.boolSign (right index) by
        apply Finset.sum_congr rfl
        intro set _
        exact walshCharacter_mul left right set]
  rw [hexpand]
  by_cases heq : left = right
  · subst right
    have hfactor : ∀ index : Fin n,
        Tal.boolSign (left index) * Tal.boolSign (left index) + 1 = 2 := by
      intro index
      cases left index <;> norm_num [Tal.boolSign]
    simp_rw [hfactor]
    simp [Nat.cast_pow]
  · rw [if_neg heq]
    have hdifferent : ∃ index : Fin n, left index ≠ right index := by
      by_contra! hsame
      exact heq (funext hsame)
    obtain ⟨index, hindex⟩ := hdifferent
    norm_num
    apply Finset.prod_eq_zero (Finset.mem_univ index)
    cases hleft : left index <;> cases hright : right index <;>
      simp_all [Tal.boolSign]

/-- Walsh inversion on the finite Boolean cube. -/
theorem fourier_inversion (function : Bits n → ℝ) (input : Bits n) :
    (∑ set : Finset (Fin n),
      Tal.fourierCoefficient function set * Tal.walshCharacter set input) =
        function input := by
  classical
  let cubeSize : ℝ := (2 ^ n : ℕ)
  have hcube : 0 < cubeSize := by positivity
  unfold Tal.fourierCoefficient Tal.uniformExpectation
  rw [show (∑ set : Finset (Fin n),
      (∑ point : Bits n, function point * Tal.walshCharacter set point) /
          (2 ^ n : ℕ) * Tal.walshCharacter set input) =
      (∑ set : Finset (Fin n),
        (∑ point : Bits n, function point * Tal.walshCharacter set point) *
          Tal.walshCharacter set input) / (2 ^ n : ℕ) by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro set _
        ring]
  have hnumerator :
      (∑ set : Finset (Fin n),
          (∑ point : Bits n,
            function point * Tal.walshCharacter set point) *
              Tal.walshCharacter set input) =
        function input * cubeSize := by
    calc
      (∑ set : Finset (Fin n),
          (∑ point : Bits n,
            function point * Tal.walshCharacter set point) *
              Tal.walshCharacter set input) =
          ∑ set : Finset (Fin n), ∑ point : Bits n,
            function point *
              (Tal.walshCharacter set point * Tal.walshCharacter set input) := by
            apply Finset.sum_congr rfl
            intro set _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro point _
            ring
      _ = ∑ point : Bits n, ∑ set : Finset (Fin n),
            function point *
              (Tal.walshCharacter set point * Tal.walshCharacter set input) := by
            rw [Finset.sum_comm]
      _ = ∑ point : Bits n, function point *
            (∑ set : Finset (Fin n),
              Tal.walshCharacter set point * Tal.walshCharacter set input) := by
            apply Finset.sum_congr rfl
            intro point _
            rw [Finset.mul_sum]
      _ = ∑ point : Bits n,
            function point * (if point = input then (2 ^ n : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro point _
            rw [sum_walshCharacter_mul]
      _ = function input * cubeSize := by
            simp [cubeSize]
  rw [hnumerator]
  simpa [cubeSize] using mul_div_cancel_right₀ (function input) hcube.ne'

/-- The uniform inner product is the dot product of Walsh coefficients. -/
theorem correlation_eq_sum_fourier
    (first second : Bits n → ℝ) :
    Tal.uniformExpectation (fun input => first input * second input) =
      ∑ set : Finset (Fin n),
        Tal.fourierCoefficient first set * Tal.fourierCoefficient second set := by
  classical
  let cubeSize : ℝ := (2 ^ n : ℕ)
  unfold Tal.uniformExpectation
  have hrewrite :
      (∑ input : Bits n, first input * second input) =
        ∑ input : Bits n,
          (∑ set : Finset (Fin n),
            Tal.fourierCoefficient first set * Tal.walshCharacter set input) *
              second input := by
    apply Finset.sum_congr rfl
    intro input _
    rw [fourier_inversion]
  rw [hrewrite]
  calc
    (∑ input : Bits n,
          (∑ set : Finset (Fin n),
            Tal.fourierCoefficient first set * Tal.walshCharacter set input) *
              second input) / (2 ^ n : ℕ) =
        (∑ set : Finset (Fin n),
          Tal.fourierCoefficient first set *
            (∑ input : Bits n,
              second input * Tal.walshCharacter set input)) / (2 ^ n : ℕ) := by
          congr 1
          calc
            (∑ input : Bits n,
                (∑ set : Finset (Fin n),
                  Tal.fourierCoefficient first set * Tal.walshCharacter set input) *
                    second input) =
                ∑ input : Bits n, ∑ set : Finset (Fin n),
                  Tal.fourierCoefficient first set *
                    (second input * Tal.walshCharacter set input) := by
                      apply Finset.sum_congr rfl
                      intro input _
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro set _
                      ring
            _ = ∑ set : Finset (Fin n), ∑ input : Bits n,
                  Tal.fourierCoefficient first set *
                    (second input * Tal.walshCharacter set input) := by
                      rw [Finset.sum_comm]
            _ = ∑ set : Finset (Fin n),
                  Tal.fourierCoefficient first set *
                    (∑ input : Bits n,
                      second input * Tal.walshCharacter set input) := by
                      apply Finset.sum_congr rfl
                      intro set _
                      rw [Finset.mul_sum]
    _ = ∑ set : Finset (Fin n),
          Tal.fourierCoefficient first set *
            ((∑ input : Bits n,
              second input * Tal.walshCharacter set input) / (2 ^ n : ℕ)) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro set _
          ring
    _ = ∑ set : Finset (Fin n),
          Tal.fourierCoefficient first set * Tal.fourierCoefficient second set := by
          rfl

/-- Parseval for a Boolean sign function. -/
theorem sum_fourier_sq_of_sign (function : Bits n → Bool) :
    (∑ set : Finset (Fin n),
      Tal.fourierCoefficient (fun input => Tal.boolSign (function input)) set ^ 2) = 1 := by
  calc
    (∑ set : Finset (Fin n),
        Tal.fourierCoefficient (fun input => Tal.boolSign (function input)) set ^ 2) =
      Tal.uniformExpectation (fun input =>
        Tal.boolSign (function input) * Tal.boolSign (function input)) := by
          simpa [pow_two] using
            (correlation_eq_sum_fourier
              (fun input => Tal.boolSign (function input))
              (fun input => Tal.boolSign (function input))).symm
    _ = 1 := by
      unfold Tal.uniformExpectation
      have hterm : ∀ input : Bits n,
          Tal.boolSign (function input) * Tal.boolSign (function input) = 1 := by
        intro input
        cases function input <;> norm_num [Tal.boolSign]
      simp_rw [hterm]
      have hden : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
      rw [show (∑ _input : Bits n, (1 : ℝ)) = ((2 ^ n : ℕ) : ℝ) by
        simp [Bits]]
      exact div_self hden.ne'

/-- Fourier mass below degree `degree`. -/
def lowerWeight (function : Bits n → ℝ) (degree : ℕ) : ℝ :=
  ∑ set ∈ (Finset.univ.filter fun set : Finset (Fin n) => set.card < degree),
    Tal.fourierCoefficient function set ^ 2

theorem lowerWeight_nonneg (function : Bits n → ℝ) (degree : ℕ) :
    0 ≤ lowerWeight function degree := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coefficient_sq_le_lowerWeight
    (function : Bits n → ℝ) (degree : ℕ) (set : Finset (Fin n))
    (hdegree : set.card < degree) :
    Tal.fourierCoefficient function set ^ 2 ≤ lowerWeight function degree := by
  unfold lowerWeight
  have h := Finset.single_le_sum
    (s := Finset.univ.filter fun candidate : Finset (Fin n) => candidate.card < degree)
    (f := fun candidate => Tal.fourierCoefficient function candidate ^ 2)
    (fun candidate _ => sq_nonneg _)
    (by simp [hdegree] : set ∈
      (Finset.univ.filter fun candidate : Finset (Fin n) => candidate.card < degree))
  simpa using h

theorem restricted_sq_sum_le_one_of_sign
    (function : Bits n → Bool) (sets : Finset (Finset (Fin n))) :
    (∑ set ∈ sets,
      Tal.fourierCoefficient (fun input => Tal.boolSign (function input)) set ^ 2) ≤ 1 := by
  rw [← sum_fourier_sq_of_sign function]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ sets)
  intro set _ _
  exact sq_nonneg _

theorem tailWeight_eq_filter (function : Bits n → ℝ) (degree : ℕ) :
    Tal.tailWeight function degree =
      ∑ set ∈ (Finset.univ.filter fun set : Finset (Fin n) => degree ≤ set.card),
        Tal.fourierCoefficient function set ^ 2 := by
  classical
  unfold Tal.tailWeight
  rw [Finset.sum_filter]

/-- Complementary-tail correlation inequality. -/
theorem abs_correlation_le_sqrt_lower_add_sqrt_tail
    (first second : Bits n → Bool) (degree : ℕ) :
    |Tal.uniformExpectation (fun input =>
        Tal.boolSign (first input) * Tal.boolSign (second input))| ≤
      Real.sqrt (lowerWeight (fun input => Tal.boolSign (second input)) degree) +
        Real.sqrt (Tal.tailWeight
          (fun input => Tal.boolSign (first input)) degree) := by
  classical
  let lowSets := Finset.univ.filter fun set : Finset (Fin n) => set.card < degree
  let highSets := Finset.univ.filter fun set : Finset (Fin n) => degree ≤ set.card
  let firstCoefficient := Tal.fourierCoefficient
    (fun input => Tal.boolSign (first input))
  let secondCoefficient := Tal.fourierCoefficient
    (fun input => Tal.boolSign (second input))
  have hpartition :
      (∑ set : Finset (Fin n), firstCoefficient set * secondCoefficient set) =
        (∑ set ∈ lowSets, firstCoefficient set * secondCoefficient set) +
          ∑ set ∈ highSets, firstCoefficient set * secondCoefficient set := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext set
        simp [lowSets, highSets]
        omega
      · intros
        rfl
    · rw [Finset.disjoint_left]
      intro set hlow hhigh
      simp only [lowSets, Finset.mem_filter, Finset.mem_univ, true_and] at hlow
      simp only [highSets, Finset.mem_filter, Finset.mem_univ, true_and] at hhigh
      omega
  have hlowSquare :
      (∑ set ∈ lowSets, firstCoefficient set * secondCoefficient set) ^ 2 ≤
        lowerWeight (fun input => Tal.boolSign (second input)) degree := by
    have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq lowSets
      firstCoefficient secondCoefficient
    calc
      (∑ set ∈ lowSets, firstCoefficient set * secondCoefficient set) ^ 2 ≤
          (∑ set ∈ lowSets, firstCoefficient set ^ 2) *
            ∑ set ∈ lowSets, secondCoefficient set ^ 2 := hcauchy
      _ ≤ 1 * (∑ set ∈ lowSets, secondCoefficient set ^ 2) := by
            gcongr
            exact restricted_sq_sum_le_one_of_sign first lowSets
      _ = lowerWeight (fun input => Tal.boolSign (second input)) degree := by
            simp [lowerWeight, lowSets, secondCoefficient]
  have hhighSquare :
      (∑ set ∈ highSets, firstCoefficient set * secondCoefficient set) ^ 2 ≤
        Tal.tailWeight (fun input => Tal.boolSign (first input)) degree := by
    have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq highSets
      firstCoefficient secondCoefficient
    calc
      (∑ set ∈ highSets, firstCoefficient set * secondCoefficient set) ^ 2 ≤
          (∑ set ∈ highSets, firstCoefficient set ^ 2) *
            ∑ set ∈ highSets, secondCoefficient set ^ 2 := hcauchy
      _ ≤ (∑ set ∈ highSets, firstCoefficient set ^ 2) * 1 := by
            gcongr
            exact restricted_sq_sum_le_one_of_sign second highSets
      _ = Tal.tailWeight (fun input => Tal.boolSign (first input)) degree := by
            rw [tailWeight_eq_filter]
            simp [highSets, firstCoefficient]
  rw [correlation_eq_sum_fourier, hpartition]
  calc
    |(∑ set ∈ lowSets, firstCoefficient set * secondCoefficient set) +
        ∑ set ∈ highSets, firstCoefficient set * secondCoefficient set| ≤
      |∑ set ∈ lowSets, firstCoefficient set * secondCoefficient set| +
        |∑ set ∈ highSets, firstCoefficient set * secondCoefficient set| := abs_add _ _
    _ ≤ Real.sqrt (lowerWeight
          (fun input => Tal.boolSign (second input)) degree) +
        Real.sqrt (Tal.tailWeight
          (fun input => Tal.boolSign (first input)) degree) :=
      add_le_add (Real.abs_le_sqrt hlowSquare) (Real.abs_le_sqrt hhighSquare)

/-- Tal's theorem plugged into the complementary-tail inequality. -/
theorem circuit_correlation_le
    (tal : Tal.FourierTailTheorem)
    (target : Bits n → Bool) (circuit : Circuit n 1)
    (depth size degree : ℕ)
    (hdepth : Circuit.depth circuit ≤ depth)
    (hsize : Circuit.gateCount circuit ≤ size) (hsizeTwo : 1 < size) :
    |Tal.uniformExpectation (fun input =>
      Tal.boolSign (Circuit.eval circuit input 0) * Tal.boolSign (target input))| ≤
      Real.sqrt (lowerWeight (fun input => Tal.boolSign (target input)) degree) +
        Real.sqrt (Tal.tailBound depth size degree) := by
  refine (abs_correlation_le_sqrt_lower_add_sqrt_tail
    (fun input => Circuit.eval circuit input 0) target degree).trans ?_
  gcongr
  exact tal circuit depth size degree hdepth hsize hsizeTwo

end FourierCorrelation
