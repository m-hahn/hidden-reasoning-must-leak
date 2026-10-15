import TransformerAC0
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Tal's Fourier-tail theorem for AC⁰

This module formalizes the general theorem quoted in the paper appendix, not
just its parity-correlation consequence.  It defines the normalized Walsh
Fourier transform on the Boolean cube, exact-degree and upper-tail Fourier
weights, and the full quantitative statement

`W^{≥k}[f] ≤ 2 · 2^{-k / (216^d log(m)^(d-1))}`

for the sign of a depth-`d`, size-`m` unbounded-fanin circuit.
`TalComplete.fourierTailTheorem` proves this proposition locally, including
common-tree switching, shared-circuit depth reduction, the Fourier induction,
and the displayed constants. The statement and Fourier foundations live here
separately from that proof to avoid an import cycle. The specialization from
the general statement to parity correlation is proved below; unconditional
paper-level entry points are supplied by `TalConsequences.lean`.
-/

open scoped BigOperators

noncomputable section

namespace Tal

open TransformerAC0

/-- The `±1` representation of a Boolean value. -/
def boolSign (b : Bool) : ℝ := if b then -1 else 1

/-- Parity, recursively exposed at the first coordinate. -/
def parity : {n : ℕ} → Bits n → Bool
  | 0, _ => false
  | _ + 1, input => Bool.xor (input 0) (parity (Fin.tail input))

/-- The Walsh character indexed by a subset of coordinates. -/
def walshCharacter {n : ℕ} (S : Finset (Fin n)) (input : Bits n) : ℝ :=
  ∏ i ∈ S, boolSign (input i)

/-- Uniform expectation on the Boolean cube. -/
def uniformExpectation {n : ℕ} (f : Bits n → ℝ) : ℝ :=
  (∑ input, f input) / (2 ^ n : ℕ)

/-- Normalized Walsh--Fourier coefficient. -/
def fourierCoefficient {n : ℕ} (f : Bits n → ℝ) (S : Finset (Fin n)) : ℝ :=
  uniformExpectation fun input => f input * walshCharacter S input

/-- Fourier weight at exact degree `k`. -/
def levelWeight {n : ℕ} (f : Bits n → ℝ) (k : ℕ) : ℝ :=
  ∑ S : Finset (Fin n), if S.card = k then fourierCoefficient f S ^ 2 else 0

/-- Fourier weight at degrees at least `k`. -/
def tailWeight {n : ℕ} (f : Bits n → ℝ) (k : ℕ) : ℝ :=
  ∑ S : Finset (Fin n), if k ≤ S.card then fourierCoefficient f S ^ 2 else 0

/-- The sign function computed by a one-output Boolean circuit. -/
def circuitSign {n : ℕ} (circuit : Circuit n 1) (input : Bits n) : ℝ :=
  boolSign (Circuit.eval circuit input 0)

/-- The quantitative right-hand side in the appendix's statement of Tal. -/
def tailBound (depth size degree : ℕ) : ℝ :=
  2 * (2 : ℝ) ^
    (-(degree : ℝ) /
      ((216 : ℝ) ^ depth * Real.logb 2 size ^ (depth - 1)))

/--
Theorem 18 of Tal, in the general Fourier-tail form stated in the appendix.

This proposition is proved by `TalComplete.fourierTailTheorem`. It
quantifies over every input dimension, circuit, upper-tail threshold, and
valid depth/size bound.
-/
def FourierTailTheorem : Prop :=
  ∀ {n : ℕ} (circuit : Circuit n 1) (depth size degree : ℕ),
    Circuit.depth circuit ≤ depth →
    Circuit.gateCount circuit ≤ size →
    1 < size →
    tailWeight (circuitSign circuit) degree ≤ tailBound depth size degree

@[simp] theorem boolSign_false : boolSign false = 1 := rfl

@[simp] theorem boolSign_true : boolSign true = -1 := rfl

theorem boolSign_xor (a b : Bool) :
    boolSign (Bool.xor a b) = boolSign a * boolSign b := by
  cases a <;> cases b <;> norm_num [boolSign]

/-- The parity sign is the top-degree Walsh character. -/
theorem boolSign_parity_eq_walsh_univ {n : ℕ} (input : Bits n) :
    boolSign (parity input) = walshCharacter Finset.univ input := by
  induction n with
  | zero => simp [parity, walshCharacter, boolSign]
  | succ n ih =>
      rw [parity, boolSign_xor, walshCharacter]
      rw [Fin.prod_univ_succ]
      change boolSign (input 0) * boolSign (parity (Fin.tail input)) =
        boolSign (input 0) * ∏ i : Fin n, boolSign (input i.succ)
      rw [ih]
      rfl

/-- Correlation with parity is the top Fourier coefficient. -/
theorem fourierCoefficient_univ_eq_parityCorrelation
    {n : ℕ} (f : Bits n → ℝ) :
    fourierCoefficient f Finset.univ =
      uniformExpectation (fun input => f input * boolSign (parity input)) := by
  unfold fourierCoefficient
  congr 1
  funext input
  rw [boolSign_parity_eq_walsh_univ]

theorem fourierCoefficient_sq_nonneg {n : ℕ} (f : Bits n → ℝ)
    (S : Finset (Fin n)) :
    0 ≤ fourierCoefficient f S ^ 2 := sq_nonneg _

/-- Any coefficient of degree at least `k` is contained in `W^{≥k}`. -/
theorem coefficient_sq_le_tailWeight {n k : ℕ} (f : Bits n → ℝ)
    (S : Finset (Fin n)) (hdegree : k ≤ S.card) :
    fourierCoefficient f S ^ 2 ≤ tailWeight f k := by
  unfold tailWeight
  calc
    fourierCoefficient f S ^ 2 =
        (if k ≤ S.card then fourierCoefficient f S ^ 2 else 0) := by
      rw [if_pos hdegree]
    _ ≤ ∑ T : Finset (Fin n),
        if k ≤ T.card then fourierCoefficient f T ^ 2 else 0 := by
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset (Finset (Fin n))))
        (f := fun T => if k ≤ T.card then fourierCoefficient f T ^ 2 else 0)
        (fun T _ => by
          by_cases hT : k ≤ T.card
          · simp [hT, sq_nonneg]
          · simp [hT])
        (Finset.mem_univ S)
      simpa using h

/-- The squared parity correlation is bounded by the top Fourier tail. -/
theorem parityCorrelation_sq_le_tailWeight {n : ℕ} (f : Bits n → ℝ) :
    uniformExpectation (fun input => f input * boolSign (parity input)) ^ 2 ≤
      tailWeight f n := by
  rw [← fourierCoefficient_univ_eq_parityCorrelation]
  apply coefficient_sq_le_tailWeight
  simp

/-- Tal's general theorem specialized to squared parity correlation. -/
theorem parityCorrelation_sq_le
    (tal : FourierTailTheorem) {n : ℕ} (circuit : Circuit n 1)
    (depth size : ℕ)
    (hdepth : Circuit.depth circuit ≤ depth)
    (hsize : Circuit.gateCount circuit ≤ size)
    (hsizeTwo : 1 < size) :
    uniformExpectation (fun input =>
      circuitSign circuit input * boolSign (parity input)) ^ 2 ≤
        tailBound depth size n := by
  exact (parityCorrelation_sq_le_tailWeight (circuitSign circuit)).trans
    (tal circuit depth size n hdepth hsize hsizeTwo)

/-- Nonnegativity of Tal's displayed upper bound. -/
theorem tailBound_nonneg (depth size degree : ℕ) :
    0 ≤ tailBound depth size degree := by
  unfold tailBound
  positivity

theorem tailBound_pos (depth size degree : ℕ) :
    0 < tailBound depth size degree := by
  unfold tailBound
  positivity

/-- Absolute parity correlation is bounded by the square root of Tal's tail. -/
theorem abs_parityCorrelation_le_sqrt_tailBound
    (tal : FourierTailTheorem) {n : ℕ} (circuit : Circuit n 1)
    (depth size : ℕ)
    (hdepth : Circuit.depth circuit ≤ depth)
    (hsize : Circuit.gateCount circuit ≤ size)
    (hsizeTwo : 1 < size) :
    |uniformExpectation (fun input =>
      circuitSign circuit input * boolSign (parity input))| ≤
        Real.sqrt (tailBound depth size n) := by
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (tailBound_nonneg depth size n)]
  exact parityCorrelation_sq_le tal circuit depth size hdepth hsize hsizeTwo

end Tal
