import TalCommonTree
import TalRandomRestriction

/-!
# Fourier tails for the actual shared partial query trees

This connects the global-coordinate trees used in multi-switching with the
normalized Fourier transform. Repeated queries and previously fixed variables
are permitted: a query costs at most one degree in every case.
-/

noncomputable section
namespace TalCommonTreeFourier
open TransformerAC0 TalRestriction TalRandomRestriction Algebraic

theorem tailWeight_eq_slice_of_slices_eq {n : ℕ} (f : Bits (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) (degree : ℕ)
    (h : slice f coordinate false = slice f coordinate true) :
    Tal.tailWeight f degree = Tal.tailWeight (slice f coordinate false) degree := by
  have hcoeff (S : Finset (Fin n)) :
      Tal.fourierCoefficient f (liftSet coordinate S) =
        Tal.fourierCoefficient (slice f coordinate false) S := by
    rw [coefficient_liftSet, ← h]
    ring
  have hinsert (S : Finset (Fin n)) :
      Tal.fourierCoefficient f (insert coordinate (liftSet coordinate S)) = 0 := by
    rw [coefficient_insert_liftSet, h]
    ring
  unfold Tal.tailWeight
  rw [sum_subsets_split coordinate]
  simp only [card_liftSet, hcoeff, hinsert, zero_pow (by decide : 2 ≠ 0), ite_self,
    Finset.sum_const_zero, add_zero]

theorem slice_fixed {n : ℕ} (f : Bits (n + 1) → ℝ) (coordinate : Fin (n + 1))
    (value branch : Bool) :
    slice (restrict f (PartialAssignment.fix coordinate value)) coordinate branch =
      slice f coordinate value := by
  funext input
  unfold TalRestriction.slice restrict
  congr 1
  funext index
  cases index using coordinate.succAboveCases <;>
    simp [applyRestriction, PartialAssignment.fix, Fin.succAbove_ne]

theorem tailWeight_fixed_eq_slice {n : ℕ} (f : Bits (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) (value : Bool) (degree : ℕ) :
    Tal.tailWeight (restrict f (PartialAssignment.fix coordinate value)) degree =
      Tal.tailWeight (slice f coordinate value) degree := by
  rw [tailWeight_eq_slice_of_slices_eq _ coordinate degree
    (by rw [slice_fixed, slice_fixed]), slice_fixed]

/-- Same-dimensional form of Tal's one-query inequality. -/
theorem tailWeight_query {n : ℕ} (f : Bits n → ℝ) (coordinate : Fin n) (degree : ℕ) :
    Tal.tailWeight f (degree + 1) ≤
      (Tal.tailWeight (restrict f (PartialAssignment.fix coordinate false)) degree +
        Tal.tailWeight (restrict f (PartialAssignment.fix coordinate true)) degree) / 2 := by
  cases n with
  | zero => exact Fin.elim0 coordinate
  | succ n =>
      rw [tailWeight_fixed_eq_slice, tailWeight_fixed_eq_slice]
      exact tailWeight_slice f coordinate degree

theorem restrict_refine {n : ℕ} (f : Bits n → ℝ) (rho sigma : PartialAssignment n) :
    restrict f (rho.refine sigma) = restrict (restrict f rho) sigma := by
  funext input
  exact congrArg f (PartialAssignment.apply_refine rho sigma input)

end TalCommonTreeFourier

namespace TalCommonTree.Tree
open TransformerAC0 TalRestriction TalRandomRestriction Algebraic TalCommonTreeFourier

def LeafTailBound {n : ℕ} : TalCommonTree.Tree n → (Bits n → ℝ) →
    PartialAssignment n → ℕ → ℝ → Prop
  | .leaf, f, rho, degree, epsilon => Tal.tailWeight (restrict f rho) degree ≤ epsilon
  | .query coordinate zero one, f, rho, degree, epsilon =>
      zero.LeafTailBound f (rho.refine (PartialAssignment.fix coordinate false)) degree epsilon ∧
        one.LeafTailBound f (rho.refine (PartialAssignment.fix coordinate true)) degree epsilon

/-- Tal's adaptive tree lemma for the shared trees in the family switching theorem. -/
theorem tailWeight_bound {n : ℕ} (tree : TalCommonTree.Tree n) (f : Bits n → ℝ)
    (rho : PartialAssignment n) (degree : ℕ) (epsilon : ℝ)
    (h : tree.LeafTailBound f rho degree epsilon) :
    Tal.tailWeight (restrict f rho) (degree + tree.depth) ≤ epsilon := by
  induction tree generalizing rho with
  | leaf => simpa only [depth, Nat.add_zero] using h
  | query coordinate zero one ihzero ihone =>
      obtain ⟨hz, ho⟩ := h
      have hzero := ihzero _ hz
      have hone := ihone _ ho
      have hzero' := (tailWeight_mono _
        (Nat.add_le_add_left (Nat.le_max_left zero.depth one.depth) degree)).trans hzero
      have hone' := (tailWeight_mono _
        (Nat.add_le_add_left (Nat.le_max_right zero.depth one.depth) degree)).trans hone
      have hquery := tailWeight_query (restrict f rho) coordinate (degree + max zero.depth one.depth)
      rw [← restrict_refine, ← restrict_refine] at hquery
      change Tal.tailWeight (restrict f rho) (degree + (max zero.depth one.depth + 1)) ≤ epsilon
      rw [← Nat.add_assoc]
      linarith

theorem tailWeight_bound_of_depth_le {n : ℕ} (tree : TalCommonTree.Tree n) (f : Bits n → ℝ)
    (rho : PartialAssignment n) (degree bound : ℕ) (epsilon : ℝ)
    (hdepth : tree.depth ≤ bound) (h : tree.LeafTailBound f rho degree epsilon) :
    Tal.tailWeight (restrict f rho) (degree + bound) ≤ epsilon :=
  (tailWeight_mono _ (Nat.add_le_add_left hdepth degree)).trans
    (tree.tailWeight_bound f rho degree epsilon h)

end TalCommonTree.Tree
