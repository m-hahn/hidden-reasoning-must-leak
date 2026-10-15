import TalRestriction
import Complexitylib.Algebraic.LowerBound.AC0.DecisionTree

/-!
# Fourier degree and restriction of decision trees

The algebraic restriction lemma here is independent of any circuit or
switching theorem. It connects the checked switching theorem's Boolean
decision trees to vanishing upper Fourier tails.
-/

noncomputable section
namespace TalDecisionTree
open TransformerAC0
open TalRestriction

/-- Restricting a coordinate cannot create a nonzero tail above a vanishing original tail. -/
theorem slice_tailWeight_eq_zero {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) (value : Bool) (k : ℕ) (hzero : Tal.tailWeight f k = 0) :
    Tal.tailWeight (slice f i value) k = 0 := by
  unfold Tal.tailWeight
  apply Finset.sum_eq_zero
  intro S _
  by_cases hdegree : k ≤ S.card
  · rw [if_pos hdegree]
    have hlift := Tal.coefficient_sq_le_tailWeight (k := k) f (liftSet i S)
      (by simpa only [card_liftSet] using hdegree)
    have hinsert := Tal.coefficient_sq_le_tailWeight (k := k) f (insert i (liftSet i S))
      (by rw [Finset.card_insert_of_not_mem (not_mem_liftSet i S), card_liftSet]; omega)
    rw [hzero] at hlift hinsert
    have henergy := coefficient_energy_split f i S
    cases value <;> nlinarith [sq_nonneg (Tal.fourierCoefficient (slice f i false) S),
      sq_nonneg (Tal.fourierCoefficient (slice f i true) S)]
  · simp [hdegree]

/-- Signs of global-coordinate trees, including trees that repeat queries. -/
def signEval {n : ℕ} (tree : Algebraic.AC0.DecisionTree n) (input : Bits n) : ℝ :=
  Tal.boolSign (tree.eval input)

theorem tailWeight_depth_succ {n : ℕ} (tree : Algebraic.AC0.DecisionTree n) :
    Tal.tailWeight (signEval tree) (tree.depth + 1) = 0 := by
  induction tree with
  | leaf value => exact tailWeight_const (Tal.boolSign value) 0
  | query i zero one ihzero ihone =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
        have hz : Tal.tailWeight (signEval zero) (max zero.depth one.depth + 1) = 0 := by
          apply le_antisymm _ (tailWeight_nonneg _ _)
          rw [← ihzero]
          exact tailWeight_mono (signEval zero)
            (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
        have ho : Tal.tailWeight (signEval one) (max zero.depth one.depth + 1) = 0 := by
          apply le_antisymm _ (tailWeight_nonneg _ _)
          rw [← ihone]
          exact tailWeight_mono (signEval one)
            (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
        have hs := tailWeight_slice (signEval (.query i zero one)) i
          (max zero.depth one.depth + 1)
        have hfalse : slice (signEval (.query i zero one)) i false =
            slice (signEval zero) i false := by
          funext input
          simp [TalRestriction.slice, signEval, Algebraic.AC0.DecisionTree.eval]
        have htrue : slice (signEval (.query i zero one)) i true =
            slice (signEval one) i true := by
          funext input
          simp [TalRestriction.slice, signEval, Algebraic.AC0.DecisionTree.eval]
        rw [hfalse, htrue,
          slice_tailWeight_eq_zero _ i false _ hz,
          slice_tailWeight_eq_zero _ i true _ ho] at hs
        apply le_antisymm _ (tailWeight_nonneg _ _)
        simpa only [Algebraic.AC0.DecisionTree.depth, Nat.succ_eq_add_one,
          zero_add, zero_div] using hs

/-- The semantic depth predicate of the switching theorem gives a zero tail. -/
theorem tailWeight_eq_zero_of_depthAtMost {n : ℕ} (f : Bits n → Bool) (bound degree : ℕ)
    (hdepth : Algebraic.AC0.DecisionTree.DepthAtMost f bound) (hdegree : bound < degree) :
    Tal.tailWeight (fun input => Tal.boolSign (f input)) degree = 0 := by
  obtain ⟨tree, hcomputes, htree⟩ := hdepth
  have heval : (fun input => Tal.boolSign (f input)) = signEval tree := by
    funext input
    rw [signEval, hcomputes input]
  rw [heval]
  apply le_antisymm _ (tailWeight_nonneg _ _)
  rw [← tailWeight_depth_succ tree]
  exact tailWeight_mono _ (by omega)

end TalDecisionTree
