import TalSwitchingNumerics

/-!
# Shared switching for mixed DNF/CNF families

Each CNF is complemented once for canonical DNF replay. A shared tree has the
same leaf depth bounds before and after any per-member output complementation.
There is one advice index per original family member, not two.
-/

namespace TalMixedSwitching
open Algebraic AC0 TalCommonTree

def signedFamily {n m : ℕ} (family : Fin m → ScalarFunction Bool n) (negated : Fin m → Bool) :
    Fin m → ScalarFunction Bool n :=
  fun index input => if negated index then !(family index input) else family index input

theorem leafBound_signedFamily_iff {n m : ℕ} (tree : Tree n)
    (family : Fin m → ScalarFunction Bool n) (negated : Fin m → Bool)
    (rho : PartialAssignment n) (shallow : ℕ) :
    tree.LeafBound (signedFamily family negated) shallow rho ↔ tree.LeafBound family shallow rho := by
  induction tree generalizing rho with
  | leaf =>
      apply forall_congr'
      intro index
      cases hnegated : negated index with
      | false =>
          have heq : signedFamily family negated index = family index := by
            funext input
            simp [signedFamily, hnegated]
          rw [heq]
      | true =>
          have heq : ScalarFunction.restrict (signedFamily family negated index) rho =
              fun input => !((ScalarFunction.restrict (family index) rho) input) := by
            funext input
            simp [ScalarFunction.restrict, signedFamily, hnegated]
          rw [heq]
          exact DecisionTree.depthAtMost_negate_iff _ _
  | query coordinate zero one ihzero ihone => exact and_congr (ihzero _) (ihone _)

theorem hasCommonTree_signedFamily_iff {n m : ℕ}
    (family : Fin m → ScalarFunction Bool n) (negated : Fin m → Bool)
    (rho : PartialAssignment n) (shallow depth : ℕ) :
    HasCommonTree (signedFamily family negated) rho shallow depth ↔
      HasCommonTree family rho shallow depth := by
  unfold HasCommonTree
  apply exists_congr
  intro tree
  exact and_congr (leafBound_signedFamily_iff tree family negated rho shallow) Iff.rfl

inductive NormalForm (n : ℕ)
  | dnf (formula : DNF n)
  | cnf (formula : CNF n)

namespace NormalForm

def eval {n : ℕ} : NormalForm n → ScalarFunction Bool n
  | .dnf formula => formula.eval
  | .cnf formula => formula.eval

def WidthAtMost {n : ℕ} : NormalForm n → ℕ → Prop
  | .dnf formula, width => formula.WidthAtMost width
  | .cnf formula, width => formula.WidthAtMost width

def dnfView {n : ℕ} : NormalForm n → DNF n
  | .dnf formula => formula
  | .cnf formula => formula.negate

def isNegated {n : ℕ} : NormalForm n → Bool
  | .dnf _ => false
  | .cnf _ => true

theorem dnfView_width {n : ℕ} (formula : NormalForm n) (width : ℕ)
    (hwidth : formula.WidthAtMost width) : formula.dnfView.WidthAtMost width := by
  cases formula with
  | dnf formula => exact hwidth
  | cnf formula => exact hwidth.negate

end NormalForm

theorem hasCommonTree_dnfView_iff {n m : ℕ} (family : Fin m → NormalForm n)
    (rho : PartialAssignment n) (shallow depth : ℕ) :
    HasCommonTree (fun index => (family index).dnfView.eval) rho shallow depth ↔
      HasCommonTree (fun index => (family index).eval) rho shallow depth := by
  have heq : (fun index => (family index).dnfView.eval) =
      signedFamily (fun index => (family index).eval) (fun index => (family index).isNegated) := by
    funext index input
    cases hformula : family index <;>
      simp [signedFamily, NormalForm.dnfView, NormalForm.eval, NormalForm.isNegated, hformula]
  rw [heq]
  exact hasCommonTree_signedFamily_iff _ _ _ _ _

/-- The exact family-size prefactor is retained for mixed CNF/DNF members. -/
theorem probability_no_commonTree_le {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → NormalForm n) (hwidth : ∀ index, (family index).WidthAtMost width) (degree : ℕ) :
    TalRandomRestriction.probability (TalSwitchingNumerics.parameter width : ℝ)
        (fun rho => ¬HasCommonTree (fun index => (family index).eval) rho (Nat.log 2 (2 * m))
          (⌊(degree : ℝ) / (360 * width)⌋₊ - 1)) ≤
      2 * (2 : ℝ) ^ (-(degree : ℝ) / (1440 * width * Real.logb 2 (2 * m : ℕ))) := by
  have hevent : (fun rho => ¬HasCommonTree (fun index => (family index).eval) rho
      (Nat.log 2 (2 * m)) (⌊(degree : ℝ) / (360 * width)⌋₊ - 1)) =
      TalMultiSwitching.Bad (fun index => (family index).dnfView) (Nat.log 2 (2 * m))
        ⌊(degree : ℝ) / (360 * width)⌋₊ := by
    funext rho
    exact propext (not_congr (hasCommonTree_dnfView_iff family rho _ _).symm)
  rw [hevent]
  exact TalSwitchingNumerics.probability_bad_le _
    (fun index => (family index).dnfView_width width (hwidth index)) degree

end TalMixedSwitching
