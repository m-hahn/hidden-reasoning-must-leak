import TalGateNetwork
import TalCommonTreeFourier

/-! The finite bottom cut used by the common-tree switching theorem. -/

noncomputable section
namespace TalGateNetwork.Model
open TransformerAC0 Algebraic AC0 TalMixedSwitching TalCommonTree

def family {n m width : ℕ} (model : Model n (Fin m) width) : Fin m → NormalForm n := by
  classical
  exact fun index => if h : model.rank index = 0 then Classical.choose (model.bottom index h) else .dnf .top

theorem family_width {n m width : ℕ} (model : Model n (Fin m) width) (index : Fin m) :
    (model.family index).WidthAtMost width := by
  classical
  by_cases h : model.rank index = 0
  · simp only [family, dif_pos h]
    exact (Classical.choose_spec (model.bottom index h)).1
  · simp only [family, dif_neg h]
    intro term hterm
    simp only [DNF.top, List.mem_singleton] at hterm
    subst term
    simpa only [LiteralSet.width_empty] using Nat.zero_le width

theorem family_eval_bottom {n m width : ℕ} (model : Model n (Fin m) width) (index : Fin m)
    (h : model.rank index = 0) : (model.family index).eval = model.functions index := by
  classical
  simp only [family, dif_pos h]
  exact funext (Classical.choose_spec (model.bottom index h)).2

theorem bottom_depth_of_family {n m width shallow : ℕ} (model : Model n (Fin m) width)
    (rho : PartialAssignment n)
    (hfamily : ∀ index, DecisionTree.DepthAtMost (ScalarFunction.restrict (model.family index).eval rho) shallow) :
    ∀ index, model.rank index = 0 →
      DecisionTree.DepthAtMost (ScalarFunction.restrict (model.functions index) rho) shallow := by
  intro index hrank
  have h := hfamily index
  rwa [model.family_eval_bottom index hrank] at h

theorem reference_normalForm_of_rank_zero {n m width : ℕ} (model : Model n (Fin m) width)
    (hwidth : 1 ≤ width) (hrank : ∀ index, model.rank index = 0) (reference : Reference n (Fin m)) :
    ∃ formula : NormalForm n, formula.WidthAtMost width ∧ formula.eval = reference.eval model.functions := by
  cases reference with
  | constant value =>
      obtain ⟨dnf, cnf, hdnf, _, ednf, _⟩ :=
        TalTreeNormalForm.normalForms_of_depthAtMost _ width (constant_depthAtMost value width)
      exact ⟨.dnf dnf, hdnf, funext ednf⟩
  | literal atom =>
      obtain ⟨dnf, cnf, hdnf, _, ednf, _⟩ :=
        TalTreeNormalForm.normalForms_of_depthAtMost _ width (literal_depthAtMost atom width hwidth)
      exact ⟨.dnf dnf, hdnf, funext ednf⟩
  | gate index positive =>
      obtain ⟨formula, hformula, heval⟩ := model.bottom index (hrank index)
      cases positive with
      | false =>
          refine ⟨formula.negate, hformula.negate, ?_⟩
          funext input
          simp only [NormalForm.eval_negate, heval, Reference.eval, Bool.false_eq_true, if_false]
      | true => exact ⟨formula, hformula, funext heval⟩

end TalGateNetwork.Model

namespace TalCommonTree.Tree
open TransformerAC0 Algebraic AC0 TalRandomRestriction

theorem leafTailBound_of_leafBound {n m : ℕ} (tree : TalCommonTree.Tree n)
    (family : Fin m → ScalarFunction Bool n) (shallow degree : ℕ) (f : Bits n → ℝ) (epsilon : ℝ)
    (hleaf : ∀ rho : PartialAssignment n,
      (∀ index, DecisionTree.DepthAtMost (ScalarFunction.restrict (family index) rho) shallow) →
        Tal.tailWeight (restrict f rho) degree ≤ epsilon)
    (rho : PartialAssignment n) (h : tree.LeafBound family shallow rho) :
    tree.LeafTailBound f rho degree epsilon := by
  induction tree generalizing rho with
  | leaf => exact hleaf rho h
  | query coordinate zero one ihzero ihone => exact ⟨ihzero _ h.1, ihone _ h.2⟩

end TalCommonTree.Tree
