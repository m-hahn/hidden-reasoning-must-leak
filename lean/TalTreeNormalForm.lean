import Complexitylib.Algebraic.LowerBound.AC0.Duality

/-!
# Bounded-width normal forms of shallow decision trees

Branch literals are conjoined with the child terms, contradictory terms are
dropped, and repeated literals are merged. Consequently the resulting DNF
has width at most the query depth, even when a tree repeats coordinates.
CNF follows by exact Boolean duality.
-/

namespace TalTreeNormalForm
open Algebraic AC0

def addLiteral {n : ℕ} (coordinate : Fin n) (value : Bool) (term : Term n) : Option (Term n) :=
  if term.requirements coordinate = none ∨ term.requirements coordinate = some value then
    some ⟨(PartialAssignment.fix coordinate value).refine term.requirements⟩
  else none

theorem addLiteral_satisfied {n : ℕ} (coordinate : Fin n) (value : Bool)
    (term : Term n) (input : Fin n → Bool) :
    (∃ result, addLiteral coordinate value term = some result ∧ result.SatisfiedBy input) ↔
      input coordinate = value ∧ term.SatisfiedBy input := by
  constructor
  · rintro ⟨result, hresult, hsatisfied⟩
    by_cases hcompatible : term.requirements coordinate = none ∨
        term.requirements coordinate = some value
    · simp only [addLiteral, if_pos hcompatible, Option.some.injEq] at hresult
      subst result
      have hcoordinate : input coordinate = value := hsatisfied coordinate value (by
        simp [PartialAssignment.refine, PartialAssignment.fix])
      refine ⟨hcoordinate, ?_⟩
      intro index required hrequired
      by_cases heq : index = coordinate
      · subst index
        rcases hcompatible with hnone | hsome
        · rw [hnone] at hrequired
          contradiction
        · have heq : required = value := Option.some.inj (hrequired.symm.trans hsome)
          simpa only [heq] using hcoordinate
      · exact hsatisfied index required (by
          simpa only [PartialAssignment.refine, PartialAssignment.fix, if_neg heq] using hrequired)
    · simp [addLiteral, hcompatible] at hresult
  · rintro ⟨hcoordinate, hsatisfied⟩
    have hcompatible : term.requirements coordinate = none ∨
        term.requirements coordinate = some value := by
      cases hterm : term.requirements coordinate with
      | none => exact Or.inl rfl
      | some required =>
          have heq := hsatisfied coordinate required hterm
          exact Or.inr (congrArg some (heq.symm.trans hcoordinate))
    refine ⟨⟨(PartialAssignment.fix coordinate value).refine term.requirements⟩,
      by simp only [addLiteral, if_pos hcompatible], ?_⟩
    intro index required hrequired
    by_cases heq : index = coordinate
    · subst index
      have hvalue : value = required := by
        simpa [PartialAssignment.refine, PartialAssignment.fix] using hrequired
      exact hcoordinate.trans hvalue
    · apply hsatisfied index required
      simpa only [PartialAssignment.refine, PartialAssignment.fix, if_neg heq] using hrequired

theorem addLiteral_width {n : ℕ} (coordinate : Fin n) (value : Bool)
    (term result : Term n) (hresult : addLiteral coordinate value term = some result) :
    result.width ≤ term.width + 1 := by
  unfold addLiteral at hresult
  split_ifs at hresult with h
  · cases Option.some.inj hresult
    simp only [LiteralSet.width, LiteralSet.support, PartialAssignment.fixedVariables_refine,
      PartialAssignment.fixedVariables_fix]
    have hunion : ({coordinate} ∪ term.requirements.fixedVariables) =
        insert coordinate term.requirements.fixedVariables := by ext index; simp
    rw [hunion]
    exact Finset.card_insert_le _ _

def conjoinLiteral {n : ℕ} (coordinate : Fin n) (value : Bool) (formula : DNF n) : DNF n :=
  ⟨formula.terms.filterMap (addLiteral coordinate value)⟩

theorem conjoinLiteral_eval_eq_true {n : ℕ} (coordinate : Fin n) (value : Bool)
    (formula : DNF n) (input : Fin n → Bool) :
    (conjoinLiteral coordinate value formula).eval input = true ↔
      input coordinate = value ∧ formula.eval input = true := by
  rw [DNF.eval_eq_true]
  constructor
  · rintro ⟨result, hresult, hsatisfied⟩
    obtain ⟨term, hterm, hadded⟩ := List.mem_filterMap.mp hresult
    obtain ⟨hcoordinate, hsatisfied⟩ := (addLiteral_satisfied coordinate value term input).mp
      ⟨result, hadded, hsatisfied⟩
    exact ⟨hcoordinate, (DNF.eval_eq_true formula input).mpr ⟨term, hterm, hsatisfied⟩⟩
  · rintro ⟨hcoordinate, hformula⟩
    obtain ⟨term, hterm, hsatisfied⟩ := (DNF.eval_eq_true formula input).mp hformula
    obtain ⟨result, hadded, hsatisfied⟩ := (addLiteral_satisfied coordinate value term input).mpr
      ⟨hcoordinate, hsatisfied⟩
    exact ⟨result, List.mem_filterMap.mpr ⟨term, hterm, hadded⟩, hsatisfied⟩

theorem conjoinLiteral_width {n : ℕ} (coordinate : Fin n) (value : Bool)
    (formula : DNF n) (bound : ℕ) (hwidth : formula.WidthAtMost bound) :
    (conjoinLiteral coordinate value formula).WidthAtMost (bound + 1) := by
  intro result hresult
  obtain ⟨term, hterm, hadded⟩ := List.mem_filterMap.mp hresult
  exact (addLiteral_width coordinate value term result hadded).trans
    (Nat.add_le_add_right (hwidth term hterm) 1)

def disjoin {n : ℕ} (left right : DNF n) : DNF n := ⟨left.terms ++ right.terms⟩

theorem disjoin_eval_eq_true {n : ℕ} (left right : DNF n) (input : Fin n → Bool) :
    (disjoin left right).eval input = true ↔ left.eval input = true ∨ right.eval input = true := by
  simp only [disjoin, DNF.eval, List.any_append, Bool.or_eq_true]

theorem disjoin_width {n : ℕ} (left right : DNF n) (bound : ℕ)
    (hleft : left.WidthAtMost bound) (hright : right.WidthAtMost bound) :
    (disjoin left right).WidthAtMost bound := by
  intro term hterm
  rcases List.mem_append.mp hterm with hleftTerm | hrightTerm
  · exact hleft term hleftTerm
  · exact hright term hrightTerm

def toDNF {n : ℕ} : DecisionTree n → DNF n
  | .leaf false => .bottom
  | .leaf true => .top
  | .query coordinate zero one =>
      disjoin (conjoinLiteral coordinate false (toDNF zero))
        (conjoinLiteral coordinate true (toDNF one))

theorem toDNF_eval {n : ℕ} (tree : DecisionTree n) (input : Fin n → Bool) :
    (toDNF tree).eval input = tree.eval input := by
  induction tree with
  | leaf value => cases value <;> simp [toDNF]
  | query coordinate zero one ihzero ihone =>
      apply Bool.eq_iff_iff.mpr
      simp only [toDNF, disjoin_eval_eq_true, conjoinLiteral_eval_eq_true, ihzero, ihone,
        DecisionTree.eval_query]
      cases input coordinate <;> simp

theorem toDNF_width {n : ℕ} (tree : DecisionTree n) : (toDNF tree).WidthAtMost tree.depth := by
  induction tree with
  | leaf value =>
      cases value <;> simp [toDNF, DNF.WidthAtMost, DNF.bottom, DNF.top, DecisionTree.depth]
  | query coordinate zero one ihzero ihone =>
      apply disjoin_width
      · exact (conjoinLiteral_width coordinate false (toDNF zero) zero.depth ihzero).mono
          (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
      · exact (conjoinLiteral_width coordinate true (toDNF one) one.depth ihone).mono
          (Nat.add_le_add_right (Nat.le_max_right _ _) 1)

def toCNF {n : ℕ} (tree : DecisionTree n) : CNF n := (toDNF tree.negate).negate

theorem toCNF_eval {n : ℕ} (tree : DecisionTree n) (input : Fin n → Bool) :
    (toCNF tree).eval input = tree.eval input := by
  simp only [toCNF, DNF.eval_negate, toDNF_eval, DecisionTree.eval_negate, Bool.not_not]

theorem toCNF_width {n : ℕ} (tree : DecisionTree n) : (toCNF tree).WidthAtMost tree.depth := by
  simpa only [toCNF, DecisionTree.depth_negate] using (toDNF_width tree.negate).negate

/-- Both normal forms are constructed from the actual shallow-tree witness. -/
theorem normalForms_of_depthAtMost {n : ℕ} (f : (Fin n → Bool) → Bool) (bound : ℕ)
    (hdepth : DecisionTree.DepthAtMost f bound) :
    ∃ dnf : DNF n, ∃ cnf : CNF n,
      dnf.WidthAtMost bound ∧ cnf.WidthAtMost bound ∧
        (∀ input, dnf.eval input = f input) ∧ (∀ input, cnf.eval input = f input) := by
  obtain ⟨tree, hcomputes, htree⟩ := hdepth
  refine ⟨toDNF tree, toCNF tree, (toDNF_width tree).mono htree,
    (toCNF_width tree).mono htree, ?_, ?_⟩
  · intro input
    rw [toDNF_eval]
    exact hcomputes input
  · intro input
    rw [toCNF_eval]
    exact hcomputes input

end TalTreeNormalForm
