import Complexitylib.Algebraic.LowerBound.AC0.Switching.CanonicalEncoding

/-!
# Completing canonical prefixes at source-term boundaries

Family multi-switching queries a complete final source-term block in each
phase. This file completes any canonical prefix, without requiring a false
leaf or presuming that the formula is non-tautological.
-/

namespace TalCanonicalCompletion
open Algebraic AC0

mutual
def ClosedTrace {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)} : formula.CanonicalTrace rho steps → Prop
  | .nil _ => True
  | .start _ _ _ block => ClosedBlock block

def ClosedBlock {n : ℕ} {formula : DNF n} {term : Term n} {rho : PartialAssignment n}
    {indices : List (Fin n)} {steps : List (DecisionTree.PathStep n)} :
    formula.CanonicalBlockTrace term rho indices steps → Prop
  | .nil _ _ _ => False
  | .takeMore tail => ClosedBlock tail
  | .takeLast tail => ClosedTrace tail
end

/-- Every nonfinal term boundary is strictly before the phase's minimum length. -/
def BoundariesBefore (minimum : ℕ) {width : ℕ} (advice : List (Switching.QueryAdvice width)) : Prop :=
  ∀ index (hindex : index + 1 < advice.length), minimum ≤ index + 1 →
    (advice[index]'(by omega)).closesBlock = false

theorem boundariesBefore_nil (minimum width : ℕ) :
    BoundariesBefore minimum ([] : List (Switching.QueryAdvice width)) := by
  intro index hindex _
  simp only [List.length_nil] at hindex
  omega

theorem boundariesBefore_singleton (minimum : ℕ) {width : ℕ}
    (symbol : Switching.QueryAdvice width) : BoundariesBefore minimum [symbol] := by
  intro index hindex _
  simp only [List.length_cons, List.length_nil] at hindex
  omega

theorem boundariesBefore_cons {width : ℕ} (minimum : ℕ)
    (symbol : Switching.QueryAdvice width) (rest : List (Switching.QueryAdvice width))
    (hhead : symbol.closesBlock = false ∨ 1 < minimum ∨ rest = [])
    (htail : BoundariesBefore (minimum - 1) rest) :
    BoundariesBefore minimum (symbol :: rest) := by
  intro index hindex hminimum
  cases index with
  | zero =>
      simp only [List.getElem_cons_zero]
      rcases hhead with hfalse | hlarge | hempty
      · exact hfalse
      · omega
      · simp only [hempty, List.length_cons, List.length_nil] at hindex
        omega
  | succ index =>
      simp only [List.getElem_cons_succ]
      apply htail index
      · simp only [List.length_cons] at hindex
        omega
      · omega

def falseSteps {n : ℕ} (indices : List (Fin n)) : List (DecisionTree.PathStep n) :=
  indices.map fun coordinate => ⟨coordinate, false⟩

def fullBlock {n : ℕ} (formula : DNF n) (term : Term n)
    (rho : PartialAssignment n) (coordinate : Fin n) (rest : List (Fin n)) :
    formula.CanonicalBlockTrace term rho (coordinate :: rest) (falseSteps (coordinate :: rest)) :=
  match rest with
  | [] => .takeLast (.nil (rho.refine (PartialAssignment.fix coordinate false)))
  | next :: remaining => .takeMore (fullBlock formula term
      (rho.refine (PartialAssignment.fix coordinate false)) next remaining)

theorem fullBlock_closed {n : ℕ} (formula : DNF n) (term : Term n)
    (rho : PartialAssignment n) (coordinate : Fin n) (rest : List (Fin n)) :
    ClosedBlock (fullBlock formula term rho coordinate rest) := by
  induction rest generalizing rho coordinate with
  | nil => trivial
  | cons next remaining ih => exact ih _ _

theorem fullBlock_boundariesBefore {n width : ℕ} [NeZero width]
    (formula : DNF n) (term : Term n) (rho : PartialAssignment n)
    (coordinate : Fin n) (rest : List (Fin n)) :
    BoundariesBefore 0 ((fullBlock formula term rho coordinate rest).adviceList (widthBound := width)) := by
  induction rest generalizing rho coordinate with
  | nil => exact boundariesBefore_singleton 0 _
  | cons next remaining ih =>
      apply boundariesBefore_cons 0 _ _ (Or.inl rfl)
      exact ih _ _

structure TraceCompletion {n : ℕ} (formula : DNF n) (rho : PartialAssignment n)
    (initial : List (DecisionTree.PathStep n)) (width : ℕ) where
  steps : List (DecisionTree.PathStep n)
  trace : formula.CanonicalTrace rho steps
  closed : ClosedTrace trace
  isPrefix : initial <+: steps
  length_bound : steps.length ≤ initial.length + width

structure BlockCompletion {n : ℕ} (formula : DNF n) (term : Term n)
    (rho : PartialAssignment n) (indices : List (Fin n))
    (initial : List (DecisionTree.PathStep n)) (width : ℕ) where
  steps : List (DecisionTree.PathStep n)
  trace : formula.CanonicalBlockTrace term rho indices steps
  closed : ClosedBlock trace
  isPrefix : initial <+: steps
  length_bound : steps.length ≤ initial.length + width

mutual
def completeTrace {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {initial : List (DecisionTree.PathStep n)} {width : ℕ}
    (trace : formula.CanonicalTrace rho initial) (hwidth : formula.WidthAtMost width) :
    TraceCompletion formula rho initial width :=
  match trace with
  | .nil rho => ⟨[], .nil rho, trivial, List.prefix_refl _, by simp⟩
  | .start (term := term) (indices := indices) found support nonempty block => by
      by_cases hempty : initial = []
      · exact ⟨[], .nil rho, trivial, by simp [hempty], by simp⟩
      have hterm := hwidth term (DNF.firstSurvivingIn_mem rho formula.terms found)
      have hindices : indices.length ≤ width := by
        rw [← support]
        exact (List.length_filter_le _ _).trans ((LiteralSet.length_orderedSupport term).le.trans hterm)
      let completed := completeBlock block hwidth hindices
      exact ⟨completed.steps, .start found support nonempty completed.trace,
        completed.closed, completed.isPrefix, completed.length_bound⟩

def completeBlock {n : ℕ} {formula : DNF n} {term : Term n} {rho : PartialAssignment n}
    {indices : List (Fin n)} {initial : List (DecisionTree.PathStep n)} {width : ℕ}
    (trace : formula.CanonicalBlockTrace term rho indices initial)
    (hwidth : formula.WidthAtMost width) (hindices : indices.length ≤ width) :
    BlockCompletion formula term rho indices initial width :=
  match trace with
  | .nil rho coordinate rest =>
      ⟨falseSteps (coordinate :: rest), fullBlock formula term rho coordinate rest,
        fullBlock_closed formula term rho coordinate rest, by simp,
        by simpa [falseSteps] using hindices⟩
  | .takeMore (index := coordinate) (value := value) tail => by
      let completed := completeBlock tail hwidth (by
        simp only [List.length_cons] at hindices ⊢
        omega)
      refine ⟨⟨coordinate, value⟩ :: completed.steps, .takeMore completed.trace,
        completed.closed, ?_, ?_⟩
      · exact List.cons_prefix_cons.mpr ⟨rfl, completed.isPrefix⟩
      · simpa only [List.length_cons, Nat.add_right_comm] using
          Nat.add_le_add_right completed.length_bound 1
  | .takeLast (index := coordinate) (value := value) tail => by
      let completed := completeTrace tail hwidth
      refine ⟨⟨coordinate, value⟩ :: completed.steps, .takeLast completed.trace,
        completed.closed, ?_, ?_⟩
      · exact List.cons_prefix_cons.mpr ⟨rfl, completed.isPrefix⟩
      · simpa only [List.length_cons, Nat.add_right_comm] using
          Nat.add_le_add_right completed.length_bound 1
end

theorem completeTrace_steps_eq_nil {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {initial : List (DecisionTree.PathStep n)} {width : ℕ}
    (trace : formula.CanonicalTrace rho initial) (hwidth : formula.WidthAtMost width)
    (hempty : initial = []) : (completeTrace trace hwidth).steps = [] := by
  cases trace with
  | nil => rfl
  | start found support nonempty block => simp [completeTrace, hempty]

mutual
theorem completeTrace_boundariesBefore {n width : ℕ} [NeZero width]
    {formula : DNF n} {rho : PartialAssignment n} {initial : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho initial) (hwidth : formula.WidthAtMost width) :
    BoundariesBefore initial.length ((completeTrace trace hwidth).trace.adviceList (widthBound := width)) :=
  match trace with
  | .nil _ => boundariesBefore_nil 0 width
  | .start (steps := steps) found support nonempty block => by
      by_cases hempty : steps = []
      · rw [completeTrace, dif_pos hempty]
        exact boundariesBefore_nil _ _
      · rw [completeTrace, dif_neg hempty]
        change BoundariesBefore steps.length (completeBlock block hwidth _).trace.adviceList
        exact completeBlock_boundariesBefore block hwidth
          (by
            have hterm := hwidth _ (DNF.firstSurvivingIn_mem _ _ found)
            rw [← support]
            exact (List.length_filter_le _ _).trans ((LiteralSet.length_orderedSupport _).le.trans hterm))
termination_by 2 * initial.length + 1
decreasing_by all_goals simp_wf

theorem completeBlock_boundariesBefore {n width : ℕ} [NeZero width]
    {formula : DNF n} {term : Term n} {rho : PartialAssignment n}
    {indices : List (Fin n)} {initial : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices initial)
    (hwidth : formula.WidthAtMost width) (hindices : indices.length ≤ width) :
    BoundariesBefore initial.length
      ((completeBlock trace hwidth hindices).trace.adviceList (widthBound := width)) := by
  cases trace with
  | nil => exact fullBlock_boundariesBefore _ _ _ _ _
  | @takeMore currentTerm state coordinate next rest value steps tail =>
      simp only [completeBlock, DNF.CanonicalBlockTrace.adviceList_takeMore, List.length_cons]
      apply boundariesBefore_cons _ _ _ (Or.inl rfl)
      simpa only [Nat.add_sub_cancel] using completeBlock_boundariesBefore tail hwidth
        (by simp only [List.length_cons] at hindices ⊢; omega)
  | @takeLast currentTerm state coordinate value steps tail =>
      by_cases hempty : steps = []
      · have hzero := completeTrace_steps_eq_nil tail hwidth hempty
        have hadvice : (completeTrace tail hwidth).trace.adviceList (widthBound := width) = [] := by
          have hlength := (completeTrace tail hwidth).trace.length_adviceList (widthBound := width)
          exact List.length_eq_zero_iff.mp (hlength.trans (by
            simpa only [List.length_nil] using congrArg List.length hzero))
        simp only [completeBlock, DNF.CanonicalBlockTrace.adviceList_takeLast, hadvice]
        exact boundariesBefore_singleton _ _
      · simp only [completeBlock, DNF.CanonicalBlockTrace.adviceList_takeLast, List.length_cons]
        apply boundariesBefore_cons _ _ _ (Or.inr (Or.inl (by
          have hpositive := List.length_pos_iff.mpr hempty
          omega)))
        simpa only [Nat.add_sub_cancel] using completeTrace_boundariesBefore tail hwidth
termination_by 2 * initial.length
decreasing_by all_goals (simp_wf; subst_vars; simp_all only [List.length_cons]; omega)
end

/-- A full source-term query block, returning to canonical term selection. -/
def queryTree {n : ℕ} (formula : DNF n) : List (Fin n) → PartialAssignment n → DecisionTree n
  | [], rho => formula.canonicalDecisionTree rho
  | coordinate :: rest, rho => .query coordinate
      (queryTree formula rest (rho.refine (PartialAssignment.fix coordinate false)))
      (queryTree formula rest (rho.refine (PartialAssignment.fix coordinate true)))

theorem queryRemainingBelow_eq_queryTree {n : ℕ} (formula : DNF n)
    (indices : List (Fin n)) (rho : PartialAssignment n) (bound : ℕ)
    (hbelow : rho.liveCount < bound) :
    DNF.queryRemainingBelow indices rho bound hbelow
      (fun sigma _ => formula.canonicalDecisionTree sigma) = queryTree formula indices rho := by
  induction indices generalizing rho with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [DNF.queryRemainingBelow, queryTree]
      rw [ih, ih]

theorem canonical_eq_queryTree_of_found {n : ℕ} (formula : DNF n)
    (rho : PartialAssignment n) (term : Term n) (indices : List (Fin n))
    (hfound : formula.firstSurviving rho = some term)
    (hsupport : DNF.liveSupport term rho = indices) (hnonempty : indices ≠ []) :
    formula.canonicalDecisionTree rho = queryTree formula indices rho := by
  rw [DNF.canonicalDecisionTree.eq_def]
  simp only [DNF.canonicalDecisionTreeStep, hfound]
  have hquery (indices : List (Fin n))
      (allLive : ∀ index, index ∈ indices → rho index = none) (hnotnil : indices ≠ []) :
      DNF.canonicalSupportStep formula rho
        (fun sigma _ => formula.canonicalDecisionTree sigma) indices allLive =
        queryTree formula indices rho := by
    cases indices with
    | nil => exact False.elim (hnotnil rfl)
    | cons coordinate rest =>
        simp only [DNF.canonicalSupportStep, queryTree]
        rw [queryRemainingBelow_eq_queryTree, queryRemainingBelow_eq_queryTree]
  rw [hquery _ _ (by simpa only [hsupport] using hnonempty), hsupport]

mutual
theorem closedTrace_path {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)} (trace : formula.CanonicalTrace rho steps)
    (hclosed : ClosedTrace trace) :
    DecisionTree.Path (formula.canonicalDecisionTree rho) steps
      (formula.canonicalDecisionTree (rho.refine (DecisionTree.PathStep.assignment steps))) := by
  cases trace with
  | nil => simpa using DecisionTree.Path.nil (formula.canonicalDecisionTree rho)
  | start found support nonempty block =>
      rw [canonical_eq_queryTree_of_found formula rho _ _ found support nonempty]
      exact closedBlock_path block hclosed

theorem closedBlock_path {n : ℕ} {formula : DNF n} {term : Term n} {rho : PartialAssignment n}
    {indices : List (Fin n)} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) (hclosed : ClosedBlock trace) :
    DecisionTree.Path (queryTree formula indices rho) steps
      (formula.canonicalDecisionTree (rho.refine (DecisionTree.PathStep.assignment steps))) := by
  cases trace with
  | nil => exact False.elim hclosed
  | @takeMore currentTerm state coordinate next rest value steps tail =>
      have h := closedBlock_path tail hclosed
      rw [DecisionTree.PathStep.assignment_cons, ← PartialAssignment.refine_assoc]
      cases value with
      | false => exact .takeFalse h
      | true => exact .takeTrue h
  | @takeLast currentTerm state coordinate value steps tail =>
      have h := closedTrace_path tail hclosed
      rw [DecisionTree.PathStep.assignment_cons, ← PartialAssignment.refine_assoc]
      cases value with
      | false => exact .takeFalse h
      | true => exact .takeTrue h
end

/-- A deep canonical tree has a phase prefix of the requested minimum length,
completed at a term boundary with at most `width` extra queries.
-/
theorem exists_closed_phase {n : ℕ} (formula : DNF n) (rho : PartialAssignment n)
    (minimum width : ℕ) (hwidth : formula.WidthAtMost width)
    (hdeep : formula.CanonicalDepthAtLeast rho minimum) :
    ∃ steps : List (DecisionTree.PathStep n),
      ∃ trace : formula.CanonicalTrace rho steps,
        ClosedTrace trace ∧ minimum ≤ steps.length ∧ steps.length ≤ minimum + width := by
  obtain ⟨path⟩ := formula.exists_canonicalPath rho minimum hdeep
  obtain ⟨trace⟩ := formula.canonicalTrace_of_path rho path.follows
  let completed := completeTrace trace hwidth
  refine ⟨completed.steps, completed.trace, completed.closed, ?_, ?_⟩
  · simpa only [path.length_steps] using completed.isPrefix.length_le
  · simpa only [path.length_steps] using completed.length_bound

/-- A phase is an actual canonical path ending at a completed source-term block. -/
structure Phase {n : ℕ} (formula : DNF n) (rho : PartialAssignment n)
    (minimum width : ℕ) where
  steps : List (DecisionTree.PathStep n)
  trace : formula.CanonicalTrace rho steps
  closed : ClosedTrace trace
  minimum_length : minimum ≤ steps.length
  maximum_length : steps.length ≤ minimum + width

structure BoundaryPhase {n width : ℕ} [NeZero width] (formula : DNF n)
    (rho : PartialAssignment n) (minimum : ℕ) extends Phase formula rho minimum width where
  boundaries : BoundariesBefore minimum (trace.adviceList (widthBound := width))

theorem exists_boundaryPhase {n width : ℕ} [NeZero width]
    (formula : DNF n) (rho : PartialAssignment n) (minimum : ℕ)
    (hwidth : formula.WidthAtMost width) (hdeep : formula.CanonicalDepthAtLeast rho minimum) :
    Nonempty (BoundaryPhase (width := width) formula rho minimum) := by
  obtain ⟨path⟩ := formula.exists_canonicalPath rho minimum hdeep
  obtain ⟨trace⟩ := formula.canonicalTrace_of_path rho path.follows
  let completed := completeTrace trace hwidth
  refine ⟨⟨⟨completed.steps, completed.trace, completed.closed, ?_, ?_⟩, ?_⟩⟩
  · simpa only [path.length_steps] using completed.isPrefix.length_le
  · simpa only [path.length_steps] using completed.length_bound
  · simpa only [path.length_steps] using completeTrace_boundariesBefore trace hwidth

theorem exists_phase {n : ℕ} (formula : DNF n) (rho : PartialAssignment n)
    (minimum width : ℕ) (hwidth : formula.WidthAtMost width)
    (hdeep : formula.CanonicalDepthAtLeast rho minimum) :
    Nonempty (Phase formula rho minimum width) := by
  obtain ⟨steps, trace, hclosed, hmin, hmax⟩ :=
    exists_closed_phase formula rho minimum width hwidth hdeep
  exact ⟨⟨steps, trace, hclosed, hmin, hmax⟩⟩

def Phase.toCanonicalPath {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {minimum width : ℕ} (phase : Phase formula rho minimum width) :
    formula.CanonicalPath rho phase.steps.length :=
  ⟨phase.steps, formula.canonicalDecisionTree (rho.refine (DecisionTree.PathStep.assignment phase.steps)),
    closedTrace_path phase.trace phase.closed, rfl⟩

theorem Phase.indices_nodup {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {minimum width : ℕ} (phase : Phase formula rho minimum width) :
    (DecisionTree.PathStep.indices phase.steps).Nodup :=
  phase.toCanonicalPath.indices_nodup

theorem Phase.indices_subset_live {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {minimum width : ℕ} (phase : Phase formula rho minimum width) :
    (DecisionTree.PathStep.indices phase.steps).toFinset ⊆ rho.liveVariables :=
  phase.toCanonicalPath.indices_subset_live

theorem Phase.length_le_canonicalDepth {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {minimum width : ℕ} (phase : Phase formula rho minimum width) :
    phase.steps.length ≤ formula.canonicalDepth rho := by
  have h := (closedTrace_path phase.trace phase.closed).length_add_endpoint_depth_le
  unfold DNF.canonicalDepth
  omega

end TalCanonicalCompletion
