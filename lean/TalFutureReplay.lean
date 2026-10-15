import TalCanonicalCompletion

/-!
# Later breadcrumbs and closed canonical phases

A later phase cannot assign an already-queried coordinate. Completing each
current term block therefore prevents later satisfying breadcrumbs from
changing the source-term selector used during replay.
-/

namespace TalFutureReplay
open Algebraic AC0 TalCanonicalCompletion

theorem closedBlock_pending_subset {n : ℕ} {formula : DNF n} {term : Term n}
    {rho : PartialAssignment n} {indices : List (Fin n)} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) (hclosed : ClosedBlock trace) :
    ∀ index ∈ indices, index ∈ DecisionTree.PathStep.indices steps := by
  cases trace with
  | nil => exact False.elim hclosed
  | @takeMore currentTerm state coordinate next rest value steps tail =>
      intro index hindex
      simp only [List.mem_cons] at hindex
      rcases hindex with rfl | htail
      · simp [DecisionTree.PathStep.indices]
      · have h := closedBlock_pending_subset tail hclosed index (List.mem_cons.mpr htail)
        simpa only [DecisionTree.PathStep.indices, List.map_cons, List.mem_cons] using Or.inr h
  | @takeLast currentTerm state coordinate value steps tail =>
      intro index hindex
      have heq : index = coordinate := by simpa using hindex
      subst index
      simp [DecisionTree.PathStep.indices]
termination_by steps.length
decreasing_by all_goals (simp_wf; subst_vars; simp_all only [List.length_cons]; omega)

theorem closedBlock_compatible_future {n width : ℕ} [NeZero width]
    {formula : DNF n} {term : Term n} {rho : PartialAssignment n}
    {indices : List (Fin n)} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) (hclosed : ClosedBlock trace)
    (hnodup : indices.Nodup) (future : PartialAssignment n)
    (hfuture : ∀ index ∈ DecisionTree.PathStep.indices steps, future index = none) :
    ∀ index ∈ indices,
      (trace.satisfyingAssignment (widthBound := width)).refine future index = none ∨
      (trace.satisfyingAssignment (widthBound := width)).refine future index =
        some (term.satisfyingValue index) := by
  intro index hindex
  have hf := hfuture index (closedBlock_pending_subset trace hclosed index hindex)
  have hcompatible := trace.satisfyingAssignment_compatible (widthBound := width) hnodup index hindex
  rcases hcompatible with hnone | hsome
  · left
    simp [PartialAssignment.refine, hnone, hf]
  · right
    simp [PartialAssignment.refine, hsome]

theorem closedTrace_firstSurviving_future {n width : ℕ} [NeZero width]
    {formula : DNF n} {rho : PartialAssignment n} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) (hclosed : ClosedTrace trace)
    (hnonempty : steps ≠ []) (future : PartialAssignment n)
    (hfuture : ∀ index ∈ DecisionTree.PathStep.indices steps, future index = none)
    {term : Term n} (hfound : formula.firstSurviving rho = some term) :
    formula.firstSurviving (rho.refine
      ((trace.satisfyingAssignment (widthBound := width)).refine future)) = some term := by
  cases trace with
  | nil => exact False.elim (hnonempty rfl)
  | @start state selected indices steps found support nonempty block =>
      have heq : term = selected := by
        rw [found] at hfound
        exact (Option.some.inj hfound).symm
      subst term
      have hnoConflict := DNF.firstSurvivingIn_not_conflicts rho formula.terms found
      apply formula.firstSurviving_refine rho _ found
      apply selected.not_conflicts_refine_of_satisfying_on_liveSupport rho _ hnoConflict
      intro index hindex
      apply closedBlock_compatible_future block hclosed
        (by rw [← support]; exact DNF.nodup_liveSupport selected rho) future hfuture
      simpa only [support] using hindex

open LiteralSet

mutual
theorem closedTrace_replay_future {n width : ℕ} [NeZero width]
    {formula : DNF n} {rho : PartialAssignment n} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) (hclosed : ClosedTrace trace)
    (hwidth : formula.WidthAtMost width) (future : PartialAssignment n)
    (hfuture : ∀ index ∈ DecisionTree.PathStep.indices steps, future index = none) :
    Switching.replayIndices formula
      (rho.refine ((trace.satisfyingAssignment (widthBound := width)).refine future)) none
      (trace.adviceList (widthBound := width)) = DecisionTree.PathStep.indices steps :=
  match trace with
  | .nil _ => rfl
  | .start (term := term) (indices := indices) found support nonempty block => by
      let currentTrace := DNF.CanonicalTrace.start found support nonempty block
      by_cases hempty : steps = []
      · have hadvice : currentTrace.adviceList (widthBound := width) = [] := by
          exact List.length_eq_zero_iff.mp (currentTrace.length_adviceList.trans (by simp [hempty]))
        rw [hadvice]
        simp [Switching.replayIndices, DecisionTree.PathStep.indices, hempty]
      · have hselector := closedTrace_firstSurviving_future (width := width)
          currentTrace hclosed hempty future hfuture found
        rw [Switching.replayIndices_none_eq_some_of_firstSurviving formula _ term hselector]
        exact closedBlock_replay_future block hclosed hwidth
          (hwidth term (DNF.firstSurvivingIn_mem _ _ found)) support future hfuture
termination_by 2 * steps.length + 1
decreasing_by all_goals simp_wf

theorem closedBlock_replay_future {n width : ℕ} [NeZero width]
    {formula : DNF n} {term : Term n} {rho : PartialAssignment n}
    {indices : List (Fin n)} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) (hclosed : ClosedBlock trace)
    (hwidth : formula.WidthAtMost width) (hterm : term.width ≤ width)
    (hsupport : DNF.liveSupport term rho = indices) (future : PartialAssignment n)
    (hfuture : ∀ index ∈ DecisionTree.PathStep.indices steps, future index = none) :
    Switching.replayIndices formula
      (rho.refine ((trace.satisfyingAssignment (widthBound := width)).refine future)) (some term)
      (trace.adviceList (widthBound := width)) = DecisionTree.PathStep.indices steps := by
  cases trace with
  | nil => exact False.elim hclosed
  | @takeMore currentTerm state coordinate next rest value steps tail =>
      have hdata := (DNF.mem_liveSupport term rho coordinate).mp (by rw [hsupport]; simp)
      have hdecode := term.getElem?_sourcePosition_of_mem_support coordinate hterm hdata.1
      have hstate := PartialAssignment.fix_refine_refine_fix rho
        ((tail.satisfyingAssignment (widthBound := width)).refine future)
        coordinate value (term.satisfyingValue coordinate) hdata.2
      have htailSupport := DNF.liveSupport_refine_fix_eq_tail term rho coordinate (next :: rest) value hsupport
      have htailFuture : ∀ index ∈ DecisionTree.PathStep.indices steps, future index = none := by
        intro index hindex
        apply hfuture index
        simpa only [DecisionTree.PathStep.indices, List.map_cons, List.mem_cons] using Or.inr hindex
      have htail := closedBlock_replay_future tail hclosed hwidth hterm htailSupport future htailFuture
      rw [DNF.CanonicalBlockTrace.satisfyingAssignment_takeMore,
        PartialAssignment.refine_assoc, DNF.CanonicalBlockTrace.adviceList_takeMore]
      simp only [Switching.replayIndices, Switching.selectTerm]
      rw [hdecode]
      simp only [Bool.false_eq_true, if_false]
      rw [Switching.QueryAdvice.decodeValue_mk_xor, hstate]
      simpa [DecisionTree.PathStep.indices] using congrArg (List.cons coordinate) htail
  | @takeLast currentTerm state coordinate value steps tail =>
      have hdata := (DNF.mem_liveSupport term rho coordinate).mp (by rw [hsupport]; simp)
      have hdecode := term.getElem?_sourcePosition_of_mem_support coordinate hterm hdata.1
      have hstate := PartialAssignment.fix_refine_refine_fix rho
        ((tail.satisfyingAssignment (widthBound := width)).refine future)
        coordinate value (term.satisfyingValue coordinate) hdata.2
      have htailFuture : ∀ index ∈ DecisionTree.PathStep.indices steps, future index = none := by
        intro index hindex
        apply hfuture index
        simpa only [DecisionTree.PathStep.indices, List.map_cons, List.mem_cons] using Or.inr hindex
      have htail := closedTrace_replay_future tail hclosed hwidth future htailFuture
      rw [DNF.CanonicalBlockTrace.satisfyingAssignment_takeLast,
        PartialAssignment.refine_assoc, DNF.CanonicalBlockTrace.adviceList_takeLast]
      simp only [Switching.replayIndices, Switching.selectTerm]
      rw [hdecode]
      simp only [if_true]
      rw [Switching.QueryAdvice.decodeValue_mk_xor, hstate]
      simpa [DecisionTree.PathStep.indices] using congrArg (List.cons coordinate) htail
termination_by 2 * steps.length
decreasing_by all_goals (simp_wf; subst_vars; simp only [List.length_cons]; omega)
end

end TalFutureReplay
