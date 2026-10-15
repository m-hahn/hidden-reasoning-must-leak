import TalCanonicalCompletion

/-!
# Prefixes of actual canonical traces

The final family phase is truncated from the same completed phase used in
the witness construction. This preserves its recoverable boundary invariant,
rather than choosing an unrelated canonical path of the desired length.
-/

namespace TalTracePrefix
open Algebraic AC0 TalCanonicalCompletion

mutual
def takeTrace {n : ℕ} {formula : DNF n} {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)} (trace : formula.CanonicalTrace rho steps)
    (count : ℕ) : formula.CanonicalTrace rho (steps.take count) :=
  match count, trace with
  | 0, _ => .nil rho
  | _ + 1, .nil rho => .nil rho
  | count + 1, .start found support nonempty block =>
      .start found support nonempty (takeBlock block (count + 1))

def takeBlock {n : ℕ} {formula : DNF n} {term : Term n} {rho : PartialAssignment n}
    {indices : List (Fin n)} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) (count : ℕ) :
    formula.CanonicalBlockTrace term rho indices (steps.take count) :=
  match count, trace with
  | 0, .nil rho index rest => .nil rho index rest
  | 0, .takeMore (rho := rho) (index := index) (next := next) (rest := rest) _ => .nil rho index (next :: rest)
  | 0, .takeLast (rho := rho) (index := index) _ => .nil rho index []
  | _ + 1, .nil rho index rest => .nil rho index rest
  | count + 1, .takeMore tail => .takeMore (takeBlock tail count)
  | count + 1, .takeLast tail => .takeLast (takeTrace tail count)
end

mutual
theorem takeTrace_advice {n width : ℕ} [NeZero width] {formula : DNF n} {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)} (trace : formula.CanonicalTrace rho steps) (count : ℕ) :
    (takeTrace trace count).adviceList (widthBound := width) =
      (trace.adviceList (widthBound := width)).take count := by
  cases count with
  | zero => simp [takeTrace, DNF.CanonicalTrace.adviceList, DNF.CanonicalTrace.queryRecords]
  | succ count =>
      cases trace with
      | nil => rfl
      | start found support nonempty block =>
          simp only [takeTrace, DNF.CanonicalTrace.adviceList_start]
          exact takeBlock_advice block (count + 1)
termination_by 2 * steps.length + 1
decreasing_by all_goals (simp_wf; subst_vars; simp_all only [List.length_cons]; omega)

theorem takeBlock_advice {n width : ℕ} [NeZero width] {formula : DNF n}
    {term : Term n} {rho : PartialAssignment n} {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)} (trace : formula.CanonicalBlockTrace term rho indices steps) (count : ℕ) :
    (takeBlock trace count).adviceList (widthBound := width) =
      (trace.adviceList (widthBound := width)).take count := by
  cases count with
  | zero => cases trace <;> rfl
  | succ count =>
      cases trace with
      | nil => rfl
      | takeMore tail =>
          simp only [takeBlock, DNF.CanonicalBlockTrace.adviceList_takeMore, List.take_succ_cons]
          rw [takeBlock_advice tail count]
      | takeLast tail =>
          simp only [takeBlock, DNF.CanonicalBlockTrace.adviceList_takeLast, List.take_succ_cons]
          rw [takeTrace_advice tail count]
termination_by 2 * steps.length
decreasing_by all_goals (simp_wf <;> subst_vars <;> simp_all only [List.length_cons] <;> omega)
end

theorem boundariesBefore_take {width : ℕ} {minimum : ℕ} {advice : List (Switching.QueryAdvice width)}
    (hbefore : BoundariesBefore minimum advice) (count : ℕ) :
    BoundariesBefore minimum (advice.take count) := by
  intro index hindex hminimum
  have hindex' : index + 1 < advice.length := hindex.trans_le (List.length_take_le' _ _)
  simpa only [List.getElem_take] using hbefore index hindex' hminimum

theorem path_take {n : ℕ} {tree endpoint : DecisionTree n} {steps : List (DecisionTree.PathStep n)}
    (path : DecisionTree.Path tree steps endpoint) (count : ℕ) :
    ∃ endpoint', DecisionTree.Path tree (steps.take count) endpoint' := by
  induction path generalizing count with
  | nil tree => exact ⟨tree, by simpa using DecisionTree.Path.nil tree⟩
  | takeFalse tail ih =>
      cases count with
      | zero => exact ⟨_, .nil _⟩
      | succ count =>
          obtain ⟨endpoint', hpath⟩ := ih count
          exact ⟨endpoint', .takeFalse hpath⟩
  | takeTrue tail ih =>
      cases count with
      | zero => exact ⟨_, .nil _⟩
      | succ count =>
          obtain ⟨endpoint', hpath⟩ := ih count
          exact ⟨endpoint', .takeTrue hpath⟩

theorem phase_prefix {n width : ℕ} [NeZero width] {formula : DNF n} {rho : PartialAssignment n}
    {minimum : ℕ} (phase : BoundaryPhase (width := width) formula rho minimum)
    (count : ℕ) (hcount : count ≤ phase.steps.length) :
    ∃ path : formula.CanonicalPath rho count,
      ∃ trace : formula.CanonicalTrace rho path.steps,
        BoundariesBefore minimum (trace.adviceList (widthBound := width)) := by
  obtain ⟨endpoint, hpath⟩ := path_take phase.toPhase.toCanonicalPath.follows count
  have hlength : (phase.steps.take count).length = count := by simp [List.length_take, hcount]
  let path : formula.CanonicalPath rho count := ⟨phase.steps.take count, endpoint, hpath, hlength⟩
  refine ⟨path, takeTrace phase.trace count, ?_⟩
  rw [takeTrace_advice]
  exact boundariesBefore_take phase.boundaries count

end TalTracePrefix
