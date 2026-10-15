import TalCanonicalCompletion
import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalEncoding

/-!
# Recovering phase boundaries from query advice

The splitter reads only the minimum phase length and the ordinary source-term
boundary bits reconstructed by the sorted-block packer. No hidden phase
lengths or coordinates are inputs.
-/

namespace TalPhaseSplit
open Algebraic AC0 Switching TalCanonicalCompletion

def splitPhase {width : ℕ} (minimum : ℕ) : ℕ → List (QueryAdvice width) →
    List (QueryAdvice width) × List (QueryAdvice width)
  | _, [] => ([], [])
  | consumed, symbol :: rest =>
      if symbol.closesBlock && decide (minimum ≤ consumed + 1) then ([symbol], rest)
      else
        let tail := splitPhase minimum (consumed + 1) rest
        (symbol :: tail.1, tail.2)

def ShiftedBoundariesBefore {width : ℕ} (minimum consumed : ℕ) (advice : List (QueryAdvice width)) : Prop :=
  ∀ index (hindex : index + 1 < advice.length), minimum ≤ consumed + index + 1 →
    (advice[index]'(by omega)).closesBlock = false

theorem splitPhase_append_closed {width : ℕ} (minimum consumed : ℕ)
    (first rest : List (QueryAdvice width)) (hnonempty : first ≠ [])
    (hbefore : ShiftedBoundariesBefore minimum consumed first)
    (hlast : first.getLast?.map QueryAdvice.closesBlock = some true)
    (hminimum : minimum ≤ consumed + first.length) :
    splitPhase minimum consumed (first ++ rest) = (first, rest) := by
  induction first generalizing consumed with
  | nil => exact False.elim (hnonempty rfl)
  | cons symbol tail ih =>
      cases tail with
      | nil =>
          have hclose : symbol.closesBlock = true := by simpa using hlast
          have hmin : minimum ≤ consumed + 1 := by simpa using hminimum
          simp [splitPhase, hclose, hmin]
      | cons next remaining =>
          have hhead : (symbol.closesBlock && decide (minimum ≤ consumed + 1)) = false := by
            by_cases hmin : minimum ≤ consumed + 1
            · have hfalse := hbefore 0 (by simp) (by simpa using hmin)
              have hfalse' : symbol.closesBlock = false := by simpa only [List.getElem_cons_zero] using hfalse
              simp [hfalse']
            · simp [hmin]
          have htailBefore : ShiftedBoundariesBefore minimum (consumed + 1) (next :: remaining) := by
            intro index hindex hmin
            have h := hbefore (index + 1) (by simp only [List.length_cons] at hindex ⊢; omega)
              (by omega)
            simpa only [List.getElem_cons_succ] using h
          have htailLast : (next :: remaining).getLast?.map QueryAdvice.closesBlock = some true := by
            simpa only [List.getLast?_cons_cons] using hlast
          have htailMin : minimum ≤ (consumed + 1) + (next :: remaining).length := by
            simp only [List.length_cons] at hminimum ⊢
            omega
          have hsplit := ih (consumed + 1) (by simp) htailBefore htailLast htailMin
          rw [List.cons_append, splitPhase]
          simp only [hhead, Bool.false_eq_true, if_false]
          rw [hsplit]

def EndsClosed {width : ℕ} (advice : List (QueryAdvice width)) : Prop :=
  ∃ initial symbol, advice = initial ++ [symbol] ∧ symbol.closesBlock = true

/-- With the last marker erased, a recoverable final phase consumes the entire remainder. -/
theorem splitPhase_clearLastClose {width : ℕ} (minimum consumed : ℕ)
    (advice : List (QueryAdvice width)) (hbefore : ShiftedBoundariesBefore minimum consumed advice) :
    splitPhase minimum consumed (clearLastClose advice) = (clearLastClose advice, []) := by
  induction advice generalizing consumed with
  | nil => rfl
  | cons symbol tail ih =>
      cases tail with
      | nil => simp [clearLastClose, QueryAdvice.withoutClose, splitPhase]
      | cons next remaining =>
          have hhead : (symbol.closesBlock && decide (minimum ≤ consumed + 1)) = false := by
            by_cases hmin : minimum ≤ consumed + 1
            · have hfalse := hbefore 0 (by simp) (by simpa using hmin)
              have hfalse' : symbol.closesBlock = false := by simpa only [List.getElem_cons_zero] using hfalse
              simp [hfalse']
            · simp [hmin]
          have htail : ShiftedBoundariesBefore minimum (consumed + 1) (next :: remaining) := by
            intro index hindex hmin
            have h := hbefore (index + 1) (by simp only [List.length_cons] at hindex ⊢; omega)
              (by omega)
            simpa only [List.getElem_cons_succ] using h
          rw [clearLastClose, splitPhase]
          simp only [hhead, Bool.false_eq_true, if_false]
          rw [ih (consumed + 1) htail]

mutual
theorem closedTrace_endsClosed {n width : ℕ} [NeZero width] {formula : DNF n}
    {rho : PartialAssignment n} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) (hclosed : ClosedTrace trace) :
    trace.adviceList (widthBound := width) = [] ∨ EndsClosed (trace.adviceList (widthBound := width)) :=
  match trace with
  | .nil _ => Or.inl rfl
  | .start _ _ _ block => Or.inr (closedBlock_endsClosed block hclosed)
termination_by 2 * steps.length + 1
decreasing_by all_goals simp_wf

theorem closedBlock_endsClosed {n width : ℕ} [NeZero width] {formula : DNF n}
    {term : Term n} {rho : PartialAssignment n} {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)} (trace : formula.CanonicalBlockTrace term rho indices steps)
    (hclosed : ClosedBlock trace) : EndsClosed (trace.adviceList (widthBound := width)) := by
  cases trace with
  | nil => exact False.elim hclosed
  | @takeMore currentTerm state coordinate next rest value steps tail =>
      obtain ⟨initial, symbol, heq, hclose⟩ := closedBlock_endsClosed (width := width) tail hclosed
      rw [DNF.CanonicalBlockTrace.adviceList_takeMore, heq]
      refine ⟨_ :: initial, symbol, rfl, hclose⟩
  | @takeLast currentTerm state coordinate value steps tail =>
      have hend := closedTrace_endsClosed (width := width) tail hclosed
      rw [DNF.CanonicalBlockTrace.adviceList_takeLast]
      rcases hend with hempty | ⟨initial, symbol, heq, hclose⟩
      · rw [hempty]
        exact ⟨[], _, rfl, rfl⟩
      · rw [heq]
        exact ⟨_ :: initial, symbol, rfl, hclose⟩
termination_by 2 * steps.length
decreasing_by all_goals (simp_wf; subst_vars; simp_all only [List.length_cons]; omega)
end

theorem boundaryPhase_split {n width : ℕ} [NeZero width] {formula : DNF n}
    {rho : PartialAssignment n} {minimum : ℕ}
    (phase : BoundaryPhase (width := width) formula rho minimum) (hpositive : 0 < minimum)
    (rest : List (QueryAdvice width)) :
    splitPhase minimum 0 (phase.trace.adviceList (widthBound := width) ++ rest) =
      (phase.trace.adviceList (widthBound := width), rest) := by
  have hlength := phase.trace.length_adviceList (widthBound := width)
  have hnonempty : phase.trace.adviceList (widthBound := width) ≠ [] := by
    intro hempty
    have hmin := phase.minimum_length
    simp only [hempty, List.length_nil] at hlength
    omega
  have hend := closedTrace_endsClosed (width := width) phase.trace phase.closed
  rcases hend with hempty | ⟨initial, symbol, heq, hclose⟩
  · exact False.elim (hnonempty hempty)
  · apply splitPhase_append_closed minimum 0 _ rest hnonempty
    · simpa only [ShiftedBoundariesBefore, Nat.zero_add] using phase.boundaries
    · rw [heq]
      simp [hclose]
    · simpa only [Nat.zero_add, hlength] using phase.minimum_length

end TalPhaseSplit
