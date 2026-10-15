import TalFamilyEncoder
import TalFamilyDecoder
import TalFutureReplay

/-!
# Exact state changes between decoded family phases

These identities prove that actual later-witness assignments satisfy the
future-replay invariant and that the decoder's global-answer overwrite
produces precisely the next witness frame.
-/

namespace TalFamilyFrames
open Algebraic AC0 Switching TalCanonicalCompletion TalFamilyWitness

theorem assignment_append {n : ℕ} (first rest : List (DecisionTree.PathStep n)) :
    DecisionTree.PathStep.assignment (first ++ rest) =
      (DecisionTree.PathStep.assignment first).refine (DecisionTree.PathStep.assignment rest) := by
  induction first with
  | nil => simp [DecisionTree.PathStep.assignment]
  | cons step first ih =>
      simp only [List.cons_append, DecisionTree.PathStep.assignment_cons, ih, PartialAssignment.refine_assoc]

theorem overwrite_refinement {n : ℕ} (rho satisfying global future : PartialAssignment n)
    (hnew : satisfying.fixedVariables ⊆ rho.liveVariables)
    (hsame : global.fixedVariables = satisfying.fixedVariables) :
    global.refine (rho.refine (satisfying.refine future)) = (rho.refine global).refine future := by
  apply PartialAssignment.ext
  intro index
  cases hglobal : global index with
  | none =>
      have hsatisfying : satisfying index = none := by
        by_contra h
        have hfixed : index ∈ satisfying.fixedVariables := (PartialAssignment.mem_fixedVariables _ _).mpr h
        rw [← hsame] at hfixed
        have hglobalFixed := (PartialAssignment.mem_fixedVariables _ _).mp hfixed
        exact hglobalFixed hglobal
      cases hrho : rho index <;> simp [PartialAssignment.refine, hglobal, hsatisfying, hrho]
  | some value =>
      have hfixed : index ∈ satisfying.fixedVariables := by
        rw [← hsame]
        simp [hglobal]
      have hlive := (PartialAssignment.mem_liveVariables _ _).mp (hnew hfixed)
      simp [PartialAssignment.refine, hglobal, hlive]

theorem answerAssignment_of_steps {n : ℕ} (steps : List (DecisionTree.PathStep n)) :
    TalFamilyDecoder.answerAssignment (DecisionTree.PathStep.indices steps)
      (steps.map DecisionTree.PathStep.value) = DecisionTree.PathStep.assignment steps := by
  have hlist : ((steps.map DecisionTree.PathStep.index).zip (steps.map DecisionTree.PathStep.value)).map
      (fun pair => (⟨pair.1, pair.2⟩ : DecisionTree.PathStep n)) = steps := by
    induction steps with
    | nil => rfl
    | cons step rest ih =>
        simp only [List.map_cons, List.zip_cons_cons]
        rw [ih]
  unfold TalFamilyDecoder.answerAssignment DecisionTree.PathStep.indices
  rw [hlist]

theorem tail_extension_none_on_phase {n m width : ℕ} [NeZero width]
    {family : Fin m → DNF n} {shallow : ℕ} {rho : PartialAssignment n} {remaining : ℕ}
    (index : Fin m) (phase : Phase (family index) rho (shallow + 1) width)
    (global : List (DecisionTree.PathStep n))
    (hsame : DecisionTree.PathStep.indices global = DecisionTree.PathStep.indices phase.steps)
    (tail : Witness family shallow width (rho.refine (DecisionTree.PathStep.assignment global)) remaining) :
    ∀ coordinate ∈ DecisionTree.PathStep.indices phase.steps, tail.extension coordinate = none := by
  intro coordinate hcoordinate
  have hfixed : coordinate ∈ (DecisionTree.PathStep.assignment global).fixedVariables := by
    rw [DecisionTree.PathStep.fixedVariables_assignment, hsame]
    exact List.mem_toFinset.mpr hcoordinate
  by_contra hfuture
  have hfutureFixed : coordinate ∈ tail.extension.fixedVariables :=
    (PartialAssignment.mem_fixedVariables _ _).mpr hfuture
  have hlive := tail.extension_fixesOnlyLive hfutureFixed
  rw [PartialAssignment.liveVariables_refine] at hlive
  exact (PartialAssignment.mem_fixedVariables _ _).mp hfixed
    ((PartialAssignment.mem_liveVariables _ _).mp (Finset.mem_inter.mp hlive).2)

theorem extension_step {n m width : ℕ} [NeZero width]
    {family : Fin m → DNF n} {shallow : ℕ} {rho : PartialAssignment n} {remaining : ℕ}
    (index : Fin m) (phase : Phase (family index) rho (shallow + 1) width)
    (global : List (DecisionTree.PathStep n))
    (hsame : DecisionTree.PathStep.indices global = DecisionTree.PathStep.indices phase.steps)
    (tail : Witness family shallow width (rho.refine (DecisionTree.PathStep.assignment global)) remaining) :
    (Witness.step index phase global hsame tail).extension =
      (phase.trace.satisfyingAssignment (widthBound := width)).refine tail.extension := by
  exact assignment_append _ _

theorem global_phase_length {n : ℕ} (global localSteps : List (DecisionTree.PathStep n))
    (hsame : DecisionTree.PathStep.indices global = DecisionTree.PathStep.indices localSteps) :
    global.length = localSteps.length := by
  simpa only [DecisionTree.PathStep.indices, List.length_map] using congrArg List.length hsame

theorem replay_phase {n m width : ℕ} [NeZero width]
    {family : Fin m → DNF n} {shallow : ℕ} {rho : PartialAssignment n} {remaining : ℕ}
    (index : Fin m) (phase : Phase (family index) rho (shallow + 1) width)
    (global : List (DecisionTree.PathStep n))
    (hsame : DecisionTree.PathStep.indices global = DecisionTree.PathStep.indices phase.steps)
    (tail : Witness family shallow width (rho.refine (DecisionTree.PathStep.assignment global)) remaining)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    replayIndices (family index)
      (rho.refine ((phase.trace.satisfyingAssignment (widthBound := width)).refine tail.extension)) none
      (phase.trace.adviceList (widthBound := width)) = DecisionTree.PathStep.indices phase.steps :=
  TalFutureReplay.closedTrace_replay_future phase.trace phase.closed (hwidth index) tail.extension
    (tail_extension_none_on_phase index phase global hsame tail)

theorem reset_phase {n m width : ℕ} [NeZero width]
    {family : Fin m → DNF n} {shallow : ℕ} {rho : PartialAssignment n} {remaining : ℕ}
    (index : Fin m) (phase : Phase (family index) rho (shallow + 1) width)
    (global : List (DecisionTree.PathStep n))
    (hsame : DecisionTree.PathStep.indices global = DecisionTree.PathStep.indices phase.steps)
    (tail : Witness family shallow width (rho.refine (DecisionTree.PathStep.assignment global)) remaining) :
    (TalFamilyDecoder.answerAssignment (DecisionTree.PathStep.indices phase.steps)
      (global.map DecisionTree.PathStep.value)).refine
        (rho.refine ((phase.trace.satisfyingAssignment (widthBound := width)).refine tail.extension)) =
      (rho.refine (DecisionTree.PathStep.assignment global)).refine tail.extension := by
  rw [← hsame, answerAssignment_of_steps]
  apply overwrite_refinement rho _ _ tail.extension
  · exact phase.toCanonicalPath.satisfyingAssignment_fixesOnlyLive phase.trace
  · rw [phase.trace.satisfyingAssignment_fixedVariables,
      DecisionTree.PathStep.fixedVariables_assignment,
      DecisionTree.PathStep.fixedVariables_assignment, hsame]

end TalFamilyFrames
