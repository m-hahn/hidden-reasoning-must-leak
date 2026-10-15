import TalFamilyFrames
import TalFamilyTranscript
import TalPhaseSplit

/-!
# Reconstruction of recoverable family witnesses

The decoder uses only the finite advice. Its phase-by-phase invariant is
proved for witnesses constructed from the genuine common-tree bad event.
-/

namespace TalFamilyDecoding
open Algebraic AC0 Switching TalCanonicalCompletion TalFamilyWitness TalFamilyFrames TalPhaseSplit

theorem run_nilAdvice {n m width : ℕ} (family : Fin m → DNF n) (minimum fuel : ℕ)
    (state : PartialAssignment n) (members : List (Fin m)) (answers : List Bool) :
    TalFamilyDecoder.run (width := width) family minimum fuel state members answers [] = [] := by
  cases fuel <;> cases members <;> rfl

theorem run_witness {n m width : ℕ} [NeZero width]
    {family : Fin m → DNF n} {shallow : ℕ} {rho : PartialAssignment n} {length : ℕ}
    (witness : Witness family shallow width rho length) (hrecoverable : witness.Recoverable)
    (hwidth : ∀ index, (family index).WidthAtMost width)
    (fuel : ℕ) (hfuel : length ≤ fuel) (padding : List (Fin m)) :
    TalFamilyDecoder.run family (shallow + 1) fuel (rho.refine witness.extension)
      (witness.memberIndices ++ padding) (witness.globalSteps.map DecisionTree.PathStep.value)
      witness.queryAdvice = witness.indices := by
  induction witness generalizing fuel padding with
  | zero =>
      exact run_nilAdvice _ _ _ _ _ _
  | @final rho length index path trace =>
      by_cases hzero : length = 0
      · have hadvice : (Witness.final (width := width) (shallow := shallow) index path trace).queryAdvice = [] := by
          exact List.length_eq_zero_iff.mp ((Witness.final (width := width) (shallow := shallow)
            index path trace).queryAdvice_length.trans hzero)
        have hindices : (Witness.final (width := width) (shallow := shallow) index path trace).indices = [] := by
          exact List.length_eq_zero_iff.mp ((Witness.final (width := width) (shallow := shallow)
            index path trace).length_indices.trans hzero)
        rw [hadvice, hindices]
        exact run_nilAdvice _ _ _ _ _ _
      · have hsplit := splitPhase_clearLastClose (shallow + 1) 0
          (trace.adviceList (widthBound := width))
          (by simpa only [ShiftedBoundariesBefore, Nat.zero_add] using hrecoverable)
        have hreplay : replayIndices (family index) (rho.refine
            (trace.satisfyingAssignment (widthBound := width))) none
            (clearLastClose (trace.adviceList (widthBound := width))) =
            DecisionTree.PathStep.indices path.steps := by
          rw [replayIndices_clearLastClose]
          exact trace.replayIndices_satisfyingAssignment (hwidth index)
        change replayIndices (family index)
          (rho.refine (DecisionTree.PathStep.assignment (trace.satisfyingSteps (widthBound := width)))) none
          (clearLastClose (trace.adviceList (widthBound := width))) = _ at hreplay
        cases fuel with
        | zero => omega
        | succ fuel =>
            have hnonempty : clearLastClose (trace.adviceList (widthBound := width)) ≠ [] := by
              intro hempty
              have hlen : (clearLastClose (trace.adviceList (widthBound := width))).length = length := by
                rw [length_clearLastClose, trace.length_adviceList, path.length_steps]
              rw [hempty] at hlen
              simp only [List.length_nil] at hlen
              omega
            cases hadvice : clearLastClose (trace.adviceList (widthBound := width)) with
            | nil => exact False.elim (hnonempty hadvice)
            | cons symbol rest =>
                simp only [Witness.memberIndices, if_neg hzero, List.singleton_append,
                  Witness.queryAdvice, hadvice]
                rw [TalFamilyDecoder.run]
                rw [← hadvice, hsplit]
                simp only
                simp only [Witness.extension, Witness.satisfyingSteps]
                rw [hreplay, run_nilAdvice]
                simp only [List.append_nil, Witness.indices]
  | @step rho remaining index phase global same tail ih =>
      obtain ⟨hpositive, hbefore, htail⟩ := hrecoverable
      have hphase : 0 < phase.steps.length := by have h := phase.minimum_length; omega
      have hnonempty : phase.trace.adviceList (widthBound := width) ≠ [] := by
        intro hempty
        have hlen := phase.trace.length_adviceList (widthBound := width)
        rw [hempty] at hlen
        simp only [List.length_nil] at hlen
        omega
      let bounded : BoundaryPhase (width := width) (family index) rho (shallow + 1) := ⟨phase, hbefore⟩
      have hsplit := boundaryPhase_split bounded (by omega) tail.queryAdvice
      have hreplay := replay_phase index phase global same tail hwidth
      have hreset := reset_phase index phase global same tail
      have hglobalLength := global_phase_length global phase.steps same
      have htake : ((global.map DecisionTree.PathStep.value) ++
          (tail.globalSteps.map DecisionTree.PathStep.value)).take
            (DecisionTree.PathStep.indices phase.steps).length = global.map DecisionTree.PathStep.value := by
        apply List.take_left'
        simpa only [DecisionTree.PathStep.indices, List.length_map] using hglobalLength
      have hdrop : ((global.map DecisionTree.PathStep.value) ++
          (tail.globalSteps.map DecisionTree.PathStep.value)).drop
            (DecisionTree.PathStep.indices phase.steps).length = tail.globalSteps.map DecisionTree.PathStep.value := by
        apply List.drop_left'
        simpa only [DecisionTree.PathStep.indices, List.length_map] using hglobalLength
      cases fuel with
      | zero => omega
      | succ fuel =>
          have htailFuel : remaining ≤ fuel := by omega
          cases hadvice : phase.trace.adviceList (widthBound := width) with
          | nil => exact False.elim (hnonempty hadvice)
          | cons symbol rest =>
              simp only [Witness.memberIndices, List.cons_append, Witness.queryAdvice,
                Witness.globalSteps, List.map_append, extension_step, hadvice, List.cons_append]
              rw [TalFamilyDecoder.run]
              have hsplit' := hsplit
              dsimp only [bounded] at hsplit'
              rw [hadvice, List.cons_append] at hsplit'
              rw [hsplit']
              simp only
              rw [hadvice] at hreplay
              rw [hreplay, htake, hdrop, hreset, ih htail fuel htailFuel padding]
              rfl

/-- The actual finite-advice decoder is a left inverse on recoverable witnesses. -/
theorem decode_encode {n m width : ℕ} [NeZero width] [NeZero m]
    {family : Fin m → DNF n} {shallow : ℕ} {rho : PartialAssignment n} {length : ℕ}
    (witness : Witness family shallow width rho length) (hrecoverable : witness.Recoverable)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    TalFamilyDecoder.decode family shallow length (witness.encode hwidth) = rho := by
  obtain ⟨padding, hmembers⟩ := witness.code_members_expand hwidth
  have hblocks : (witness.code hwidth).2.2.toQueryList = witness.queryAdvice :=
    (witness.code_blocks hwidth).trans (witness.queryAdvice_eq_packed hrecoverable)
  unfold TalFamilyDecoder.decode Witness.encode
  dsimp only
  rw [hmembers, witness.code_answers hwidth, hblocks,
    run_witness witness hrecoverable hwidth length le_rfl padding]
  exact witness.clear_extension_recovers

end TalFamilyDecoding
