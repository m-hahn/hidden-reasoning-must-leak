import TalFamilyEncoder
import TalRecoverableWitness
import TalFutureReplay

/-!
# The actual packed family replay transcript

Every completed phase retains its final block boundary. Only the final global
query marker is erased. This connects the finite sorted-block packer to the
phase transcript used by the decoder.
-/

namespace TalFamilyTranscript
open Algebraic AC0 Switching TalCanonicalCompletion TalFamilyWitness

def fullBlocks {width : ℕ} : List (List (RelativeQuery width)) → List (QueryAdvice width)
  | [] => []
  | block :: rest => relativeBlockToQueryList block true ++ fullBlocks rest

theorem relativeBlock_cons {width : ℕ} (query : RelativeQuery width)
    (block : List (RelativeQuery width)) (hnonempty : block ≠ []) (closes : Bool) :
    relativeBlockToQueryList (query :: block) closes =
      query.toQueryAdvice false :: relativeBlockToQueryList block closes := by
  unfold relativeBlockToQueryList
  rw [List.ofFn_succ]
  congr 1
  · cases closes <;> simp [hnonempty]
  · congr 1
    funext index
    simp only [List.get_eq_getElem, List.getElem_cons_succ, Fin.val_succ,
      List.length_cons, Nat.add_right_cancel_iff]

theorem fullBlocks_prependFirst {width : ℕ} (query : RelativeQuery width)
    (blocks : List (List (RelativeQuery width)))
    (hblocks : ∀ block ∈ blocks, block ≠ []) (hnonempty : blocks ≠ []) :
    fullBlocks (prependToFirstBlock query blocks) = query.toQueryAdvice false :: fullBlocks blocks := by
  cases blocks with
  | nil => exact False.elim (hnonempty rfl)
  | cons block rest =>
      simp only [prependToFirstBlock, fullBlocks]
      rw [relativeBlock_cons query block (hblocks _ (by simp))]
      rfl

theorem relativeBlocks_append {width : ℕ} (first rest : List (List (RelativeQuery width)))
    (hrest : rest ≠ []) :
    relativeBlocksToQueryList (first ++ rest) = fullBlocks first ++ relativeBlocksToQueryList rest := by
  induction first with
  | nil => simp [fullBlocks]
  | cons block tail ih =>
      cases tail with
      | nil =>
          cases rest with
          | nil => exact False.elim (hrest rfl)
          | cons next remaining => simp [relativeBlocksToQueryList, fullBlocks]
      | cons next remaining =>
          change relativeBlocksToQueryList (block :: next :: (remaining ++ rest)) = _
          rw [relativeBlocksToQueryList.eq_def, fullBlocks]
          dsimp only
          rw [List.cons_append] at ih
          rw [ih]
          exact (List.append_assoc _ _ _).symm

theorem closedBlock_blocks_nonempty {n width : ℕ} [NeZero width] {formula : DNF n}
    {term : Term n} {rho : PartialAssignment n} {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)} (trace : formula.CanonicalBlockTrace term rho indices steps)
    (hclosed : ClosedBlock trace) : trace.combinedBlocks (widthBound := width) ≠ [] := by
  cases trace with
  | nil => exact False.elim hclosed
  | takeMore tail =>
      simp only [DNF.CanonicalBlockTrace.combinedBlocks]
      cases tail.combinedBlocks (widthBound := width) <;> simp [prependToFirstBlock]
  | takeLast tail => simp [DNF.CanonicalBlockTrace.combinedBlocks]

mutual
theorem closedTrace_fullBlocks {n width : ℕ} [NeZero width] {formula : DNF n}
    {rho : PartialAssignment n} {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) (hclosed : ClosedTrace trace) :
    fullBlocks (trace.combinedBlocks (widthBound := width)) = trace.adviceList (widthBound := width) :=
  match trace with
  | .nil _ => rfl
  | .start _ _ _ block => closedBlock_fullBlocks block hclosed
termination_by 2 * steps.length + 1
decreasing_by all_goals simp_wf

theorem closedBlock_fullBlocks {n width : ℕ} [NeZero width] {formula : DNF n}
    {term : Term n} {rho : PartialAssignment n} {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)} (trace : formula.CanonicalBlockTrace term rho indices steps)
    (hclosed : ClosedBlock trace) :
    fullBlocks (trace.combinedBlocks (widthBound := width)) = trace.adviceList (widthBound := width) := by
  cases trace with
  | nil => exact False.elim hclosed
  | @takeMore currentTerm state coordinate next rest value steps tail =>
      rw [DNF.CanonicalBlockTrace.combinedBlocks,
        fullBlocks_prependFirst _ _ tail.combinedBlocks_nonempty
          (closedBlock_blocks_nonempty tail hclosed),
        closedBlock_fullBlocks tail hclosed, DNF.CanonicalBlockTrace.adviceList_takeMore]
      rfl
  | @takeLast currentTerm state coordinate value steps tail =>
      rw [DNF.CanonicalBlockTrace.combinedBlocks, fullBlocks,
        relativeBlockToQueryList_singleton, closedTrace_fullBlocks tail hclosed,
        DNF.CanonicalBlockTrace.adviceList_takeLast]
      rfl
termination_by 2 * steps.length
decreasing_by all_goals (simp_wf; subst_vars; simp_all only [List.length_cons]; omega)
end

end TalFamilyTranscript

namespace TalFamilyWitness.Witness
open Algebraic AC0 Switching TalCanonicalCompletion TalFamilyTranscript

def queryAdvice {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] :
    {rho : PartialAssignment n} → {length : ℕ} → Witness family shallow width rho length →
      List (QueryAdvice width)
  | _, _, .zero _ => []
  | _, _, .final _ _ trace => clearLastClose (trace.adviceList (widthBound := width))
  | _, _, .step _ phase _ _ tail => phase.trace.adviceList (widthBound := width) ++ tail.queryAdvice

theorem queryAdvice_length {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.queryAdvice.length = length := by
  induction witness with
  | zero => rfl
  | final index path trace =>
      simp only [queryAdvice, length_clearLastClose, trace.length_adviceList, path.length_steps]
  | step index phase global same tail ih =>
      simp only [queryAdvice, List.length_append, phase.trace.length_adviceList, ih]

theorem queryAdvice_eq_packed {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hrecoverable : witness.Recoverable) :
    relativeBlocksToQueryList witness.blocks = witness.queryAdvice := by
  induction witness with
  | zero => rfl
  | final index path trace => exact trace.relativeBlocksToQueryList_combinedBlocks
  | @step rho remaining index phase global same tail ih =>
      obtain ⟨hpositive, hbefore, htail⟩ := hrecoverable
      have hblocks : tail.blocks ≠ [] := by
        intro hempty
        have h := tail.blocks_length_sum
        simp only [hempty, List.map_nil, List.sum_nil] at h
        omega
      rw [blocks, relativeBlocks_append _ _ hblocks, closedTrace_fullBlocks phase.trace phase.closed,
        ih htail]
      rfl

end TalFamilyWitness.Witness
