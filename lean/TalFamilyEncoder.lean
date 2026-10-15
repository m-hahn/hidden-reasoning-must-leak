import TalFamilyWitness
import TalBlockPacking

/-!
# The finite family switching encoder

The output consists of a refined restriction and exactly the finite advice
counted in `TalFamilyAdvice`: global answer bits, padded family indices, and
sorted source-term blocks. Hidden coordinates and terms are not stored in
the advice. Injectivity is a separate decoder obligation.
-/

noncomputable section
namespace TalFamilyWitness
open Algebraic AC0 Switching
open TalFamilyWitness

namespace Witness

def blocks {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] :
    {rho : PartialAssignment n} → {length : ℕ} → Witness family shallow width rho length →
      List (List (RelativeQuery width))
  | _, _, .zero _ => []
  | _, _, .final _ _ trace => trace.combinedBlocks (widthBound := width)
  | _, _, .step _ phase _ _ tail => phase.trace.combinedBlocks (widthBound := width) ++ tail.blocks

def memberIndices {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} :
    {rho : PartialAssignment n} → {length : ℕ} → Witness family shallow width rho length → List (Fin m)
  | _, _, .zero _ => []
  | _, length, .final index _ _ => if length = 0 then [] else [index]
  | _, _, .step index _ _ _ tail => index :: tail.memberIndices

theorem memberIndices_length {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ}
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.memberIndices.length = witness.phaseCount := by
  induction witness with
  | zero => rfl
  | final index path trace =>
      simp only [memberIndices, Witness.phaseCount]
      split_ifs <;> rfl
  | step index phase global same tail ih => simp [memberIndices, Witness.phaseCount, ih]

theorem blocks_length_sum {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    (witness.blocks.map List.length).sum = length := by
  induction witness with
  | zero => rfl
  | final index path trace =>
      exact (trace.sum_length_combinedBlocks (widthBound := width)).trans path.length_steps
  | step index phase global same tail ih =>
      simp only [blocks, List.map_append, List.sum_append]
      rw [phase.trace.sum_length_combinedBlocks, ih]

theorem blocks_nonempty {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    ∀ block ∈ witness.blocks, block ≠ [] := by
  induction witness with
  | zero => simp [blocks]
  | final index path trace => exact trace.combinedBlocks_nonempty
  | step index phase global same tail ih =>
      intro block hblock
      simp only [blocks, List.mem_append] at hblock
      rcases hblock with hphase | htail
      · exact phase.trace.combinedBlocks_nonempty block hphase
      · exact ih block htail

theorem blocks_sorted {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    ∀ block ∈ witness.blocks, (block.map Prod.fst).Pairwise (· < ·) := by
  induction witness with
  | zero => simp [blocks]
  | final index path trace => exact trace.combinedBlocks_positions_pairwise (hwidth index)
  | step index phase global same tail ih =>
      intro block hblock
      simp only [blocks, List.mem_append] at hblock
      rcases hblock with hphase | htail
      · exact phase.trace.combinedBlocks_positions_pairwise (hwidth index) block hphase
      · exact ih block htail

theorem blocks_bounded {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    ∀ block ∈ witness.blocks, block.length ≤ width := by
  intro block hblock
  have hsorted := witness.blocks_sorted hwidth block hblock
  have h := hsorted.nodup.length_le_card
  simpa only [List.length_map, Fintype.card_fin] using h

theorem globalSteps_length {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ}
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.globalSteps.length = length := by
  have h := congrArg List.length witness.globalSteps_indices
  simpa only [DecisionTree.PathStep.indices, List.length_map, witness.length_indices] using h

def code {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] [NeZero m]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    TalFamilyAdvice.BroadAdvice m width shallow length :=
  let answers : Fin length → Bool := listToFn (witness.globalSteps.map DecisionTree.PathStep.value)
    (by simpa using witness.globalSteps_length)
  let members := fun index : Fin (TalFamilyAdvice.phaseSlots shallow length) =>
    witness.memberIndices[index.val]?.getD (Fin.ofNat' m 0)
  let packed := TalBlockAdvice.pack width witness.blocks witness.blocks_nonempty
    (witness.blocks_sorted hwidth) (witness.blocks_bounded hwidth)
  let blockCode : TalBlockAdvice.Advice width length := witness.blocks_length_sum ▸ packed.advice
  (answers, members, blockCode)

theorem code_answers {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] [NeZero m]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    List.ofFn (witness.code hwidth).1 = witness.globalSteps.map DecisionTree.PathStep.value := by
  exact ofFn_listToFn _ (by simpa only [List.length_map] using witness.globalSteps_length)

theorem code_member {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] [NeZero m]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width)
    (index : ℕ) (hindex : index < witness.memberIndices.length) :
    (witness.code hwidth).2.1 ⟨index, by
      exact hindex.trans_le (witness.memberIndices_length.trans_le witness.phaseCount_le_slots)⟩ =
      witness.memberIndices[index] := by
  simp [code, List.getElem?_eq_getElem hindex]

theorem code_blocks {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] [NeZero m]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    (witness.code hwidth).2.2.toQueryList = relativeBlocksToQueryList witness.blocks := by
  unfold code
  rw [TalBlockAdvice.Advice.toQueryList_cast]
  exact (TalBlockAdvice.pack width witness.blocks witness.blocks_nonempty
    (witness.blocks_sorted hwidth) (witness.blocks_bounded hwidth)).toQueryList

theorem code_members_prefix {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] [NeZero m]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    (List.ofFn (witness.code hwidth).2.1).take witness.memberIndices.length = witness.memberIndices := by
  have hlength : witness.memberIndices.length ≤ TalFamilyAdvice.phaseSlots shallow length :=
    witness.memberIndices_length.trans_le witness.phaseCount_le_slots
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    exact Nat.min_eq_left hlength
  · intro index hleft hright
    rw [List.getElem_take, List.getElem_ofFn]
    exact witness.code_member hwidth index hright

theorem code_members_expand {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] [NeZero m]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    ∃ padding : List (Fin m), List.ofFn (witness.code hwidth).2.1 = witness.memberIndices ++ padding := by
  refine ⟨(List.ofFn (witness.code hwidth).2.1).drop witness.memberIndices.length, ?_⟩
  have h := List.take_append_drop witness.memberIndices.length (List.ofFn (witness.code hwidth).2.1)
  rw [witness.code_members_prefix hwidth] at h
  exact h.symm

def encode {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] [NeZero m]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length)
    (hwidth : ∀ index, (family index).WidthAtMost width) :
    PartialAssignment n × TalFamilyAdvice.BroadAdvice m width shallow length :=
  (rho.refine witness.extension, witness.code hwidth)

end Witness
end TalFamilyWitness
