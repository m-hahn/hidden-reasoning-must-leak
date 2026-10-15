import TalCanonicalCompletion
import TalCommonTree
import TalFamilyAdvice
import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalPacking

/-!
# Actual bad-restriction witnesses for family multi-switching

Every nonfinal phase uses at least `shallow + 1` local canonical queries,
ends at a completed source-term block, and has a global answer transcript
preserving the common-tree bad event. The final phase has exactly the number
of queries left in the requested witness. Existence is proved from the
common-tree predicate, not postulated as an encoding assumption.
-/

namespace TalFamilyWitness
open scoped ENNReal
open Algebraic AC0
open TalCanonicalCompletion TalCommonTree

inductive Witness {n m : ℕ} (family : Fin m → DNF n) (shallow width : ℕ) :
    PartialAssignment n → ℕ → Type
  | zero (rho : PartialAssignment n) : Witness family shallow width rho 0
  | final {rho : PartialAssignment n} {length : ℕ}
      (index : Fin m) (path : (family index).CanonicalPath rho length)
      (trace : (family index).CanonicalTrace rho path.steps) :
      Witness family shallow width rho length
  | step {rho : PartialAssignment n} {remaining : ℕ}
      (index : Fin m) (phase : Phase (family index) rho (shallow + 1) width)
      (global : List (DecisionTree.PathStep n))
      (sameIndices : DecisionTree.PathStep.indices global = DecisionTree.PathStep.indices phase.steps)
      (tail : Witness family shallow width
        (rho.refine (DecisionTree.PathStep.assignment global)) remaining) :
      Witness family shallow width rho (phase.steps.length + remaining)

/-- Every genuine common-tree bad restriction has a full length-`D` witness. -/
theorem exists_witness {n m : ℕ} (family : Fin m → DNF n) (shallow width : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ) :
    ∀ rho : PartialAssignment n,
      ¬HasCommonTree (fun index => (family index).eval) rho shallow (length - 1) →
      Nonempty (Witness family shallow width rho length) := by
  induction length using Nat.strong_induction_on with
  | h length ih =>
      intro rho hbad
      by_cases hzero : length = 0
      · subst length
        exact ⟨.zero rho⟩
      · obtain ⟨index, hdeep⟩ := exists_deep_canonical_member family rho shallow (length - 1) hbad
        obtain ⟨phase⟩ := exists_phase (family index) rho (shallow + 1) width (hwidth index) hdeep
        by_cases hlast : length ≤ phase.steps.length
        · have hdeep' : (family index).CanonicalDepthAtLeast rho length :=
            hlast.trans phase.length_le_canonicalDepth
          obtain ⟨path⟩ := (family index).exists_canonicalPath rho length hdeep'
          obtain ⟨trace⟩ := (family index).canonicalTrace_of_path rho path.follows
          exact ⟨.final index path trace⟩
        · have hphase : 0 < phase.steps.length := by have h := phase.minimum_length; omega
          have hlength : phase.steps.length < length := lt_of_not_ge hlast
          have hbad' : ¬HasCommonTree (fun index => (family index).eval) rho shallow
              ((length - phase.steps.length - 1) +
                (DecisionTree.PathStep.indices phase.steps).length) := by
            have heq : (length - phase.steps.length - 1) +
                (DecisionTree.PathStep.indices phase.steps).length = length - 1 := by
              simp only [DecisionTree.PathStep.indices, List.length_map]
              omega
            rwa [heq]
          obtain ⟨global, hindices, hglobalbad⟩ := exists_bad_transcript
            (fun index => (family index).eval) rho shallow
            (length - phase.steps.length - 1) (DecisionTree.PathStep.indices phase.steps) hbad'
          obtain ⟨tail⟩ := ih (length - phase.steps.length) (by omega)
            (rho.refine (DecisionTree.PathStep.assignment global)) hglobalbad
          have hsum : phase.steps.length + (length - phase.steps.length) = length := by omega
          exact ⟨hsum ▸ Witness.step index phase global hindices tail⟩

namespace Witness

def satisfyingSteps {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] :
    {rho : PartialAssignment n} → {length : ℕ} → Witness family shallow width rho length →
      List (DecisionTree.PathStep n)
  | _, _, .zero _ => []
  | _, _, .final _ _ trace => trace.satisfyingSteps (widthBound := width)
  | _, _, .step _ phase _ _ tail => phase.trace.satisfyingSteps (widthBound := width) ++ tail.satisfyingSteps

def globalSteps {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} :
    {rho : PartialAssignment n} → {length : ℕ} → Witness family shallow width rho length →
      List (DecisionTree.PathStep n)
  | _, _, .zero _ => []
  | _, _, .final _ path _ => path.steps
  | _, _, .step _ _ global _ tail => global ++ tail.globalSteps

def indices {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} :
    {rho : PartialAssignment n} → {length : ℕ} → Witness family shallow width rho length → List (Fin n)
  | _, _, .zero _ => []
  | _, _, .final _ path _ => DecisionTree.PathStep.indices path.steps
  | _, _, .step _ phase _ _ tail => DecisionTree.PathStep.indices phase.steps ++ tail.indices

def phaseCount {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} :
    {rho : PartialAssignment n} → {length : ℕ} → Witness family shallow width rho length → ℕ
  | _, _, .zero _ => 0
  | _, length, .final _ _ _ => if length = 0 then 0 else 1
  | _, _, .step _ _ _ _ tail => tail.phaseCount + 1

theorem length_indices {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ}
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.indices.length = length := by
  induction witness with
  | zero => rfl
  | final index path trace => simpa [indices, DecisionTree.PathStep.indices] using path.length_steps
  | step index phase global same tail ih =>
      simp only [indices, List.length_append, DecisionTree.PathStep.indices, List.length_map, ih]

theorem satisfyingSteps_indices {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    DecisionTree.PathStep.indices witness.satisfyingSteps = witness.indices := by
  induction witness with
  | zero => rfl
  | final index path trace => exact trace.satisfyingSteps_indices
  | step index phase global same tail ih =>
      simp only [satisfyingSteps, DecisionTree.PathStep.indices, List.map_append] at ih ⊢
      rw [show (phase.trace.satisfyingSteps (widthBound := width)).map DecisionTree.PathStep.index =
          phase.steps.map DecisionTree.PathStep.index from phase.trace.satisfyingSteps_indices, ih]
      rfl

theorem globalSteps_indices {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ}
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    DecisionTree.PathStep.indices witness.globalSteps = witness.indices := by
  induction witness with
  | zero => rfl
  | final index path trace => rfl
  | step index phase global same tail ih =>
      change DecisionTree.PathStep.indices (global ++ tail.globalSteps) = _
      simp only [DecisionTree.PathStep.indices, List.map_append] at same ih ⊢
      rw [same, ih]
      rfl

theorem phaseCount_mul_le {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ}
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.phaseCount * (shallow + 1) ≤ length + shallow := by
  induction witness with
  | zero => simp [phaseCount]
  | final index path trace =>
      simp only [phaseCount]
      split_ifs <;> omega
  | step index phase global same tail ih =>
      have hphase := phase.minimum_length
      simp only [phaseCount, Nat.add_mul, Nat.one_mul]
      omega

theorem phaseCount_le_slots {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ}
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.phaseCount ≤ TalFamilyAdvice.phaseSlots shallow length := by
  unfold TalFamilyAdvice.phaseSlots
  exact (Nat.le_div_iff_mul_le (by omega)).mpr witness.phaseCount_mul_le

/-- All queried variables are distinct and were live in the original restriction. -/
theorem indices_nodup_and_subset_live {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ}
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.indices.Nodup ∧ witness.indices.toFinset ⊆ rho.liveVariables := by
  induction witness with
  | zero => simp [indices]
  | final index path trace => exact ⟨path.indices_nodup, path.indices_subset_live⟩
  | @step rho remaining index phase global same tail ih =>
      constructor
      · apply phase.indices_nodup.append ih.1
        intro coordinate hphase htail
        have hfixed : coordinate ∈ (DecisionTree.PathStep.assignment global).fixedVariables := by
          rw [DecisionTree.PathStep.fixedVariables_assignment, same]
          exact List.mem_toFinset.mpr hphase
        have hlive := ih.2 (List.mem_toFinset.mpr htail)
        rw [PartialAssignment.liveVariables_refine] at hlive
        exact (PartialAssignment.mem_fixedVariables _ _).mp hfixed
          ((PartialAssignment.mem_liveVariables _ _).mp (Finset.mem_inter.mp hlive).2)
      · intro coordinate hcoord
        simp only [indices, List.mem_toFinset, List.mem_append] at hcoord
        rcases hcoord with hphase | htail
        · exact phase.indices_subset_live (List.mem_toFinset.mpr hphase)
        · have h := ih.2 (List.mem_toFinset.mpr htail)
          rw [PartialAssignment.liveVariables_refine] at h
          exact (Finset.mem_inter.mp h).1

def extension {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    PartialAssignment n := DecisionTree.PathStep.assignment witness.satisfyingSteps

theorem extension_fixesOnlyLive {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.extension.fixedVariables ⊆ rho.liveVariables := by
  rw [extension, DecisionTree.PathStep.fixedVariables_assignment, witness.satisfyingSteps_indices]
  exact witness.indices_nodup_and_subset_live.2

theorem extension_fixedCount {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    witness.extension.fixedCount = length := by
  rw [extension, PartialAssignment.fixedCount, DecisionTree.PathStep.fixedVariables_assignment,
    witness.satisfyingSteps_indices, List.toFinset_card_of_nodup witness.indices_nodup_and_subset_live.1,
    witness.length_indices]

/-- The encoded restriction changes exactly `D` previously live variables. -/
theorem clear_extension_recovers {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {length : ℕ} (witness : Witness family shallow width rho length) :
    (rho.refine witness.extension).clear witness.indices.toFinset = rho := by
  have hfixed : witness.extension.fixedVariables = witness.indices.toFinset := by
    rw [extension, DecisionTree.PathStep.fixedVariables_assignment, witness.satisfyingSteps_indices]
  rw [← hfixed]
  exact PartialAssignment.clear_refine_fixedVariables rho witness.extension witness.extension_fixesOnlyLive

/-- Exact mass change of the constructed witness, including endpoint parameters `p=0,1`. -/
theorem distribution_extension_cross_mul {n m : ℕ} {family : Fin m → DNF n}
    {shallow width : ℕ} [NeZero width] {rho : PartialAssignment n} {length : ℕ}
    (witness : Witness family shallow width rho length) (p : NNReal) (hone : p ≤ 1) :
    (RandomRestriction.fixedWeight p : ENNReal) ^ length *
        RandomRestriction.distribution n p hone rho =
      (p : ENNReal) ^ length *
        RandomRestriction.distribution n p hone (rho.refine witness.extension) := by
  have h := RandomRestriction.distribution_refine_cross_mul n p hone rho witness.extension
    witness.extension_fixesOnlyLive
  rwa [witness.extension_fixedCount] at h

end Witness

end TalFamilyWitness
