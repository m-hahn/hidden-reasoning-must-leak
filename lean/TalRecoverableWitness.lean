import TalFamilyWitness
import TalTracePrefix

/-!
# Recoverable family phase boundaries

Bad restrictions have witnesses whose nonfinal phases end at the first
completed term block after `shallow + 1` queries. The final phase is a prefix
of the same completed phase, so it cannot contain an unrecorded extra phase
boundary. No phase lengths need to be stored in the finite advice.
-/

namespace TalFamilyWitness
open Algebraic AC0 TalCanonicalCompletion TalCommonTree TalTracePrefix

namespace Witness

def Recoverable {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width] :
    {rho : PartialAssignment n} → {length : ℕ} → Witness family shallow width rho length → Prop
  | _, _, .zero _ => True
  | _, _, .final _ _ trace => BoundariesBefore (shallow + 1) (trace.adviceList (widthBound := width))
  | _, _, .step (remaining := remaining) _ phase _ _ tail =>
      0 < remaining ∧
      BoundariesBefore (shallow + 1) (phase.trace.adviceList (widthBound := width)) ∧ tail.Recoverable

theorem recoverable_cast {n m : ℕ} {family : Fin m → DNF n} {shallow width : ℕ} [NeZero width]
    {rho : PartialAssignment n} {left right : ℕ} (heq : left = right)
    (witness : Witness family shallow width rho left) :
    (show Witness family shallow width rho right from heq ▸ witness).Recoverable ↔ witness.Recoverable := by
  subst right
  rfl

end Witness

theorem exists_recoverable_witness {n m width : ℕ} [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ) (hwidth : ∀ index, (family index).WidthAtMost width)
    (length : ℕ) : ∀ rho : PartialAssignment n,
      ¬HasCommonTree (fun index => (family index).eval) rho shallow (length - 1) →
      ∃ witness : Witness family shallow width rho length, witness.Recoverable := by
  induction length using Nat.strong_induction_on with
  | h length ih =>
      intro rho hbad
      by_cases hzero : length = 0
      · subst length
        exact ⟨.zero rho, trivial⟩
      · obtain ⟨index, hdeep⟩ := exists_deep_canonical_member family rho shallow (length - 1) hbad
        obtain ⟨phase⟩ := exists_boundaryPhase (family index) rho (shallow + 1) (hwidth index) hdeep
        by_cases hlast : length ≤ phase.steps.length
        · obtain ⟨path, trace, hbefore⟩ := phase_prefix phase length hlast
          exact ⟨.final index path trace, hbefore⟩
        · have hphase : 0 < phase.steps.length := by have h := phase.minimum_length; omega
          have hlength : phase.steps.length < length := lt_of_not_ge hlast
          have hbad' : ¬HasCommonTree (fun index => (family index).eval) rho shallow
              ((length - phase.steps.length - 1) + (DecisionTree.PathStep.indices phase.steps).length) := by
            have heq : (length - phase.steps.length - 1) +
                (DecisionTree.PathStep.indices phase.steps).length = length - 1 := by
              simp only [DecisionTree.PathStep.indices, List.length_map]
              omega
            rwa [heq]
          obtain ⟨global, hindices, hglobalbad⟩ := exists_bad_transcript
            (fun index => (family index).eval) rho shallow (length - phase.steps.length - 1)
            (DecisionTree.PathStep.indices phase.steps) hbad'
          obtain ⟨tail, htail⟩ := ih (length - phase.steps.length) (by omega)
            (rho.refine (DecisionTree.PathStep.assignment global)) hglobalbad
          have hsum : phase.steps.length + (length - phase.steps.length) = length := by omega
          refine ⟨hsum ▸ Witness.step index phase.toPhase global hindices tail, ?_⟩
          exact (Witness.recoverable_cast hsum _).mpr ⟨by omega, phase.boundaries, htail⟩

end TalFamilyWitness
