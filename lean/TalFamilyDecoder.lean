import TalFamilyEncoder
import TalPhaseSplit

/-!
# The finite family advice decoder

Only the refined restriction, global answer bits, family indices, and counted
block advice are read. Source coordinates are reconstructed by canonical
replay. Global answers overwrite the completed phase's satisfying crumbs
before the next phase is decoded. Fuel bounds malformed-advice behavior.

The end-to-end reconstruction proof is in `TalFamilyDecoding`; injectivity
and the family multi-switching probability theorem are in `TalMultiSwitching`.
-/

namespace TalFamilyDecoder
open Algebraic AC0 Switching

def answerAssignment {n : ℕ} (indices : List (Fin n)) (answers : List Bool) : PartialAssignment n :=
  DecisionTree.PathStep.assignment ((indices.zip answers).map fun pair => ⟨pair.1, pair.2⟩)

def run {n m width : ℕ} (family : Fin m → DNF n) (minimum : ℕ) :
    ℕ → PartialAssignment n → List (Fin m) → List Bool → List (QueryAdvice width) → List (Fin n)
  | 0, _, _, _, _ => []
  | _ + 1, _, [], _, _ => []
  | _ + 1, _, _ :: _, _, [] => []
  | fuel + 1, state, member :: members, answers, symbol :: symbols =>
      let parts := TalPhaseSplit.splitPhase minimum 0 (symbol :: symbols)
      let indices := replayIndices (family member) state none parts.1
      let nextState := (answerAssignment indices (answers.take indices.length)).refine state
      indices ++ run family minimum fuel nextState members
        (answers.drop indices.length) parts.2

noncomputable def decode {n m width : ℕ} (family : Fin m → DNF n) (shallow length : ℕ)
    (encoded : PartialAssignment n × TalFamilyAdvice.BroadAdvice m width shallow length) : PartialAssignment n :=
  let indices := run family (shallow + 1) length encoded.1
    (List.ofFn encoded.2.2.1) (List.ofFn encoded.2.1) encoded.2.2.2.toQueryList
  encoded.1.clear indices.toFinset

end TalFamilyDecoder
