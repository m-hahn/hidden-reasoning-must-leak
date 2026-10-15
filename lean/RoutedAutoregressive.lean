import RoutedMatrixCorrectness
import CausalAutoregressive

/-!
# Autoregression by the explicit routing matrices

The finite routing/local-map recurrence is executed by one learned matrix
parameter set on growing causal prefixes. The recurrence below is derived
from the plan and local map; it is not a realization field of the model.
-/

noncomputable section
namespace RoutedMatrix
open TransformerAC0

variable {vocabulary window heads opcodes front steps : ℕ}

def causalModel (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (hv : 0 < vocabulary) (hfront : 0 < front) (bounded : front + steps ≤ window) :
    CausalAutoregressive.Model (architecture vocabulary window heads opcodes) front steps where
  parameters := transformer plan localMap label
  vocabulary_positive := hv
  front_positive := hfront
  context_bound := bounded

def promptInput (prompt : Fin front → Fin vocabulary) : Bits (front * vocabulary) := fun wire =>
  let pt := finProdFinEquiv.symm wire
  decide (pt.2 = prompt pt.1)

/-- Only the prompt and already generated tokens fill the causal prefix.
The dummy suffix is never read by the restricted matrix execution. -/
def contextWord (hv : 0 < vocabulary) (prompt : Fin front → Fin vocabulary)
    (time : ℕ) (previous : Fin time → Fin vocabulary) : Fin window → Fin vocabulary := fun position =>
  if hprompt : position.val < front then prompt ⟨position.val, hprompt⟩
  else if hprevious : position.val - front < time then previous ⟨position.val - front, hprevious⟩
  else ⟨0, hv⟩

theorem context_input_literal (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (hv : 0 < vocabulary) (hfront : 0 < front) (bounded : front + steps ≤ window)
    (prompt : Fin front → Fin vocabulary) (time : Fin (steps + 1)) (previous : Fin time.val → Fin vocabulary) :
    (causalModel plan localMap label hv hfront bounded).contextInput (promptInput prompt) time previous =
      CausalMatrix.restrictInput (transformer plan localMap label) (front + time.val)
        (by change front + time.val ≤ window; have ht := time.isLt; omega)
        (oneHot (contextWord hv prompt time.val previous)) := by
  funext wire
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [CausalMatrix.restrictInput, oneHot, FixedPrecisionTransformer.inputIndex,
    architecture, CausalMatrix.architecture, Equiv.symm_apply_apply]
  change (CausalAutoregressive.Model.contextLiteral _ time previous
    (finProdFinEquiv (position, token))).eval (promptInput prompt) = _
  simp only [CausalAutoregressive.Model.contextLiteral, Equiv.symm_apply_apply]
  refine Fin.addCases (fun p => ?_) (fun p => ?_) position
  · simp [Autoregressive.ContextLiteral.eval, promptInput, contextWord,
      FixedPrecisionTransformer.inputIndex, p.isLt]
  · have hp : ¬front + p.val < front := by omega
    simp [Autoregressive.ContextLiteral.eval, contextWord, hp, p.isLt]

def routedToken (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary)
    (hv : 0 < vocabulary) (hfront : 0 < front) (bounded : front + steps ≤ window)
    (prompt : Fin front → Fin vocabulary) (time : Fin (steps + 1)) : Fin vocabulary :=
  localMap (features plan
    (contextWord hv prompt time.val (fun previous =>
      routedToken plan localMap hv hfront bounded prompt ⟨previous.val, previous.isLt.trans time.isLt⟩))
    ⟨front + time.val - 1, by have ht := time.isLt; omega⟩)
termination_by time.val

/-- Every generated token is computed by the numerical matrix Transformer.
The local recurrence is a theorem about the explicit constructor, not a
correctness assumption attached to an abstract Transformer. -/
theorem autoregressive_correct (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (hv : 0 < vocabulary) (hfront : 0 < front) (bounded : front + steps ≤ window)
    (prompt : Fin front → Fin vocabulary) (time : Fin (steps + 1)) :
    (causalModel plan localMap label hv hfront bounded).generatedToken (promptInput prompt) time =
      routedToken plan localMap hv hfront bounded prompt time := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h n ih =>
      rw [CausalAutoregressive.Model.generatedToken, routedToken]
      have hprevious : (fun previous : Fin time.val =>
          (causalModel plan localMap label hv hfront bounded).generatedToken (promptInput prompt)
            ⟨previous.val, previous.isLt.trans time.isLt⟩) =
          (fun previous : Fin time.val => routedToken plan localMap hv hfront bounded prompt
            ⟨previous.val, previous.isLt.trans time.isLt⟩) := by
        funext previous
        exact ih previous.val (by omega) _ rfl
      rw [hprevious, context_input_literal]
      change (CausalMatrix.restrictContext (transformer plan localMap label) (front + time.val) _).runToken _ _ _ = _
      rw [run_token_prefix_correct]
      rfl

theorem answer_correct (plan : Plan vocabulary window heads opcodes)
    (localMap : Bits (featureCount vocabulary heads opcodes) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (hv : 0 < vocabulary) (hfront : 0 < front) (bounded : front + steps ≤ window)
    (prompt : Fin front → Fin vocabulary) :
    (causalModel plan localMap label hv hfront bounded).answer (promptInput prompt) =
      label (routedToken plan localMap hv hfront bounded prompt (Fin.last steps)) := by
  unfold CausalAutoregressive.Model.answer
  rw [autoregressive_correct]
  rfl

end RoutedMatrix
