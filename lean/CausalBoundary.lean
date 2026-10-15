import CausalToken
import SeededToken

/-! # Native Boolean first-separator traces with a longer answer/EOS suffix -/
noncomputable section
namespace CausalBoundary
open TransformerAC0 Autoregressive
variable {a : Architecture} {front n bound : ℕ}

def generator (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (boundary : ℕ) (hboundary : boundary ≤ bound)
    (stops : ∀ input : Bits n, model.generatedToken (CausalToken.promptInput prompt input) ⟨boundary, by omega⟩ = separator) :=
  CausalToken.generator model prompt separator (fun input => ⟨⟨boundary, by omega⟩, stops input⟩)

theorem length_eq (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (boundary : ℕ) (hboundary : boundary ≤ bound)
    (stops : ∀ input : Bits n, model.generatedToken (CausalToken.promptInput prompt input) ⟨boundary, by omega⟩ = separator)
    (before : ∀ (input : Bits n) (time : Fin boundary), model.generatedToken (CausalToken.promptInput prompt input)
      ⟨time.val, by have h := time.isLt; omega⟩ ≠ separator) (input : Bits n) :
    ((generator model prompt separator boundary hboundary stops).length input).val = boundary := by
  let G := generator model prompt separator boundary hboundary stops
  have hle : (G.length input).val ≤ boundary := Nat.find_min' (G.terminates input)
    ⟨hboundary, (CausalToken.generated_correct model prompt separator input ⟨boundary, by omega⟩).trans (stops input)⟩
  apply le_antisymm hle
  by_contra h
  have ht : (G.length input).val < boundary := by omega
  have hsep := G.separator_at_length input
  have hn := CausalToken.generated_correct model prompt separator input ⟨(G.length input).val, by omega⟩
  exact before input ⟨_, ht⟩ (hn.symm.trans hsep)

theorem answer_eq (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (boundary : ℕ) (hboundary : boundary ≤ bound)
    (stops : ∀ input : Bits n, model.generatedToken (CausalToken.promptInput prompt input) ⟨boundary, by omega⟩ = separator)
    (before : ∀ (input : Bits n) (time : Fin boundary), model.generatedToken (CausalToken.promptInput prompt input)
      ⟨time.val, by have h := time.isLt; omega⟩ ≠ separator) (input : Bits n) :
    (generator model prompt separator boundary hboundary stops).answer input =
      model.parameters.outputLabel (model.generatedToken (CausalToken.promptInput prompt input) ⟨boundary + 1, by omega⟩) := by
  unfold TokenAutoregressive.Generator.answer
  rw [length_eq model prompt separator boundary hboundary stops before input]
  exact congrArg model.parameters.outputLabel (CausalToken.generated_correct model prompt separator input ⟨boundary + 1, by omega⟩)

end CausalBoundary
