import CausalToken
import TokenSymbolic

/-! # First-separator fibers of the native symbolic growing-prefix driver

Only unary raw-symbol wiring appears in the prompt.  The core uses exactly
the native matrices, including their context restriction and greedy readout.
The separator may precede an arbitrarily long plaintext/EOS suffix.
-/

noncomputable section
namespace CausalSymbolicToken
open TransformerAC0 UniformTaskFootprint
variable {a : Architecture} {front steps n : ℕ} {Alphabet : Type*} [DecidableEq Alphabet]

def context (prompt : Fin (front * a.vocabulary) → SymbolLiteral n Alphabet) (time : ℕ)
    (previous : Fin time → Fin a.vocabulary) (wire : Fin a.inputBits) : SymbolLiteral n Alphabet :=
  let pair := finProdFinEquiv.symm wire
  if hfront : pair.1.val < front then
    prompt (finProdFinEquiv (⟨pair.1.val, hfront⟩, pair.2))
  else if hprevious : pair.1.val - front < time then
    .constant (decide (pair.2 = previous ⟨pair.1.val - front, hprevious⟩))
  else .constant false

def core (model : CausalAutoregressive.Model a front steps)
    (prompt : Fin (front * a.vocabulary) → SymbolLiteral n Alphabet) (separator : Fin a.vocabulary) :
    TokenSymbolic.Core n Alphabet where
  architecture := a
  transformer := model.parameters
  vocabulary_positive := model.vocabulary_positive
  context_positive := by have hf := model.front_positive; have hb := model.context_bound; omega
  separator := separator
  context := context prompt
  prefixLength := CausalToken.prefixLength model

def promptInput {vocabulary : ℕ} (prompt : Fin (front * vocabulary) → SymbolLiteral n Alphabet)
    (input : Fin n → Alphabet) : Bits (front * vocabulary) := fun wire => (prompt wire).eval input

theorem context_correct (model : CausalAutoregressive.Model a front steps)
    (prompt : Fin (front * a.vocabulary) → SymbolLiteral n Alphabet)
    (time : Fin (steps + 1)) (previous : Fin time.val → Fin a.vocabulary) (input : Fin n → Alphabet)
    (wire : Fin ((front + time.val) * a.vocabulary)) :
    (context prompt time.val previous (Fin.castLE
      (Nat.mul_le_mul_right a.vocabulary (by have ht := time.isLt; have hb := model.context_bound; omega)) wire)).eval input =
      model.contextInput (promptInput prompt input) time previous wire := by
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  have hpair : finProdFinEquiv.symm (Fin.castLE
      (Nat.mul_le_mul_right a.vocabulary (by have ht := time.isLt; have hb := model.context_bound; omega))
      (finProdFinEquiv (position, token))) =
      ((⟨position.val, by have hp := position.isLt; have ht := time.isLt; have hb := model.context_bound; omega⟩ : Fin a.contextLength), token) := by
    apply finProdFinEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl
  unfold context
  rw [hpair]
  simp only [CausalAutoregressive.Model.contextInput, CausalAutoregressive.Model.contextLiteral,
    Equiv.symm_apply_apply]
  refine Fin.addCases (fun p => ?_) (fun p => ?_) position
  · simp [p.isLt, promptInput, SymbolLiteral.eval, Autoregressive.ContextLiteral.eval]
  · have hn : ¬front + p.val < front := by omega
    simp [hn, p.isLt, SymbolLiteral.eval, Autoregressive.ContextLiteral.eval]

theorem generated_correct (model : CausalAutoregressive.Model a front steps)
    (prompt : Fin (front * a.vocabulary) → SymbolLiteral n Alphabet) (separator : Fin a.vocabulary)
    (input : Fin n → Alphabet) (time : Fin (steps + 1)) :
    (core model prompt separator).generatedToken input time.val =
      model.generatedToken (promptInput prompt input) time := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h count ih =>
      subst count
      rw [TokenSymbolic.Core.generatedToken, CausalAutoregressive.Model.generatedToken]
      apply CausalToken.runToken_prefix_congr model.parameters model.vocabulary_positive _ _ _ _
        (CausalToken.prefixLength_at model time)
      intro first second hwire
      change (context prompt time.val
        (fun previous => (core model prompt separator).generatedToken input previous)
        (Fin.castLE _ first)).eval input = _
      have hcast : Fin.castLE (Nat.mul_le_mul_right a.vocabulary (CausalToken.prefixLength model time.val).property.2) first =
          Fin.castLE (Nat.mul_le_mul_right a.vocabulary
            (by have ht := time.isLt; have hb := model.context_bound; omega)) second := Fin.ext hwire
      rw [hcast, context_correct model prompt]
      congr 1
      funext previous
      exact ih previous.val (by omega) ⟨previous.val, previous.isLt.trans time.isLt⟩ rfl

def generator {bound : ℕ} (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → SymbolLiteral n Alphabet) (separator : Fin a.vocabulary)
    (boundary : ℕ) (hboundary : boundary ≤ bound)
    (stops : ∀ input : Fin n → Alphabet, model.generatedToken (promptInput prompt input)
      ⟨boundary, by omega⟩ = separator) : TokenSymbolic.Generator n bound Alphabet where
  core := core model prompt separator
  terminates input := ⟨boundary, hboundary,
    (generated_correct model prompt separator input ⟨boundary, by omega⟩).trans (stops input)⟩

theorem length_eq {bound : ℕ} (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → SymbolLiteral n Alphabet) (separator : Fin a.vocabulary)
    (boundary : ℕ) (hboundary : boundary ≤ bound)
    (stops : ∀ input : Fin n → Alphabet, model.generatedToken (promptInput prompt input) ⟨boundary, by omega⟩ = separator)
    (before : ∀ (input : Fin n → Alphabet) (time : Fin boundary), model.generatedToken (promptInput prompt input)
      ⟨time.val, by have h := time.isLt; omega⟩ ≠ separator) (input : Fin n → Alphabet) :
    ((generator model prompt separator boundary hboundary stops).length input).val = boundary := by
  let G := generator model prompt separator boundary hboundary stops
  have hle : (G.length input).val ≤ boundary := Nat.find_min' (G.terminates input)
    ⟨hboundary, (generated_correct model prompt separator input ⟨boundary, by omega⟩).trans (stops input)⟩
  apply le_antisymm hle
  by_contra h
  have ht : (G.length input).val < boundary := by omega
  have hsep := (Nat.find_spec (G.terminates input)).2
  have hn := generated_correct model prompt separator input ⟨(G.length input).val, by omega⟩
  exact before input ⟨_, ht⟩ (hn.symm.trans hsep)

theorem answer_eq {bound : ℕ} (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → SymbolLiteral n Alphabet) (separator : Fin a.vocabulary)
    (boundary : ℕ) (hboundary : boundary ≤ bound)
    (stops : ∀ input : Fin n → Alphabet, model.generatedToken (promptInput prompt input) ⟨boundary, by omega⟩ = separator)
    (before : ∀ (input : Fin n → Alphabet) (time : Fin boundary), model.generatedToken (promptInput prompt input)
      ⟨time.val, by have h := time.isLt; omega⟩ ≠ separator) (input : Fin n → Alphabet) :
    (generator model prompt separator boundary hboundary stops).answer input =
      model.parameters.outputLabel (model.generatedToken (promptInput prompt input) ⟨boundary + 1, by omega⟩) := by
  unfold TokenSymbolic.Generator.answer
  rw [length_eq model prompt separator boundary hboundary stops before input]
  exact congrArg model.parameters.outputLabel (generated_correct model prompt separator input ⟨boundary + 1, by omega⟩)

end CausalSymbolicToken
