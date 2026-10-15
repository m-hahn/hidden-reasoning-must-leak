import CausalAutoregressive
import TokenAutoregressive

/-!
# Native growing-prefix separator-terminated lower bounds

The general token-fiber proofs now allow context restriction of the same
matrices. Here their semantics is identified with the native causal driver,
with literal prompt wiring and no simulation or fiber-circuit certificate.
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace CausalToken
open TransformerAC0 Autoregressive
variable {a : Architecture} {front steps n : ℕ}

def prefixLength (model : CausalAutoregressive.Model a front steps) (time : ℕ) :
    {length : ℕ // 0 < length ∧ length ≤ a.contextLength} :=
  ⟨min (front + time) a.contextLength, by
    have hf := model.front_positive
    have hb := model.context_bound
    omega, min_le_right _ _⟩

def context (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (time : ℕ)
    (previous : Fin time → Fin a.vocabulary) (wire : Fin a.inputBits) : ContextLiteral n :=
  let pair := finProdFinEquiv.symm wire
  if hfront : pair.1.val < front then
    prompt (finProdFinEquiv (⟨pair.1.val, hfront⟩, pair.2))
  else if hprevious : pair.1.val - front < time then
    .constant (decide (pair.2 = previous ⟨pair.1.val - front, hprevious⟩))
  else .constant false

def core (model : CausalAutoregressive.Model a front steps)
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary) :
    TokenAutoregressive.Core n where
  architecture := a
  transformer := model.parameters
  vocabulary_positive := model.vocabulary_positive
  context_positive := by have hf := model.front_positive; have hb := model.context_bound; omega
  separator := separator
  context := context prompt
  prefixLength := prefixLength model

def promptInput {vocabulary : ℕ} (prompt : Fin (front * vocabulary) → ContextLiteral n) (input : Bits n) : Bits (front * vocabulary) :=
  fun wire => (prompt wire).eval input

theorem prefixLength_at (model : CausalAutoregressive.Model a front steps) (time : Fin (steps + 1)) :
    (prefixLength model time.val).val = front + time.val := by
  apply min_eq_left
  have ht := time.isLt
  have hb := model.context_bound
  omega

theorem context_correct (model : CausalAutoregressive.Model a front steps)
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (time : Fin (steps + 1)) (previous : Fin time.val → Fin a.vocabulary) (input : Bits n)
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
  · simp [p.isLt, promptInput, ContextLiteral.eval]
  · have hn : ¬front + p.val < front := by omega
    simp [hn, p.isLt, ContextLiteral.eval]

theorem runToken_prefix_congr (parameters : FixedPrecisionTransformer a) (hv : 0 < a.vocabulary)
    {first second : ℕ} (hfirst : 0 < first) (hsecond : 0 < second)
    (bfirst : first ≤ a.contextLength) (bsecond : second ≤ a.contextLength) (heq : first = second)
    (inputFirst : Bits (first * a.vocabulary)) (inputSecond : Bits (second * a.vocabulary))
    (agree : ∀ i j, i.val = j.val → inputFirst i = inputSecond j) :
    (CausalMatrix.restrictContext parameters first bfirst).runToken hv hfirst inputFirst =
      (CausalMatrix.restrictContext parameters second bsecond).runToken hv hsecond inputSecond := by
  subst second
  congr 1
  funext wire
  exact agree wire wire rfl

theorem generated_correct (model : CausalAutoregressive.Model a front steps)
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (input : Bits n) (time : Fin (steps + 1)) :
    (core model prompt separator).generatedToken input time.val =
      model.generatedToken (promptInput prompt input) time := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h count ih =>
      subst count
      rw [TokenAutoregressive.Core.generatedToken, CausalAutoregressive.Model.generatedToken]
      have hlength := prefixLength_at model time
      apply runToken_prefix_congr model.parameters model.vocabulary_positive _ _ _ _ hlength
      intro first second hwire
      change (context prompt time.val
        (fun previous => (core model prompt separator).generatedToken input previous)
        (Fin.castLE _ first)).eval input = _
      have hcast : Fin.castLE (Nat.mul_le_mul_right a.vocabulary (prefixLength model time.val).property.2) first =
          Fin.castLE (Nat.mul_le_mul_right a.vocabulary
            (by have ht := time.isLt; have hb := model.context_bound; omega)) second := Fin.ext hwire
      rw [hcast]
      rw [context_correct model prompt separator]
      congr 1
      funext previous
      exact ih previous.val (by omega) ⟨previous.val, previous.isLt.trans time.isLt⟩ rfl

def generator {bound : ℕ} (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (terminates : ∀ input : Bits n, ∃ time : Fin (bound + 1),
      model.generatedToken (promptInput prompt input) ⟨time.val, by have h := time.isLt; omega⟩ = separator) :
    TokenAutoregressive.Generator n bound where
  core := core model prompt separator
  terminates input := by
    obtain ⟨time, hsep⟩ := terminates input
    refine ⟨time.val, by have h := time.isLt; omega, ?_⟩
    exact (generated_correct model prompt separator input
      ⟨time.val, by have h := time.isLt; omega⟩).trans hsep

theorem answer_correct {bound : ℕ} (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (terminates : ∀ input : Bits n, ∃ time : Fin (bound + 1),
      model.generatedToken (promptInput prompt input) ⟨time.val, by have h := time.isLt; omega⟩ = separator)
    (input : Bits n) :
    (generator model prompt separator terminates).answer input =
      model.parameters.outputLabel (model.generatedToken (promptInput prompt input)
        ⟨((generator model prompt separator terminates).length input).val + 1, by
          have h := ((generator model prompt separator terminates).length input).isLt; omega⟩) := by
  unfold TokenAutoregressive.Generator.answer
  exact congrArg model.parameters.outputLabel (generated_correct model prompt separator input
    ⟨((generator model prompt separator terminates).length input).val + 1, by
      have h := ((generator model prompt separator terminates).length input).isLt; omega⟩)

def fixedGenerator {bound : ℕ} (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (stops : ∀ input : Bits n, model.generatedToken (promptInput prompt input)
      ⟨bound, by omega⟩ = separator) : TokenAutoregressive.Generator n bound :=
  generator model prompt separator (fun input => ⟨Fin.last bound, stops input⟩)

theorem fixed_length {bound : ℕ} (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (stops : ∀ input : Bits n, model.generatedToken (promptInput prompt input) ⟨bound, by omega⟩ = separator)
    (before : ∀ (input : Bits n) (time : Fin bound), model.generatedToken (promptInput prompt input)
      ⟨time.val, by have h := time.isLt; omega⟩ ≠ separator) (input : Bits n) :
    (fixedGenerator model prompt separator stops).length input = Fin.last bound := by
  apply Fin.ext
  have hb := ((fixedGenerator model prompt separator stops).length input).isLt
  by_contra hne
  have ht : ((fixedGenerator model prompt separator stops).length input).val < bound := by
    change _ ≠ bound at hne
    omega
  have hsep := (fixedGenerator model prompt separator stops).separator_at_length input
  have hnative := generated_correct model prompt separator input
    ⟨((fixedGenerator model prompt separator stops).length input).val, by omega⟩
  exact before input ⟨_, ht⟩ (hnative.symm.trans hsep)

theorem fixed_answer {bound : ℕ} (model : CausalAutoregressive.Model a front (bound + 1))
    (prompt : Fin (front * a.vocabulary) → ContextLiteral n) (separator : Fin a.vocabulary)
    (stops : ∀ input : Bits n, model.generatedToken (promptInput prompt input) ⟨bound, by omega⟩ = separator)
    (before : ∀ (input : Bits n) (time : Fin bound), model.generatedToken (promptInput prompt input)
      ⟨time.val, by have h := time.isLt; omega⟩ ≠ separator) (input : Bits n) :
    (fixedGenerator model prompt separator stops).answer input = model.answer (promptInput prompt input) := by
  have h := answer_correct model prompt separator (fun input => ⟨Fin.last bound, stops input⟩) input
  have hl := fixed_length model prompt separator stops before input
  change (fixedGenerator model prompt separator stops).answer input =
    model.parameters.outputLabel (model.generatedToken (promptInput prompt input)
      ⟨((fixedGenerator model prompt separator stops).length input).val + 1, _⟩) at h
  have ht : (⟨((fixedGenerator model prompt separator stops).length input).val + 1,
      by have h := ((fixedGenerator model prompt separator stops).length input).isLt; omega⟩ : Fin (bound + 2)) =
      Fin.last (bound + 1) := by
    apply Fin.ext
    have hv := congrArg Fin.val hl
    simp only [Fin.val_last] at hv ⊢
    omega
  exact h.trans (congrArg model.parameters.outputLabel (congrArg (model.generatedToken (promptInput prompt input)) ht))

end CausalToken
