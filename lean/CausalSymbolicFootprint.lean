import CausalSymbolicToken

/-! # Entropy of the native prefix, including its separator

This interface lemma is proved for abstract numerical matrices, so callers
need not normalize a concrete matrix constructor inside an entropy proof.
-/
noncomputable section
namespace CausalSymbolicToken
open TransformerAC0 UniformTaskFootprint FiniteInformation
variable {a : Architecture} {front n bound : ℕ} {Alphabet : Type*}
variable [Fintype Alphabet] [DecidableEq Alphabet]
variable (model : CausalAutoregressive.Model a front (bound + 1))
variable (prompt : Fin (front * a.vocabulary) → SymbolLiteral n Alphabet) (separator : Fin a.vocabulary)
variable (boundary : ℕ) (hboundary : boundary ≤ bound)
variable (stops : ∀ input : Fin n → Alphabet, model.generatedToken (promptInput prompt input) ⟨boundary, by omega⟩ = separator)
variable (before : ∀ (input : Fin n → Alphabet) (time : Fin boundary), model.generatedToken (promptInput prompt input)
  ⟨time.val, by have h := time.isLt; omega⟩ ≠ separator)

def nativePrefix (input : Fin n → Alphabet) : Fin (boundary + 1) → Fin a.vocabulary := fun time =>
  model.generatedToken (promptInput prompt input) ⟨time.val, by have h := time.isLt; omega⟩

def recoverPrefix (fallback : {token : Fin a.vocabulary // token ≠ separator})
    (word : Fin (boundary + 1) → Fin a.vocabulary) :
    (generator model prompt separator boundary hboundary stops).Transcript :=
  ⟨⟨boundary, by omega⟩, fun time => if h : word time.castSucc = separator then fallback else ⟨word time.castSucc, h⟩⟩

include before in
theorem recoverPrefix_correct (fallback : {token : Fin a.vocabulary // token ≠ separator}) (input : Fin n → Alphabet) :
    recoverPrefix model prompt separator boundary hboundary stops fallback (nativePrefix model prompt boundary hboundary input) =
      (generator model prompt separator boundary hboundary stops).transcript input := by
  let G := generator model prompt separator boundary hboundary stops
  have word_eq {firstCount secondCount : Fin (bound + 1)}
      (first : Fin firstCount.val → G.Nonterminal) (second : Fin secondCount.val → G.Nonterminal)
      (hcount : firstCount = secondCount) (htokens : ∀ i j, i.val = j.val → first i = second j) :
      (⟨firstCount, first⟩ : G.Transcript) = ⟨secondCount, second⟩ := by
    subst secondCount
    congr 1
    funext i
    exact htokens i i rfl
  apply word_eq _ _ (Fin.ext (length_eq model prompt separator boundary hboundary stops before input).symm)
  intro i j hij
  have hne : nativePrefix model prompt boundary hboundary input i.castSucc ≠ separator := before input i
  apply Subtype.ext
  simp only [recoverPrefix, hne, ↓reduceDIte]
  have h := generated_correct model prompt separator input ⟨i.val, by have ht := i.isLt; omega⟩
  change model.generatedToken _ _ = (core model prompt separator).generatedToken input j.val
  rw [← hij]
  exact h.symm

include before in
theorem entropy_prefix (D : Distribution (Fin n → Alphabet))
    (fallback : {token : Fin a.vocabulary // token ≠ separator}) :
    D.entropy (generator model prompt separator boundary hboundary stops).transcript ≤
      D.entropy (nativePrefix model prompt boundary hboundary) :=
  D.entropy_mono_of_comp _ _ (recoverPrefix model prompt separator boundary hboundary stops fallback)
    (recoverPrefix_correct model prompt separator boundary hboundary stops before fallback)

end CausalSymbolicToken
