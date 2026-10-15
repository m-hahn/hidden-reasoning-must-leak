import ConcreteReasoning

/-!
# Private bits in a single full-vocabulary matrix model

The private seed occupies additional input wires of the same Transformer.
Fixing a seed changes only literals, not weights, architecture, vocabulary,
separator, or positional encodings. The trace is the actual first-separator
word. Both the information loss and the expected-length bound are proved for
the explicit uniform independent input/seed distribution.
-/

noncomputable section

namespace Autoregressive.ContextLiteral

open TransformerAC0

def fixSeed (literal : ContextLiteral (n + r)) (seed : Bits r) : ContextLiteral n :=
  match literal with
  | .constant value => .constant value
  | .positive index => Fin.addCases (fun i => .positive i) (fun j => .constant (seed j)) index
  | .negative index => Fin.addCases (fun i => .negative i) (fun j => .constant (!(seed j))) index

@[simp] theorem eval_fixSeed (literal : ContextLiteral (n + r)) (seed : Bits r) (input : Bits n) :
    (literal.fixSeed seed).eval input = literal.eval (Fin.append input seed) := by
  cases literal with
  | constant value => rfl
  | positive index =>
      refine Fin.addCases (fun i => ?_) (fun j => ?_) index
      · simp [fixSeed, eval]
      · simp [fixSeed, eval, Fin.addCases_right]
  | negative index =>
      refine Fin.addCases (fun i => ?_) (fun j => ?_) index
      · simp [fixSeed, eval]
      · simp [fixSeed, eval, Fin.addCases_right]

end Autoregressive.ContextLiteral

namespace TokenAutoregressive

namespace Core

open TransformerAC0 Autoregressive

def fixSeed (core : Core (n + r)) (seed : Bits r) : Core n where
  architecture := core.architecture
  transformer := core.transformer
  vocabulary_positive := core.vocabulary_positive
  context_positive := core.context_positive
  separator := core.separator
  context := fun time prefixTokens wire => (core.context time prefixTokens wire).fixSeed seed
  prefixLength := core.prefixLength

@[simp] theorem fixSeed_generatedToken (core : Core (n + r)) (seed : Bits r)
    (input : Bits n) (time : ℕ) :
    (core.fixSeed seed).generatedToken input time = core.generatedToken (Fin.append input seed) time := by
  induction time using Nat.strong_induction_on with
  | h time ih =>
      rw [generatedToken, generatedToken]
      change (core.stepTransformer time).runToken core.vocabulary_positive (core.prefixLength time).property.1 _ =
        (core.stepTransformer time).runToken core.vocabulary_positive (core.prefixLength time).property.1 _
      congr 1
      funext wire
      change ((core.context time
        (fun previous => (core.fixSeed seed).generatedToken input previous) (core.inputWire time wire)).fixSeed seed).eval input = _
      rw [ContextLiteral.eval_fixSeed]
      congr 2
      funext previous
      exact ih previous previous.isLt

end Core

namespace Generator

open TransformerAC0 Autoregressive FiniteInformation

variable {n r bound : ℕ}

def fixSeed (model : Generator (n + r) bound) (seed : Bits r) : Generator n bound where
  core := model.core.fixSeed seed
  terminates := by
    intro input
    obtain ⟨time, htime, hsep⟩ := model.terminates (Fin.append input seed)
    exact ⟨time, htime, by rw [Core.fixSeed_generatedToken]; exact hsep⟩

@[simp] theorem fixSeed_length (model : Generator (n + r) bound) (seed : Bits r) (input : Bits n) :
    (model.fixSeed seed).length input = model.length (Fin.append input seed) := by
  apply Fin.ext
  apply le_antisymm
  · apply Nat.find_min' ((model.fixSeed seed).terminates input)
    have h := Nat.find_spec (model.terminates (Fin.append input seed))
    refine ⟨h.1, ?_⟩
    change (model.core.fixSeed seed).generatedToken input _ = model.core.separator
    rw [Core.fixSeed_generatedToken]
    exact h.2
  · apply Nat.find_min' (model.terminates (Fin.append input seed))
    have h := Nat.find_spec ((model.fixSeed seed).terminates input)
    have hs := h.2
    change (model.core.fixSeed seed).generatedToken input _ = model.core.separator at hs
    rw [Core.fixSeed_generatedToken] at hs
    exact ⟨h.1, hs⟩

@[simp] theorem fixSeed_transcript (model : Generator (n + r) bound) (seed : Bits r) (input : Bits n) :
    (model.fixSeed seed).transcript input = model.transcript (Fin.append input seed) := by
  have word_eq {firstCount secondCount : Fin (bound + 1)}
      (first : Fin firstCount.val → model.Nonterminal)
      (second : Fin secondCount.val → model.Nonterminal)
      (hcount : firstCount = secondCount)
      (htokens : ∀ i j, i.val = j.val → first i = second j) :
      (⟨firstCount, first⟩ : model.Transcript) = ⟨secondCount, second⟩ := by
    subst secondCount
    congr 1
    funext i
    exact htokens i i rfl
  apply word_eq _ _ (model.fixSeed_length seed input)
  intro i j hij
  apply Subtype.ext
  change (model.core.fixSeed seed).generatedToken input i.val =
    model.core.generatedToken (Fin.append input seed) j.val
  rw [Core.fixSeed_generatedToken, hij]

@[simp] theorem fixSeed_answer (model : Generator (n + r) bound) (seed : Bits r) (input : Bits n) :
    (model.fixSeed seed).answer input = model.answer (Fin.append input seed) := by
  unfold answer
  rw [fixSeed_length]
  exact congrArg model.core.transformer.outputLabel (model.core.fixSeed_generatedToken seed input _)

@[simp] theorem fixSeed_fiberDepth (model : Generator (n + r) bound) (seed : Bits r) :
    (model.fixSeed seed).fiberDepth = model.fiberDepth := rfl

@[simp] theorem fixSeed_fiberSize (model : Generator (n + r) bound) (seed : Bits r) :
    (model.fixSeed seed).fiberSize = model.fiberSize := rfl

def seededTrace (model : Generator (n + r) bound) (pair : Bits n × Bits r) : model.Transcript :=
  model.transcript (Fin.append pair.1 pair.2)

def seededExpectedLength (model : Generator (n + r) bound) : ℝ :=
  (Distribution.uniform (Bits n × Bits r)).expectation
    (fun pair => ((model.length (Fin.append pair.1 pair.2)).val + 1 : ℕ))

theorem seedwise_footprint (tal : Tal.FourierTailTheorem) (model : Generator (n + r) bound)
    (correct : ∀ input seed, model.answer (Fin.append input seed) = Tal.parity input) (hn : 1 ≤ n)
    (seed : Bits r) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (Distribution.uniform (Bits n)).entropy (fun input => model.seededTrace (input, seed)) := by
  have hcorrect : ∀ input, (model.fixSeed seed).answer input = Tal.parity input := by
    intro input
    rw [fixSeed_answer, correct]
  have h := (model.fixSeed seed).footprint tal hcorrect hn
  rw [Distribution.mutualInformation_id_eq_entropy] at h
  have htrace : (model.fixSeed seed).transcript =
      fun input => model.seededTrace (input, seed) := by
    funext input
    exact model.fixSeed_transcript seed input
  rw [htrace] at h
  simpa only [fixSeed_fiberDepth, fixSeed_fiberSize] using h

/-- The actual private-seed information bound; no seed-indexed matrix family
or private-randomness entropy law is assumed. -/
theorem seeded_footprint (tal : Tal.FourierTailTheorem) (model : Generator (n + r) bound)
    (correct : ∀ input seed, model.answer (Fin.append input seed) = Tal.parity input) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) - (r : ℝ) ≤
      (Distribution.uniform (Bits n × Bits r)).mutualInformation Prod.fst model.seededTrace := by
  have hbits : Real.logb 2 (Fintype.card (Bits r)) = (r : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
    rw [Real.logb, Real.log_pow]
    have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog]
  rw [← hbits]
  exact Distribution.private_randomness_information_lower_bound model.seededTrace _
    (model.seedwise_footprint tal correct hn)

/-- The seed costs at most `r` bits of information, but cannot lower the
expected number of full-vocabulary tokens needed for the computation. -/
theorem seeded_expected_length_lower_bound
    (tal : Tal.FourierTailTheorem) (model : Generator (n + r) bound)
    (correct : ∀ input seed, model.answer (Fin.append input seed) = Tal.parity input) (hn : 1 ≤ n)
    (hv : 1 < model.core.architecture.vocabulary) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.seededExpectedLength := by
  have hcard := model.nonterminal_card
  have hpositive : 0 < Fintype.card model.Nonterminal := by omega
  have htotal : Fintype.card model.Nonterminal + 1 = model.core.architecture.vocabulary := by omega
  have h := ConcreteReasoning.randomness_expected_length_lower_bound model.seededTrace _
    (model.seedwise_footprint tal correct hn) (Fintype.card model.Nonterminal) hpositive
    model.payload model.payload_injective
  rw [htotal] at h
  simpa [seededExpectedLength, seededTrace, payload, transcript] using h

/-- Public values may be correlated with the covert input and with the seed.
The only distribution conditions are actual uniform public masses and an
actual decoder from the emitted word. -/
theorem seeded_public_length_tax
    (tal : Tal.FourierTailTheorem) (model : Generator (n + r) bound)
    (correct : ∀ input seed, model.answer (Fin.append input seed) = Tal.parity input) (hn : 1 ≤ n)
    (hv : 1 < model.core.architecture.vocabulary)
    (publicLength inputAlphabetCard : ℕ) (hinput : 0 < inputAlphabetCard)
    (public : Bits n × Bits r → (Fin publicLength → Fin inputAlphabetCard))
    (decode : model.Transcript → (Fin publicLength → Fin inputAlphabetCard))
    (recoverable : ∀ pair, decode (model.seededTrace pair) = public pair)
    (uniformPublic : ∀ p, (Distribution.uniform (Bits n × Bits r)).pushMass public p =
      1 / (Fintype.card (Fin publicLength → Fin inputAlphabetCard) : ℝ)) :
    ((publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) -
        Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) - (r : ℝ) -
        (Distribution.uniform (Bits n × Bits r)).mutualInformation Prod.fst public) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.seededExpectedLength := by
  let D := Distribution.uniform (Bits n × Bits r)
  have hpair := D.mutualInformation_recoverable_pair Prod.fst public model.seededTrace decode recoverable
  have hfootprint := model.seeded_footprint tal correct hn
  have hcard := model.nonterminal_card
  have hpositive : 0 < Fintype.card model.Nonterminal := by omega
  have htotal : Fintype.card model.Nonterminal + 1 = model.core.architecture.vocabulary := by omega
  have h := ConcreteReasoning.hidden_reasoning_tax D Prod.fst publicLength inputAlphabetCard
    (Fintype.card model.Nonterminal) hinput hpositive public model.seededTrace decode recoverable
    uniformPublic model.payload model.payload_injective
    (-Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) - (r : ℝ))
    (by rw [hpair]; exact hfootprint)
  rw [htotal] at h
  simpa [D, seededExpectedLength, seededTrace, payload, transcript, sub_eq_add_neg, add_assoc] using h

/-- Multiplication uses the same seed restriction and the already proved
elementary middle-bit Fourier estimate. -/
theorem seedwise_multiplication_footprint
    (tal : Tal.FourierTailTheorem) (model : Generator ((N + N) + r) bound)
    (correct : ∀ input seed,
      model.answer (Fin.append input seed) = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) (seed : Bits r) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) ≤
      (Distribution.uniform (Bits (N + N))).entropy (fun input => model.seededTrace (input, seed)) := by
  have hcorrect : ∀ input, (model.fixSeed seed).answer input =
      MultiplicationFootprint.middleBitTarget N input := by
    intro input
    rw [fixSeed_answer, correct]
  have h := ConcreteReasoning.token_multiplication_footprint tal (model.fixSeed seed) hcorrect hN
  rw [Distribution.mutualInformation_id_eq_entropy] at h
  have htrace : (model.fixSeed seed).transcript =
      fun input => model.seededTrace (input, seed) := by
    funext input
    exact model.fixSeed_transcript seed input
  rw [htrace] at h
  simpa only [fixSeed_fiberDepth, fixSeed_fiberSize] using h

theorem seeded_multiplication_footprint
    (tal : Tal.FourierTailTheorem) (model : Generator ((N + N) + r) bound)
    (correct : ∀ input seed,
      model.answer (Fin.append input seed) = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) - (r : ℝ) ≤
      (Distribution.uniform (Bits (N + N) × Bits r)).mutualInformation Prod.fst model.seededTrace := by
  have hbits : Real.logb 2 (Fintype.card (Bits r)) = (r : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
    rw [Real.logb, Real.log_pow]
    have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog]
  rw [← hbits]
  exact Distribution.private_randomness_information_lower_bound model.seededTrace _
    (model.seedwise_multiplication_footprint tal correct hN)

theorem seeded_multiplication_expected_length_lower_bound
    (tal : Tal.FourierTailTheorem) (model : Generator ((N + N) + r) bound)
    (correct : ∀ input seed,
      model.answer (Fin.append input seed) = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) (hv : 1 < model.core.architecture.vocabulary) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.seededExpectedLength := by
  have hcard := model.nonterminal_card
  have hpositive : 0 < Fintype.card model.Nonterminal := by omega
  have htotal : Fintype.card model.Nonterminal + 1 = model.core.architecture.vocabulary := by omega
  have h := ConcreteReasoning.randomness_expected_length_lower_bound model.seededTrace _
    (model.seedwise_multiplication_footprint tal correct hN) (Fintype.card model.Nonterminal) hpositive
    model.payload model.payload_injective
  rw [htotal] at h
  simpa [seededExpectedLength, seededTrace, payload, transcript] using h

end Generator

end TokenAutoregressive
