import Encryption
import EntropyCoding
import MultiplicationFootprint
import TerminatedAutoregressive
import TokenAutoregressive

/-!
# Concrete information-theoretic consequences

The finite distributions and random variables in this file determine every
entropy and mutual information in its statements.  The public-input tax uses
the proved separator coding bound; the private-randomness theorem uses the
proved entropy inequality for uniform independent inputs.  Neither theorem
accepts an entropy profile or information-law certificate.
-/

noncomputable section

open scoped BigOperators

namespace ConcreteReasoning

open TransformerAC0 FiniteInformation

/-- The correlated public/covert length tax for an explicit finite joint
distribution.  Public recoverability and the uniform public marginal are the
assumptions of the paper's theorem, stated here as equalities of actual maps
and probability masses.  Source coding and entropy monotonicity are proved
internally. -/
theorem hidden_reasoning_tax
    {Ω Covert Trace : Type*} [Fintype Ω] [Fintype Covert] [Fintype Trace]
    [DecidableEq Covert] [DecidableEq Trace]
    (D : Distribution Ω) (covert : Ω → Covert)
    (publicLength inputAlphabetCard dataCard : ℕ) (hinput : 0 < inputAlphabetCard)
    (hdata : 0 < dataCard)
    (public : Ω → (Fin publicLength → Fin inputAlphabetCard)) (trace : Ω → Trace)
    (decode : Trace → (Fin publicLength → Fin inputAlphabetCard))
    (recoverable : ∀ ω, decode (trace ω) = public ω)
    (uniformPublic : ∀ p, D.pushMass public p =
      1 / (Fintype.card (Fin publicLength → Fin inputAlphabetCard) : ℝ))
    (payload : Trace → List (Fin dataCard)) (encode_injective : Function.Injective payload)
    (footprintLower : ℝ)
    (footprint : footprintLower ≤ D.mutualInformation covert
      (fun ω => (public ω, trace ω))) :
    ((publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) +
        footprintLower - D.mutualInformation covert public) /
        Real.logb 2 (dataCard + 1 : ℕ) ≤
      D.expectation (fun ω => ((payload (trace ω)).length + 1 : ℕ)) := by
  letI : Nonempty (Fin inputAlphabetCard) := Fin.pos_iff_nonempty.mp hinput
  have hpublic := D.entropy_of_uniform_pushMass public uniformPublic
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow,
    Real.logb, Real.log_pow] at hpublic
  have hpublic' : D.entropy public =
      (publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) := by
    rw [hpublic, Real.logb]
    ring
  have htrade := D.entropy_tradeoff covert public trace decode recoverable
  have hcoding := TerminatedCode.entropy_le_expected_terminated_length D trace
    dataCard hdata payload encode_injective
  have hlog : 0 < Real.logb 2 (dataCard + 1 : ℕ) := by
    apply Real.logb_pos (by norm_num)
    exact_mod_cast (show 1 < dataCard + 1 by omega)
  apply (div_le_iff₀ hlog).2
  rw [hpublic'] at htrade
  linarith

/-- The correlated public-input tax composed with a variable-length matrix
parity computation. The only imported theorem is Tal; neither a footprint
premise nor an information/source-coding profile is supplied. -/
theorem terminated_hidden_reasoning_tax
    (tal : Tal.FourierTailTheorem)
    (model : TerminatedAutoregressive.Generator n bound)
    (correct : ∀ input, model.answer input = Tal.parity input) (hn : 1 ≤ n)
    (publicLength inputAlphabetCard : ℕ) (hinput : 0 < inputAlphabetCard)
    (public : Bits n → (Fin publicLength → Fin inputAlphabetCard))
    (decode : TerminatedAutoregressive.Transcript bound → (Fin publicLength → Fin inputAlphabetCard))
    (recoverable : ∀ input, decode (model.transcript input) = public input)
    (uniformPublic : ∀ p, (Distribution.uniform (Bits n)).pushMass public p =
      1 / (Fintype.card (Fin publicLength → Fin inputAlphabetCard) : ℝ)) :
    ((publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) -
        Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) -
        (Distribution.uniform (Bits n)).mutualInformation id public) /
        Real.logb 2 3 ≤ model.expectedLength := by
  have hfootprint := model.footprint tal correct hn
  have hpair := (Distribution.uniform (Bits n)).mutualInformation_recoverable_pair
    id public model.transcript decode recoverable
  have h := hidden_reasoning_tax (Distribution.uniform (Bits n)) id
    publicLength inputAlphabetCard 2 hinput (by decide) public model.transcript
    decode recoverable uniformPublic TerminatedAutoregressive.Generator.payload
    TerminatedAutoregressive.Generator.payload_injective
    (-Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)))
    (by rw [hpair]; exact hfootprint)
  simpa [TerminatedAutoregressive.Generator.payload,
    TerminatedAutoregressive.Generator.expectedLength,
    TerminatedAutoregressive.Generator.transcript, sub_eq_add_neg] using h

/-- The middle multiplication bit has the same separator-terminated
variable-length footprint, using the elementary low-degree estimate. -/
theorem terminated_multiplication_footprint
    (tal : Tal.FourierTailTheorem)
    (model : TerminatedAutoregressive.Generator (N + N) bound)
    (correct : ∀ input, model.answer input = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) ≤
      (Distribution.uniform (Bits (N + N))).mutualInformation id model.transcript := by
  have hsize : 1 < model.fiberSize := by
    unfold TerminatedAutoregressive.Generator.fiberSize; omega
  have hrate := MultiplicationFootprint.correlationRate_pos N model.fiberDepth model.fiberSize
  have hleft : 0 < MultiplicationFootprint.correlationRate N model.fiberDepth model.fiberSize +
      |TaskFootprint.targetBias (MultiplicationFootprint.middleBitTarget N)| := by positivity
  have hraw := model.task_footprint (MultiplicationFootprint.middleBitTarget N) correct
    (MultiplicationFootprint.correlationRate N model.fiberDepth model.fiberSize)
    (MultiplicationFootprint.middleBit_signCorrelationBound tal hN hsize) hleft
  have hsmall := MultiplicationFootprint.correlationRate_add_bias_le_explicit N
    model.fiberDepth model.fiberSize hN
  have hright := MultiplicationFootprint.explicitFiberRate_pos N model.fiberDepth model.fiberSize
  have hlog : Real.logb 2 (MultiplicationFootprint.correlationRate N model.fiberDepth model.fiberSize +
      |TaskFootprint.targetBias (MultiplicationFootprint.middleBitTarget N)|) ≤
      Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) :=
    (Real.logb_le_logb (by norm_num) hleft hright).mpr hsmall
  linarith

theorem terminated_multiplication_expected_length
    (tal : Tal.FourierTailTheorem)
    (model : TerminatedAutoregressive.Generator (N + N) bound)
    (correct : ∀ input, model.answer input = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) /
      Real.logb 2 3 ≤ model.expectedLength := by
  have hfootprint := terminated_multiplication_footprint tal model correct hN
  rw [Distribution.mutualInformation_id_eq_entropy] at hfootprint
  apply (div_le_iff₀ (Real.logb_pos (by norm_num) (by norm_num) : 0 < Real.logb 2 (3 : ℝ))).mpr
  exact hfootprint.trans model.entropy_le_expected_length

/-- The public/covert tax for the entire vocabulary trace of a greedy matrix
Transformer, with the paper's actual `log₂ |Γ|` denominator. -/
theorem token_hidden_reasoning_tax
    (tal : Tal.FourierTailTheorem) (model : TokenAutoregressive.Generator n bound)
    (correct : ∀ input, model.answer input = Tal.parity input) (hn : 1 ≤ n)
    (hv : 1 < model.core.architecture.vocabulary)
    (publicLength inputAlphabetCard : ℕ) (hinput : 0 < inputAlphabetCard)
    (public : Bits n → (Fin publicLength → Fin inputAlphabetCard))
    (decode : model.Transcript → (Fin publicLength → Fin inputAlphabetCard))
    (recoverable : ∀ input, decode (model.transcript input) = public input)
    (uniformPublic : ∀ p, (Distribution.uniform (Bits n)).pushMass public p =
      1 / (Fintype.card (Fin publicLength → Fin inputAlphabetCard) : ℝ)) :
    ((publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) -
        Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) -
        (Distribution.uniform (Bits n)).mutualInformation id public) /
        Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.expectedLength := by
  have hfootprint := model.footprint tal correct hn
  have hpair := (Distribution.uniform (Bits n)).mutualInformation_recoverable_pair
    id public model.transcript decode recoverable
  have hcard := model.nonterminal_card
  have hpositive : 0 < Fintype.card model.Nonterminal := by omega
  have htotal : Fintype.card model.Nonterminal + 1 = model.core.architecture.vocabulary := by omega
  have h := hidden_reasoning_tax (Distribution.uniform (Bits n)) id
    publicLength inputAlphabetCard (Fintype.card model.Nonterminal) hinput hpositive
    public model.transcript decode recoverable uniformPublic model.payload model.payload_injective
    (-Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)))
    (by rw [hpair]; exact hfootprint)
  rw [htotal] at h
  simpa [TokenAutoregressive.Generator.payload, TokenAutoregressive.Generator.expectedLength,
    TokenAutoregressive.Generator.transcript, sub_eq_add_neg] using h

theorem token_multiplication_footprint
    (tal : Tal.FourierTailTheorem) (model : TokenAutoregressive.Generator (N + N) bound)
    (correct : ∀ input, model.answer input = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) ≤
      (Distribution.uniform (Bits (N + N))).mutualInformation id model.transcript := by
  have hsize : 1 < model.fiberSize := by unfold TokenAutoregressive.Generator.fiberSize; omega
  have hrate := MultiplicationFootprint.correlationRate_pos N model.fiberDepth model.fiberSize
  have hpositive : 0 < MultiplicationFootprint.correlationRate N model.fiberDepth model.fiberSize +
      |TaskFootprint.targetBias (MultiplicationFootprint.middleBitTarget N)| := by positivity
  have hraw := model.task_footprint (MultiplicationFootprint.middleBitTarget N) correct
    (MultiplicationFootprint.correlationRate N model.fiberDepth model.fiberSize)
    (MultiplicationFootprint.middleBit_signCorrelationBound tal hN hsize) hpositive
  have hlog : Real.logb 2 (MultiplicationFootprint.correlationRate N model.fiberDepth model.fiberSize +
      |TaskFootprint.targetBias (MultiplicationFootprint.middleBitTarget N)|) ≤
      Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) :=
    (Real.logb_le_logb (by norm_num) hpositive
      (MultiplicationFootprint.explicitFiberRate_pos N model.fiberDepth model.fiberSize)).mpr
      (MultiplicationFootprint.correlationRate_add_bias_le_explicit N model.fiberDepth model.fiberSize hN)
  linarith

theorem token_multiplication_expected_length
    (tal : Tal.FourierTailTheorem) (model : TokenAutoregressive.Generator (N + N) bound)
    (correct : ∀ input, model.answer input = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) (hv : 1 < model.core.architecture.vocabulary) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.fiberDepth model.fiberSize) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.expectedLength := by
  have hfootprint := token_multiplication_footprint tal model correct hN
  rw [Distribution.mutualInformation_id_eq_entropy] at hfootprint
  have hlog : 0 < Real.logb 2 (model.core.architecture.vocabulary : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hv)
  apply (div_le_iff₀ hlog).mpr
  exact hfootprint.trans (model.entropy_le_expected_length hv)

namespace TerminatedSeeded

abbrev Family (n seedLength bound : ℕ) :=
  Bits seedLength → TerminatedAutoregressive.Generator n bound

def depth (models : Family n seedLength bound) : ℕ :=
  Finset.univ.sup fun seed => (models seed).fiberDepth

def size (models : Family n seedLength bound) : ℕ :=
  2 + Finset.univ.sup fun seed => (models seed).fiberSize

def visibleTrace (models : Family n seedLength bound) (pair : Bits n × Bits seedLength) :
    TerminatedAutoregressive.Transcript bound := (models pair.2).transcript pair.1

def circuits (models : Family n seedLength bound)
    (correct : ∀ seed input, (models seed).answer input = Tal.parity input)
    (seed : Bits seedLength) :
    Footprint.FiberCircuitFamily ((models seed).parityTrace (correct seed))
      (depth models) (size models) where
  circuit := (models seed).fiberCircuit
  correct := fun candidate answer input => (models seed).eval_fiberCircuit input candidate answer
  depth_le := by
    intro candidate answer
    exact ((models seed).fiberCircuit_depth_le candidate answer).trans
      (Finset.le_sup (s := Finset.univ) (f := fun seed => (models seed).fiberDepth) (by simp))
  size_le := by
    intro candidate answer
    have h := Finset.le_sup (s := Finset.univ)
      (f := fun seed => (models seed).fiberSize) (by simp : seed ∈ Finset.univ)
    exact ((models seed).fiberCircuit_size_le candidate answer).trans
      (h.trans (Nat.le_add_left _ _))

theorem fixed_seed_footprint
    (tal : Tal.FourierTailTheorem) (models : Family n seedLength bound)
    (correct : ∀ seed input, (models seed).answer input = Tal.parity input) (hn : 1 ≤ n)
    (seed : Bits seedLength) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound (depth models) (size models) n)) ≤
      (Distribution.uniform (Bits n)).entropy (fun input => visibleTrace models (input, seed)) := by
  have h := Footprint.footprint_from_tal tal ((models seed).parityTrace (correct seed))
    (circuits models correct seed) hn (by unfold size; omega)
  unfold Footprint.ParityTrace.uniformMutualInformation at h
  rw [← EntropyCoding.uniform_entropy_eq_transcriptEntropy] at h
  exact h

theorem randomness_footprint
    (tal : Tal.FourierTailTheorem) (models : Family n seedLength bound)
    (correct : ∀ seed input, (models seed).answer input = Tal.parity input) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound (depth models) (size models) n)) - (seedLength : ℝ) ≤
      (Distribution.uniform (Bits n × Bits seedLength)).mutualInformation Prod.fst (visibleTrace models) := by
  have hbits : Real.logb 2 (Fintype.card (Bits seedLength)) = (seedLength : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
    rw [Real.logb, Real.log_pow]
    have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog]
  rw [← hbits]
  exact Distribution.private_randomness_information_lower_bound (visibleTrace models) _
    (fixed_seed_footprint tal models correct hn)

/-- General correlated public/covert expected-length tax, including a private
seed used to choose the public input. All probabilities refer to the actual
uniform independent input/seed pair. The public marginal and public recovery
conditions are the paper's own task conditions. -/
theorem correlated_public_expected_length_tax
    (tal : Tal.FourierTailTheorem) (models : Family n seedLength bound)
    (correct : ∀ seed input, (models seed).answer input = Tal.parity input) (hn : 1 ≤ n)
    (publicLength inputAlphabetCard : ℕ) (hinput : 0 < inputAlphabetCard)
    (public : Bits n × Bits seedLength → (Fin publicLength → Fin inputAlphabetCard))
    (decode : TerminatedAutoregressive.Transcript bound → (Fin publicLength → Fin inputAlphabetCard))
    (recoverable : ∀ pair, decode (visibleTrace models pair) = public pair)
    (uniformPublic : ∀ p, (Distribution.uniform (Bits n × Bits seedLength)).pushMass public p =
      1 / (Fintype.card (Fin publicLength → Fin inputAlphabetCard) : ℝ)) :
    ((publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) -
        Real.logb 2 (Real.sqrt (Tal.tailBound (depth models) (size models) n)) - (seedLength : ℝ) -
        (Distribution.uniform (Bits n × Bits seedLength)).mutualInformation Prod.fst public) /
        Real.logb 2 3 ≤
      (Distribution.uniform (Bits n × Bits seedLength)).expectation
        (fun pair => (((models pair.2).length pair.1).val + 1 : ℕ)) := by
  let D := Distribution.uniform (Bits n × Bits seedLength)
  have hpair := D.mutualInformation_recoverable_pair Prod.fst public (visibleTrace models) decode recoverable
  have hfootprint := randomness_footprint tal models correct hn
  have h := hidden_reasoning_tax D Prod.fst publicLength inputAlphabetCard 2 hinput (by decide)
    public (visibleTrace models) decode recoverable uniformPublic
    TerminatedAutoregressive.Generator.payload TerminatedAutoregressive.Generator.payload_injective
    (-Real.logb 2 (Real.sqrt (Tal.tailBound (depth models) (size models) n)) - (seedLength : ℝ))
    (by rw [hpair]; exact hfootprint)
  simpa [D, visibleTrace, TerminatedAutoregressive.Generator.payload,
    TerminatedAutoregressive.Generator.transcript, sub_eq_add_neg, add_assoc] using h

end TerminatedSeeded

namespace SeededGenerator

variable {n seedLength length : ℕ}

abbrev Family (n seedLength length : ℕ) :=
  Bits seedLength → Autoregressive.FixedPrecisionGenerator n length

/-- An architecture-independent common bound obtained from the actual
compiled matrix circuits for every seed. -/
def depth (models : Family n seedLength length) : ℕ :=
  Finset.univ.sup fun seed => (models seed).explicitFiberDepth

def size (models : Family n seedLength length) : ℕ :=
  2 + Finset.univ.sup fun seed => (models seed).explicitFiberSize

def visibleTrace (models : Family n seedLength length)
    (pair : Bits n × Bits seedLength) : Bits length :=
  (models pair.2).transcript pair.1

def circuits (models : Family n seedLength length)
    (correct : ∀ seed input, (models seed).answer input = Tal.parity input)
    (seed : Bits seedLength) :
    Footprint.FiberCircuitFamily ((models seed).parityTrace (correct seed))
      (depth models) (size models) where
  circuit := (models seed).fiberCircuit
  correct := (models seed).eval_fiberCircuit
  depth_le := by
    intro candidate answer
    exact ((models seed).depth_fiberCircuit_le candidate answer).trans
      (Finset.le_sup (s := Finset.univ) (f := fun seed => (models seed).explicitFiberDepth)
        (by simp))
  size_le := by
    intro candidate answer
    have h := Finset.le_sup (s := Finset.univ)
      (f := fun seed => (models seed).explicitFiberSize) (by simp : seed ∈ Finset.univ)
    have hlocal := (models seed).gateCount_fiberCircuit_le candidate answer
    unfold size
    exact hlocal.trans (h.trans (Nat.le_add_left _ _))

/-- The private-randomness footprint theorem for actual matrix-level
autoregressive executions.  Tal is the only imported theorem; every circuit
and every information quantity is computed from `models`. -/
theorem randomness_footprint_of_tal
    (tal : Tal.FourierTailTheorem) (models : Family n seedLength length)
    (correct : ∀ seed input, (models seed).answer input = Tal.parity input)
    (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound (depth models) (size models) n)) -
        (seedLength : ℝ) ≤
      (Distribution.uniform (Bits n × Bits seedLength)).mutualInformation
        Prod.fst (visibleTrace models) := by
  have hbits : Real.logb 2 (Fintype.card (Bits seedLength)) = (seedLength : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
    rw [Real.logb, Real.log_pow]
    have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog]
  rw [← hbits]
  apply Distribution.private_randomness_information_lower_bound (visibleTrace models)
  intro seed
  have h := Footprint.footprint_from_tal tal ((models seed).parityTrace (correct seed))
    (circuits models correct seed) hn (by unfold size; omega)
  unfold Footprint.ParityTrace.uniformMutualInformation at h
  rw [← EntropyCoding.uniform_entropy_eq_transcriptEntropy] at h
  exact h

end SeededGenerator

/-- The source-coding consequence of the seedwise footprint: private
randomness does not reduce the required expected trace length. -/
theorem randomness_expected_length_lower_bound
    {Input Seed Trace : Type*} [Fintype Input] [Fintype Seed] [Fintype Trace]
    [Nonempty Input] [Nonempty Seed] [DecidableEq Seed] [DecidableEq Trace]
    (trace : Input × Seed → Trace) (lower : ℝ)
    (fixedSeedFootprint : ∀ seed, lower ≤
      (Distribution.uniform Input).entropy (fun input => trace (input, seed)))
    (dataCard : ℕ) (hdata : 0 < dataCard)
    (payload : Trace → List (Fin dataCard)) (injective : Function.Injective payload) :
    lower / Real.logb 2 (dataCard + 1 : ℕ) ≤
      (Distribution.uniform (Input × Seed)).expectation
        (fun pair => ((payload (trace pair)).length + 1 : ℕ)) := by
  have hfootprint := Distribution.uniform_product_entropy_ge_lower trace lower fixedSeedFootprint
  have hcoding := TerminatedCode.entropy_le_expected_terminated_length
    (Distribution.uniform (Input × Seed)) trace dataCard hdata payload injective
  have hlog : 0 < Real.logb 2 (dataCard + 1 : ℕ) := by
    apply Real.logb_pos (by norm_num)
    exact_mod_cast (show 1 < dataCard + 1 by omega)
  apply (div_le_iff₀ hlog).2
  exact hfootprint.trans hcoding

/-- Fixed-pad XOR preserves every plaintext entropy exactly. -/
theorem encrypted_fixed_seed_entropy
    {Input : Type*} [Fintype Input]
    (D : Distribution Input) (plainTrace : Input → Bits length) (pad : Bits length) :
    D.entropy (fun input => Encryption.bitXor (plainTrace input) pad) = D.entropy plainTrace := by
  apply D.entropy_eq_of_comp
    (fun input => Encryption.bitXor (plainTrace input) pad) plainTrace
    (fun value => Encryption.bitXor value pad) (fun _ => rfl)
    (fun value => Encryption.bitXor value pad)
    (fun input => Encryption.bitXor_right_involutive (plainTrace input) pad)

/-- Leakage of an actual XOR ciphertext, with all information quantities
computed from its plaintext trace and private seed. -/
theorem encrypted_trace_information_lower_bound
    {Input : Type*} [Fintype Input] [Nonempty Input] [DecidableEq Input]
    (plainTrace : Input → Bits length) (generator : Bits seedLength → Bits length)
    (lower : ℝ) (footprint : lower ≤ (Distribution.uniform Input).entropy plainTrace) :
    lower - (seedLength : ℝ) ≤
      (Distribution.uniform (Input × Bits seedLength)).mutualInformation Prod.fst
        (fun pair => Encryption.encryptedTrace plainTrace generator pair.1 pair.2) := by
  have hbits : Real.logb 2 (Fintype.card (Bits seedLength)) = (seedLength : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
    rw [Real.logb, Real.log_pow]
    have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog]
  rw [← hbits]
  apply Distribution.private_randomness_information_lower_bound
  intro seed
  unfold Encryption.encryptedTrace
  dsimp only
  rw [encrypted_fixed_seed_entropy]
  exact footprint

/-- The leakage half of the paper's encrypted-reasoning theorem, directly
from Tal and an actual autoregressive plaintext Transformer. -/
theorem encrypted_autoregressive_footprint
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator n length)
    (correct : ∀ input, model.answer input = Tal.parity input)
    (generator : Bits seedLength → Bits length) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.explicitFiberDepth model.explicitFiberSize n)) -
        (seedLength : ℝ) ≤
      (Distribution.uniform (Bits n × Bits seedLength)).mutualInformation Prod.fst
        (fun pair => Encryption.encryptedTrace model.transcript generator pair.1 pair.2) := by
  apply encrypted_trace_information_lower_bound
  have h := model.footprint tal correct hn (by
    unfold Autoregressive.FixedPrecisionGenerator.explicitFiberSize; omega)
  unfold Footprint.ParityTrace.uniformMutualInformation at h
  rw [← EntropyCoding.uniform_entropy_eq_transcriptEntropy] at h
  exact h

end ConcreteReasoning
