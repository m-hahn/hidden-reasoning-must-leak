import Tal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The parity footprint theorem

This file proves the footprint theorem from the paper appendix.  The proof is
split at the same interface as the paper:

1. fixed-prefix simulation supplies small, shallow AC⁰ circuits recognizing
   the two answer-refined transcript fibers;
2. the cited AC⁰--parity correlation theorem bounds the correlation of each
   such circuit with parity;
3. exact correctness turns those two correlation bounds into a uniform upper
   bound on every transcript fiber;
4. the maximum-fiber bound gives a Shannon mutual-information lower bound.

The external circuit lower bound is represented by
`IndicatorParityCorrelationBound`.  Everything after that result, including
the easily missed conversion from a sign correlation bound to a `0/1`
indicator bound, is proved here without axioms or proof placeholders.
-/

open scoped BigOperators

noncomputable section

namespace Footprint

open TransformerAC0

/-! ## Uniform Boolean inputs and deterministic transcripts -/

/-- Parity of a Boolean input. -/
abbrev parity {n : ℕ} (input : Bits n) : Bool := Tal.parity input

/-- The usual `±1` encoding: `false ↦ 1`, `true ↦ -1`. -/
abbrev boolSign (b : Bool) : ℝ := Tal.boolSign b

/-- The `0/1` indicator of a Boolean value. -/
def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- Uniform expectation on `n` Boolean input bits. -/
abbrev uniformExpectation {n : ℕ} (f : Bits n → ℝ) : ℝ := Tal.uniformExpectation f

/--
A deterministic CoT computation of parity.  `answer_correct` is the paper's
zero-error assumption; it is what lets a next-answer-token circuit recognize
an answer-refined fiber without itself computing parity.
-/
structure ParityTrace (n : ℕ) (Transcript : Type*) where
  transcript : Bits n → Transcript
  answer : Bits n → Bool
  answer_correct : ∀ input, answer input = parity input

namespace ParityTrace

variable {n : ℕ} {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]

/-- Inputs producing a specified visible transcript. -/
def transcriptFiber (G : ParityTrace n Transcript) (τ : Transcript) : Finset (Bits n) :=
  Finset.univ.filter fun input => G.transcript input = τ

/-- Probability of a transcript under the uniform input distribution. -/
def transcriptProbability (G : ParityTrace n Transcript) (τ : Transcript) : ℝ :=
  (G.transcriptFiber τ).card / (2 ^ n : ℕ)

/-- Shannon entropy, in bits, of the deterministic transcript. -/
def transcriptEntropy (G : ParityTrace n Transcript) : ℝ :=
  ∑ τ, -(G.transcriptProbability τ) * Real.logb 2 (G.transcriptProbability τ)

/--
For a deterministic transcript, `I(X; CoT) = H(CoT)` because
`H(CoT | X) = 0`.  This is the finite uniform mutual information used in the
paper's theorem.
-/
def uniformMutualInformation (G : ParityTrace n Transcript) : ℝ :=
  G.transcriptEntropy

private theorem card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by
  simp [Bits, Fintype.card_congr (Equiv.refl (Bits n))]

theorem sum_fiber_card (G : ParityTrace n Transcript) :
    ∑ τ, (G.transcriptFiber τ).card = 2 ^ n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Bits n)))
    (t := (Finset.univ : Finset Transcript))
    (f := G.transcript) (by simp)
  simpa only [Finset.card_univ, transcriptFiber, card_bits] using h.symm

/-- Transcript probabilities form a probability distribution. -/
theorem sum_transcriptProbability (G : ParityTrace n Transcript) :
    ∑ τ, G.transcriptProbability τ = 1 := by
  classical
  rw [show (∑ τ, G.transcriptProbability τ) =
      (∑ τ, ((G.transcriptFiber τ).card : ℝ)) / (2 ^ n : ℕ) by
    simp only [transcriptProbability, Finset.sum_div]]
  rw [← Nat.cast_sum, G.sum_fiber_card]
  have hpow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  exact div_self hpow.ne'

omit [Fintype Transcript] in
theorem transcriptProbability_nonneg (G : ParityTrace n Transcript) (τ : Transcript) :
    0 ≤ G.transcriptProbability τ := by
  unfold transcriptProbability
  positivity

omit [Fintype Transcript] in
private theorem sum_indicator_eq_fiber_card
    (G : ParityTrace n Transcript) (τ : Transcript) :
    ∑ input, boolIndicator (decide (G.transcript input = τ)) =
      ((G.transcriptFiber τ).card : ℝ) := by
  classical
  rw [transcriptFiber, Finset.card_eq_sum_ones]
  push_cast
  simp [boolIndicator]

omit [Fintype Transcript] in
/-- Fiber probability is the uniform expectation of its indicator. -/
theorem transcriptProbability_eq_expectation
    (G : ParityTrace n Transcript) (τ : Transcript) :
    G.transcriptProbability τ =
      uniformExpectation (fun input =>
        boolIndicator (decide (G.transcript input = τ))) := by
  rw [transcriptProbability, uniformExpectation, Tal.uniformExpectation,
    sum_indicator_eq_fiber_card]

end ParityTrace

variable {n : ℕ} {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]

/-! ## The circuit/correlation interface -/

/--
The fixed-prefix circuits used in the appendix.  The circuit for `(τ,b)`
recognizes inputs whose complete transcript is `τ` and whose model-predicted
answer is `b`.  Exact correctness then identifies this with `B_{τ,b}`.
-/
structure FiberCircuitFamily (G : ParityTrace n Transcript) (depthBound sizeBound : ℕ) where
  circuit : Transcript → Bool → Circuit n 1
  correct : ∀ τ b input,
    Circuit.eval (circuit τ b) input 0 =
      decide (G.transcript input = τ ∧ G.answer input = b)
  depth_le : ∀ τ b, Circuit.depth (circuit τ b) ≤ depthBound
  size_le : ∀ τ b, Circuit.gateCount (circuit τ b) ≤ sizeBound

/--
The indicator form of the cited AC⁰--parity correlation bound.  A usual sign
bound `|E[(-1)^C χ]| ≤ ρ` implies this statement with `ρ/2`, since parity is
balanced and `1_C = (1 - (-1)^C)/2`.
-/
def IndicatorParityCorrelationBound (n depthBound sizeBound : ℕ) (ρ : ℝ) : Prop :=
  ∀ circuit : Circuit n 1,
    Circuit.depth circuit ≤ depthBound →
    Circuit.gateCount circuit ≤ sizeBound →
    |uniformExpectation (fun input =>
      boolIndicator (Circuit.eval circuit input 0) * boolSign (parity input))| ≤ ρ / 2

/-- The standard sign form of the AC⁰--parity correlation bound. -/
def SignParityCorrelationBound (n depthBound sizeBound : ℕ) (ρ : ℝ) : Prop :=
  ∀ circuit : Circuit n 1,
    Circuit.depth circuit ≤ depthBound →
    Circuit.gateCount circuit ≤ sizeBound →
    |uniformExpectation (fun input =>
      boolSign (Circuit.eval circuit input 0) * boolSign (parity input))| ≤ ρ

@[simp] private theorem parity_cons (head : Bool) (tail : Bits n) :
    parity (Fin.cons head tail) = Bool.xor head (parity tail) := rfl

private theorem sum_paritySign_succ (n : ℕ) :
    ∑ input : Bits (n + 1), boolSign (parity input) = 0 := by
  calc
    (∑ input : Bits (n + 1), boolSign (parity input)) =
        ∑ pair : Bool × Bits n,
          boolSign (parity (Fin.cons pair.1 pair.2)) := by
      exact (Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => Bool)
        (fun input => boolSign (parity input))).symm
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_bool]
      simp only [parity_cons, Bool.false_xor, Bool.true_xor, boolSign]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro tail _
      cases h : parity tail <;> simp [h]

private theorem expectation_paritySign_eq_zero (hn : 1 ≤ n) :
    uniformExpectation (fun input : Bits n => boolSign (parity input)) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [uniformExpectation, Tal.uniformExpectation, sum_paritySign_succ]
  simp

private theorem indicator_eq_one_sub_sign_div_two (b : Bool) :
    boolIndicator b = (1 - boolSign b) / 2 := by
  cases b <;> norm_num [boolIndicator, boolSign]

/--
For nonempty inputs, the usual sign correlation theorem implies its indicator
form.  This discharges explicitly the conversion left implicit in the paper's
fiber calculation.
-/
theorem indicatorParityCorrelationBound_of_sign
    (hn : 1 ≤ n) {ρ : ℝ}
    (correlation : SignParityCorrelationBound n depthBound sizeBound ρ) :
    IndicatorParityCorrelationBound n depthBound sizeBound ρ := by
  intro circuit hdepth hsize
  let signed := uniformExpectation (fun input : Bits n =>
    boolSign (Circuit.eval circuit input 0) * boolSign (parity input))
  have hsigned : |signed| ≤ ρ := correlation circuit hdepth hsize
  have hsumParity : ∑ input : Bits n, boolSign (parity input) = 0 := by
    have hz := expectation_paritySign_eq_zero (n := n) hn
    unfold uniformExpectation Tal.uniformExpectation at hz
    have hden : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    exact (div_eq_zero_iff).1 hz |>.resolve_right hden.ne'
  have hindicator : uniformExpectation (fun input : Bits n =>
      boolIndicator (Circuit.eval circuit input 0) * boolSign (parity input)) =
      -(1 / 2 : ℝ) * signed := by
    dsimp only [signed]
    unfold uniformExpectation Tal.uniformExpectation
    have hsum :
        (∑ input : Bits n,
          boolIndicator (Circuit.eval circuit input 0) * boolSign (parity input)) =
        -(1 / 2 : ℝ) *
          (∑ input : Bits n,
            boolSign (Circuit.eval circuit input 0) * boolSign (parity input)) := by
      calc
        (∑ input : Bits n,
            boolIndicator (Circuit.eval circuit input 0) * boolSign (parity input)) =
            ∑ input : Bits n,
              ((1 / 2 : ℝ) * boolSign (parity input) -
                (1 / 2 : ℝ) *
                  (boolSign (Circuit.eval circuit input 0) * boolSign (parity input))) := by
              apply Finset.sum_congr rfl
              intro input _
              rw [indicator_eq_one_sub_sign_div_two]
              ring
        _ = (1 / 2 : ℝ) * (∑ input : Bits n, boolSign (parity input)) -
              (1 / 2 : ℝ) * (∑ input : Bits n,
                boolSign (Circuit.eval circuit input 0) * boolSign (parity input)) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = -(1 / 2 : ℝ) * (∑ input : Bits n,
                boolSign (Circuit.eval circuit input 0) * boolSign (parity input)) := by
              rw [hsumParity]
              ring
    rw [hsum]
    ring
  rw [hindicator, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith

/-- Tal's full Fourier-tail theorem supplies the sign-correlation hypothesis. -/
theorem signParityCorrelationBound_of_tal
    (tal : Tal.FourierTailTheorem) (hsizeTwo : 1 < sizeBound) :
    SignParityCorrelationBound n depthBound sizeBound
      (Real.sqrt (Tal.tailBound depthBound sizeBound n)) := by
  intro circuit hdepth hsize
  simpa [Tal.circuitSign] using
    Tal.abs_parityCorrelation_le_sqrt_tailBound tal circuit depthBound sizeBound
      hdepth hsize hsizeTwo

omit [Fintype Transcript] in
private theorem fiber_indicator_identity (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound) (τ : Transcript) (input : Bits n) :
    boolIndicator (decide (G.transcript input = τ)) =
      (boolIndicator (Circuit.eval (C.circuit τ false) input 0) -
        boolIndicator (Circuit.eval (C.circuit τ true) input 0)) *
          boolSign (parity input) := by
  rw [C.correct, C.correct, G.answer_correct]
  by_cases hτ : G.transcript input = τ <;>
    cases hp : parity input <;>
    simp [boolIndicator, boolSign, hτ, hp]

omit [Fintype Transcript] in
private theorem expectation_fiber_identity (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound) (τ : Transcript) :
    uniformExpectation (fun input =>
      boolIndicator (decide (G.transcript input = τ))) =
      uniformExpectation (fun input =>
        boolIndicator (Circuit.eval (C.circuit τ false) input 0) *
          boolSign (parity input)) -
      uniformExpectation (fun input =>
        boolIndicator (Circuit.eval (C.circuit τ true) input 0) *
          boolSign (parity input)) := by
  unfold uniformExpectation Tal.uniformExpectation
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro input _
  calc
    boolIndicator (decide (G.transcript input = τ)) =
        (boolIndicator (Circuit.eval (C.circuit τ false) input 0) -
          boolIndicator (Circuit.eval (C.circuit τ true) input 0)) *
            boolSign (parity input) := fiber_indicator_identity G C τ input
    _ = boolIndicator (Circuit.eval (C.circuit τ false) input 0) *
          boolSign (parity input) -
        boolIndicator (Circuit.eval (C.circuit τ true) input 0) *
          boolSign (parity input) := by ring

namespace ParityTrace

omit [Fintype Transcript] in
/-- Every transcript fiber has probability at most the correlation rate. -/
theorem transcriptProbability_le_of_correlation
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    {ρ : ℝ} (correlation : IndicatorParityCorrelationBound n depthBound sizeBound ρ)
    (τ : Transcript) :
    G.transcriptProbability τ ≤ ρ := by
  let e₀ := uniformExpectation (fun input =>
    boolIndicator (Circuit.eval (C.circuit τ false) input 0) * boolSign (parity input))
  let e₁ := uniformExpectation (fun input =>
    boolIndicator (Circuit.eval (C.circuit τ true) input 0) * boolSign (parity input))
  have h₀ : |e₀| ≤ ρ / 2 :=
    correlation (C.circuit τ false) (C.depth_le τ false) (C.size_le τ false)
  have h₁ : |e₁| ≤ ρ / 2 :=
    correlation (C.circuit τ true) (C.depth_le τ true) (C.size_le τ true)
  have hid : G.transcriptProbability τ = e₀ - e₁ := by
    rw [G.transcriptProbability_eq_expectation, expectation_fiber_identity G C τ]
  calc
    G.transcriptProbability τ = |e₀ - e₁| := by
      rw [← hid, abs_of_nonneg (G.transcriptProbability_nonneg τ)]
    _ ≤ |e₀| + |e₁| := abs_sub _ _
    _ ≤ ρ / 2 + ρ / 2 := add_le_add h₀ h₁
    _ = ρ := by ring

end ParityTrace

/-! ## The information-theoretic fiber argument -/

namespace ParityTrace

/-- Shannon entropy is at least min-entropy. -/
theorem entropy_ge_neg_log_maxProbability
    (G : ParityTrace n Transcript) {ρ : ℝ} (hρ : 0 < ρ)
    (hmax : ∀ τ, G.transcriptProbability τ ≤ ρ) :
    -Real.logb 2 ρ ≤ G.transcriptEntropy := by
  have hterm : ∀ τ,
      G.transcriptProbability τ * (-Real.logb 2 ρ) ≤
        -(G.transcriptProbability τ) * Real.logb 2 (G.transcriptProbability τ) := by
    intro τ
    by_cases hp : G.transcriptProbability τ = 0
    · simp [hp]
    · have hp0 : 0 < G.transcriptProbability τ :=
        lt_of_le_of_ne (G.transcriptProbability_nonneg τ) (Ne.symm hp)
      have hlog : Real.logb 2 (G.transcriptProbability τ) ≤ Real.logb 2 ρ :=
        (Real.logb_le_logb (by norm_num) hp0 hρ).2 (hmax τ)
      nlinarith
  calc
    -Real.logb 2 ρ =
        (∑ τ, G.transcriptProbability τ) * (-Real.logb 2 ρ) := by
          rw [G.sum_transcriptProbability, one_mul]
    _ = ∑ τ, G.transcriptProbability τ * (-Real.logb 2 ρ) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ τ, -(G.transcriptProbability τ) *
        Real.logb 2 (G.transcriptProbability τ) := Finset.sum_le_sum fun τ _ => hterm τ
    _ = G.transcriptEntropy := rfl

end ParityTrace

/--
Abstract footprint theorem: shallow, small transcript-fiber circuits plus an
AC⁰--parity correlation rate `ρ` force at least `-log₂ ρ` bits of mutual
information into the visible transcript.
-/
theorem footprint_from_correlation
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    {ρ : ℝ} (hρ : 0 < ρ)
    (correlation : IndicatorParityCorrelationBound n depthBound sizeBound ρ) :
    -Real.logb 2 ρ ≤ G.uniformMutualInformation := by
  apply G.entropy_ge_neg_log_maxProbability hρ
  exact G.transcriptProbability_le_of_correlation C correlation

/-- Footprint bound stated from the standard sign-correlation theorem. -/
theorem footprint_from_sign_correlation
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    (correlation : SignParityCorrelationBound n depthBound sizeBound ρ) :
    -Real.logb 2 ρ ≤ G.uniformMutualInformation :=
  footprint_from_correlation G C hρ
    (indicatorParityCorrelationBound_of_sign hn correlation)

/--
The footprint conclusion obtained directly from Tal's general Fourier-tail
theorem, with no separately assumed parity-correlation statement.
-/
theorem footprint_from_tal
    (tal : Tal.FourierTailTheorem)
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (hn : 1 ≤ n) (hsizeTwo : 1 < sizeBound) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound depthBound sizeBound n)) ≤
      G.uniformMutualInformation := by
  apply footprint_from_sign_correlation G C hn
  · exact Real.sqrt_pos.2 (Tal.tailBound_pos depthBound sizeBound n)
  · exact signParityCorrelationBound_of_tal tal hsizeTwo

/-- The quantitative form used in the paper: rate `q` gives `q - 3/2` bits. -/
theorem footprint_quantitative
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (q : ℝ)
    (correlation : IndicatorParityCorrelationBound n depthBound sizeBound
      ((2 : ℝ) ^ ((3 / 2 : ℝ) - q))) :
    q - 3 / 2 ≤ G.uniformMutualInformation := by
  have h := footprint_from_correlation G C
    (Real.rpow_pos_of_pos (by norm_num) _) correlation
  rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h
  linarith

/-- Quantitative footprint bound directly from the standard sign form. -/
theorem footprint_quantitative_of_sign
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (hn : 1 ≤ n) (q : ℝ)
    (correlation : SignParityCorrelationBound n depthBound sizeBound
      ((2 : ℝ) ^ ((3 / 2 : ℝ) - q))) :
    q - 3 / 2 ≤ G.uniformMutualInformation := by
  have h := footprint_from_sign_correlation G C hn
    (Real.rpow_pos_of_pos (by norm_num) _) correlation
  rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h
  linarith

/-- The denominator appearing after the circuit translation in the appendix. -/
def footprintRate (n : ℕ) (E S : ℝ) (d : ℕ) : ℝ :=
  n / (E * Real.logb 2 S) ^ d

/--
The displayed parity footprint bound before the final `S = poly(M,N+P)`
substitution.
-/
theorem parity_footprint
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (hn : 1 ≤ n) (E S : ℝ) (d : ℕ)
    (correlation : SignParityCorrelationBound n depthBound sizeBound
      ((2 : ℝ) ^ ((3 / 2 : ℝ) - footprintRate n E S d))) :
    footprintRate n E S d - 3 / 2 ≤ G.uniformMutualInformation :=
  footprint_quantitative_of_sign G C hn _ correlation

/-- Scale obtained after substituting circuit size and depth into the bound. -/
def footprintScale (n : ℕ) (M P F : ℝ) (L c : ℕ) : ℝ :=
  (F * (Real.logb 2 M + Real.logb 2 (P + n))) ^ (c * L)

/-- The appendix's explicit mutual-information lower bound after substitution. -/
theorem footprint_information_lower_bound
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (hn : 1 ≤ n) (M P F : ℝ) (L c : ℕ)
    (correlation : SignParityCorrelationBound n depthBound sizeBound
      ((2 : ℝ) ^ ((3 / 2 : ℝ) -
        n / footprintScale n M P F L c))) :
    n / footprintScale n M P F L c - 3 / 2 ≤
      G.uniformMutualInformation :=
  footprint_quantitative_of_sign G C hn _ correlation

/--
The paper's footprint tradeoff in exact, non-asymptotic form.  `M` is model
size, `P` the maximum CoT length, `L` Transformer depth, and `F,c` the
universal constants obtained by substituting the polynomial circuit-size and
linear circuit-depth bounds.  This is the rearrangement underlying the
paper's `Ω̃` display; its additive `3/2` and the factor `F^(cL)` are absorbed
there into universal/polylogarithmic constants.
-/
theorem footprint_tradeoff_of_sign_correlation
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (hn : 1 ≤ n) (M P F : ℝ) (L c : ℕ)
    (hscale : 0 < footprintScale n M P F L c)
    (correlation : SignParityCorrelationBound n depthBound sizeBound
      ((2 : ℝ) ^ ((3 / 2 : ℝ) -
        n / footprintScale n M P F L c))) :
    n ≤ footprintScale n M P F L c *
      (3 / 2 + G.uniformMutualInformation) := by
  have hlower := footprint_information_lower_bound G C hn M P F L c correlation
  have hdiv : (n : ℝ) / footprintScale n M P F L c ≤
      3 / 2 + G.uniformMutualInformation := by
    linarith
  have hmul := (div_le_iff₀ hscale).1 hdiv
  simpa [mul_comm] using hmul

/--
The footprint theorem with Tal's full theorem as its circuit-complexity input.
The FPT translation fixes `depthBound` and `sizeBound`; Tal then forces the
displayed information-theoretic footprint.
-/
theorem footprint_theorem
    (tal : Tal.FourierTailTheorem)
    (G : ParityTrace n Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (hn : 1 ≤ n) (hsizeTwo : 1 < sizeBound) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound depthBound sizeBound n)) ≤
      G.uniformMutualInformation :=
  footprint_from_tal tal G C hn hsizeTwo

end Footprint
