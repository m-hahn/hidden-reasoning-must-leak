import Footprint

/-!
# Footprints for arbitrary Boolean tasks

The parity-specific development is enough for parity and reductions to it.
Multiplication needs the slightly more general statement below: a target may
have a small, nonzero bias, and its correlation with every shallow circuit may
be bounded by a task-specific Fourier argument.
-/

noncomputable section

namespace TaskFootprint

open TransformerAC0

abbrev Bits := TransformerAC0.Bits
abbrev boolSign := Tal.boolSign
abbrev boolIndicator := Footprint.boolIndicator
def uniformExpectation {n : ℕ} (function : Bits n → ℝ) : ℝ :=
  Tal.uniformExpectation function

structure BooleanTrace (n : ℕ) (target : Bits n → Bool)
    (Transcript : Type*) where
  transcript : Bits n → Transcript
  answer : Bits n → Bool
  answer_correct : ∀ input, answer input = target input

namespace BooleanTrace

variable {n : ℕ} {target : Bits n → Bool}
variable {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]

/-- Reuse the already proved finite Shannon-entropy API; only its transcript
map matters for entropy and probability. -/
def asParityTrace (G : BooleanTrace n target Transcript) :
    Footprint.ParityTrace n Transcript where
  transcript := G.transcript
  answer := Tal.parity
  answer_correct := fun _ => rfl

abbrev transcriptProbability (G : BooleanTrace n target Transcript) (t : Transcript) : ℝ :=
  G.asParityTrace.transcriptProbability t

abbrev transcriptEntropy (G : BooleanTrace n target Transcript) : ℝ :=
  G.asParityTrace.transcriptEntropy

abbrev uniformMutualInformation (G : BooleanTrace n target Transcript) : ℝ :=
  G.asParityTrace.uniformMutualInformation

end BooleanTrace

variable {n depthBound sizeBound : ℕ}
variable {target : Bits n → Bool}
variable {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]

structure FiberCircuitFamily (G : BooleanTrace n target Transcript)
    (depthBound sizeBound : ℕ) where
  circuit : Transcript → Bool → Circuit n 1
  correct : ∀ transcript answer input,
    Circuit.eval (circuit transcript answer) input 0 =
      decide (G.transcript input = transcript ∧ G.answer input = answer)
  depth_le : ∀ transcript answer,
    Circuit.depth (circuit transcript answer) ≤ depthBound
  size_le : ∀ transcript answer,
    Circuit.gateCount (circuit transcript answer) ≤ sizeBound

def SignCorrelationBound (target : Bits n → Bool)
    (depthBound sizeBound : ℕ) (rate : ℝ) : Prop :=
  ∀ circuit : Circuit n 1,
    Circuit.depth circuit ≤ depthBound →
    Circuit.gateCount circuit ≤ sizeBound →
    |uniformExpectation (fun input =>
      boolSign (Circuit.eval circuit input 0) * boolSign (target input))| ≤ rate

def targetBias (target : Bits n → Bool) : ℝ :=
  uniformExpectation fun input => boolSign (target input)

private theorem indicator_eq_one_sub_sign_div_two (b : Bool) :
    boolIndicator b = (1 - boolSign b) / 2 := by
  cases b <;> norm_num [Footprint.boolIndicator, Tal.boolSign]

/-- The indicator correlation bound, including the target's possible bias. -/
theorem indicator_correlation_le
    {rate : ℝ} (correlation : SignCorrelationBound target depthBound sizeBound rate)
    (circuit : Circuit n 1) (hdepth : Circuit.depth circuit ≤ depthBound)
    (hsize : Circuit.gateCount circuit ≤ sizeBound) :
    |uniformExpectation (fun input =>
      boolIndicator (Circuit.eval circuit input 0) * boolSign (target input))| ≤
      (rate + |targetBias target|) / 2 := by
  let signed := uniformExpectation (fun input : Bits n =>
    boolSign (Circuit.eval circuit input 0) * boolSign (target input))
  have hsigned : |signed| ≤ rate := correlation circuit hdepth hsize
  have hid : uniformExpectation (fun input : Bits n =>
      boolIndicator (Circuit.eval circuit input 0) * boolSign (target input)) =
      (1 / 2 : ℝ) * targetBias target - (1 / 2 : ℝ) * signed := by
    dsimp only [signed, targetBias]
    unfold uniformExpectation Tal.uniformExpectation
    have hsum :
        (∑ input : Bits n,
          boolIndicator (Circuit.eval circuit input 0) * boolSign (target input)) =
          (1 / 2 : ℝ) * (∑ input : Bits n, boolSign (target input)) -
            (1 / 2 : ℝ) * (∑ input : Bits n,
              boolSign (Circuit.eval circuit input 0) * boolSign (target input)) := by
      calc
        (∑ input : Bits n,
            boolIndicator (Circuit.eval circuit input 0) * boolSign (target input)) =
            ∑ input : Bits n,
              ((1 / 2 : ℝ) * boolSign (target input) -
                (1 / 2 : ℝ) *
                  (boolSign (Circuit.eval circuit input 0) *
                    boolSign (target input))) := by
              apply Finset.sum_congr rfl
              intro input _
              rw [indicator_eq_one_sub_sign_div_two]
              ring
        _ = (1 / 2 : ℝ) * (∑ input : Bits n, boolSign (target input)) -
              (1 / 2 : ℝ) * (∑ input : Bits n,
                boolSign (Circuit.eval circuit input 0) * boolSign (target input)) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [hsum]
    ring
  rw [hid]
  calc
    |(1 / 2 : ℝ) * targetBias target - (1 / 2 : ℝ) * signed| ≤
        |(1 / 2 : ℝ) * targetBias target| + |(1 / 2 : ℝ) * signed| :=
      abs_sub _ _
    _ = (|targetBias target| + |signed|) / 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    _ ≤ (rate + |targetBias target|) / 2 := by linarith

omit [Fintype Transcript] in
private theorem fiber_indicator_identity
    (G : BooleanTrace n target Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    (t : Transcript) (input : Bits n) :
    boolIndicator (decide (G.transcript input = t)) =
      (boolIndicator (Circuit.eval (C.circuit t false) input 0) -
        boolIndicator (Circuit.eval (C.circuit t true) input 0)) *
          boolSign (target input) := by
  rw [C.correct, C.correct, G.answer_correct]
  by_cases ht : G.transcript input = t <;>
    cases hp : target input <;>
    simp [Footprint.boolIndicator, Tal.boolSign, ht, hp]

omit [Fintype Transcript] in
private theorem expectation_fiber_identity
    (G : BooleanTrace n target Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound) (t : Transcript) :
    uniformExpectation (fun input =>
      boolIndicator (decide (G.transcript input = t))) =
      uniformExpectation (fun input =>
        boolIndicator (Circuit.eval (C.circuit t false) input 0) *
          boolSign (target input)) -
      uniformExpectation (fun input =>
        boolIndicator (Circuit.eval (C.circuit t true) input 0) *
          boolSign (target input)) := by
  unfold uniformExpectation Tal.uniformExpectation
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro input _
  calc
    (fun input => boolIndicator (decide (G.transcript input = t))) input =
        (boolIndicator (Circuit.eval (C.circuit t false) input 0) -
          boolIndicator (Circuit.eval (C.circuit t true) input 0)) *
            boolSign (target input) := fiber_indicator_identity G C t input
    _ = boolIndicator (Circuit.eval (C.circuit t false) input 0) *
          boolSign (target input) -
        boolIndicator (Circuit.eval (C.circuit t true) input 0) *
          boolSign (target input) := by ring

omit [Fintype Transcript] in
private theorem probability_eq_expectation
    (G : BooleanTrace n target Transcript) (t : Transcript) :
    G.transcriptProbability t =
      uniformExpectation (fun input =>
        boolIndicator (decide (G.transcript input = t))) := by
  exact G.asParityTrace.transcriptProbability_eq_expectation t

/-- Every transcript fiber is bounded by circuit correlation plus target bias. -/
theorem transcriptProbability_le
    (G : BooleanTrace n target Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    {rate : ℝ} (correlation : SignCorrelationBound target depthBound sizeBound rate)
    (t : Transcript) :
    G.transcriptProbability t ≤ rate + |targetBias target| := by
  let e₀ := uniformExpectation (fun input =>
    boolIndicator (Circuit.eval (C.circuit t false) input 0) * boolSign (target input))
  let e₁ := uniformExpectation (fun input =>
    boolIndicator (Circuit.eval (C.circuit t true) input 0) * boolSign (target input))
  have h₀ : |e₀| ≤ (rate + |targetBias target|) / 2 :=
    indicator_correlation_le correlation (C.circuit t false)
      (C.depth_le t false) (C.size_le t false)
  have h₁ : |e₁| ≤ (rate + |targetBias target|) / 2 :=
    indicator_correlation_le correlation (C.circuit t true)
      (C.depth_le t true) (C.size_le t true)
  have hid : G.transcriptProbability t = e₀ - e₁ := by
    rw [probability_eq_expectation, expectation_fiber_identity G C t]
  have hnonneg := G.asParityTrace.transcriptProbability_nonneg t
  calc
    G.transcriptProbability t = |e₀ - e₁| := by rw [← hid, abs_of_nonneg hnonneg]
    _ ≤ |e₀| + |e₁| := abs_sub _ _
    _ ≤ (rate + |targetBias target|) / 2 +
        (rate + |targetBias target|) / 2 := add_le_add h₀ h₁
    _ = rate + |targetBias target| := by ring

/-- Generic information-theoretic footprint theorem for a Boolean target. -/
theorem footprint
    (G : BooleanTrace n target Transcript)
    (C : FiberCircuitFamily G depthBound sizeBound)
    {rate : ℝ} (correlation : SignCorrelationBound target depthBound sizeBound rate)
    (hpositive : 0 < rate + |targetBias target|) :
    -Real.logb 2 (rate + |targetBias target|) ≤
      G.uniformMutualInformation := by
  apply G.asParityTrace.entropy_ge_neg_log_maxProbability hpositive
  exact transcriptProbability_le G C correlation

end TaskFootprint

