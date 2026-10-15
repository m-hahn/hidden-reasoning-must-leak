import TaskFootprint

/-!
# Autoregressive fixed-precision Transformers and transcript fibers

This file closes the fixed-prefix gap between the matrix-level Transformer in
`TransformerAC0` and the transcript-fiber argument in `Footprint`.

At a fixed generation time, the candidate prefix is a constant.  Consequently
every input wire of the Transformer's context is either a constant or a literal
of the original input.  `ContextLiteral` records precisely that wiring.  The
construction below substitutes those literals into the already proved
fixed-precision Transformer compiler, checks all candidate next-token
predictions in parallel, and obtains the `FiberCircuitFamily` used by the
footprint theorem.  No circuit-realization field occurs in the model.
-/

noncomputable section

namespace Autoregressive

open TransformerAC0
open Footprint

/-- One wire in a fixed-prefix Transformer context. -/
inductive ContextLiteral (n : ℕ)
  | constant (value : Bool)
  | positive (index : Fin n)
  | negative (index : Fin n)

namespace ContextLiteral

def eval (literal : ContextLiteral n) (input : Bits n) : Bool :=
  match literal with
  | .constant value => value
  | .positive index => input index
  | .negative index => !(input index)

/-- A literal is realized by at most one Boolean gate. -/
def circuit (literal : ContextLiteral n) : Circuit n 1 :=
  match literal with
  | .constant value => Circuit.const n value
  | .positive index => .wire fun _ => index
  | .negative index => .seq (.wire fun _ => index) .notGate

@[simp] theorem eval_circuit (literal : ContextLiteral n) (input : Bits n) :
    Circuit.eval literal.circuit input 0 = literal.eval input := by
  cases literal with
  | constant value => cases value <;> simp [circuit, eval, Circuit.eval, Circuit.const]
  | positive index => simp [circuit, eval, Circuit.eval]
  | negative index => simp [circuit, eval, Circuit.eval]

theorem depth_circuit_le_one (literal : ContextLiteral n) :
    Circuit.depth literal.circuit ≤ 1 := by
  cases literal with
  | constant value => cases value <;> simp [circuit, Circuit.depth, Circuit.const]
  | positive index => simp [circuit, Circuit.depth]
  | negative index => simp [circuit, Circuit.depth]

theorem gateCount_circuit_le_one (literal : ContextLiteral n) :
    Circuit.gateCount literal.circuit ≤ 1 := by
  cases literal with
  | constant value => cases value <;> simp [circuit, Circuit.gateCount, Circuit.const]
  | positive index => simp [circuit, Circuit.gateCount]
  | negative index => simp [circuit, Circuit.gateCount]

end ContextLiteral

/--
A deterministic binary autoregressive use of one matrix-level fixed-precision
Transformer.  `context` is data, not a correctness certificate: it says how a
fixed candidate prefix and the original input are laid out in the Transformer's
one-hot Boolean context.
-/
structure FixedPrecisionGenerator (n traceLength : ℕ) where
  architecture : Architecture
  transformer : FixedPrecisionTransformer architecture
  context : (time : ℕ) → Bits time →
    Fin architecture.inputBits → ContextLiteral n

namespace FixedPrecisionGenerator

variable {n traceLength : ℕ}

def contextInput (model : FixedPrecisionGenerator n traceLength)
    (input : Bits n) (time : ℕ) (prefixBits : Bits time) :
    Bits model.architecture.inputBits :=
  fun index => (model.context time prefixBits index).eval input

/-- Greedy autoregressive execution of the matrix semantics. -/
def generatedToken (model : FixedPrecisionGenerator n traceLength)
    (input : Bits n) (time : ℕ) : Bool :=
  model.transformer.run
    (model.contextInput input time (fun previous =>
      model.generatedToken input previous))
termination_by time

/-- The monitor-visible fixed-length trace. -/
def transcript (model : FixedPrecisionGenerator n traceLength)
    (input : Bits n) : Bits traceLength :=
  fun time => model.generatedToken input time

/-- The answer token immediately following the visible trace. -/
def answer (model : FixedPrecisionGenerator n traceLength)
    (input : Bits n) : Bool :=
  model.generatedToken input traceLength

/-- The candidate prefix of length `time`. -/
def candidatePrefix (candidate : Bits traceLength) (time : ℕ)
    (htime : time ≤ traceLength) : Bits time :=
  fun index => candidate ⟨index, index.isLt.trans_le htime⟩

/-- Literal wiring for a fixed candidate prefix. -/
def contextCircuit (model : FixedPrecisionGenerator n traceLength)
    (time : ℕ) (prefixBits : Bits time) :
    Circuit n model.architecture.inputBits :=
  .bundle fun index => (model.context time prefixBits index).circuit

@[simp] theorem eval_contextCircuit
    (model : FixedPrecisionGenerator n traceLength)
    (time : ℕ) (prefixBits : Bits time) (input : Bits n) :
    Circuit.eval (model.contextCircuit time prefixBits) input =
      model.contextInput input time prefixBits := by
  funext index
  simp [contextCircuit, contextInput, Circuit.eval]

theorem depth_contextCircuit_le_one
    (model : FixedPrecisionGenerator n traceLength)
    (time : ℕ) (prefixBits : Bits time) :
    Circuit.depth (model.contextCircuit time prefixBits) ≤ 1 := by
  simp only [contextCircuit, Circuit.depth]
  apply Finset.sup_le
  intro index _
  exact ContextLiteral.depth_circuit_le_one _

theorem gateCount_contextCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (time : ℕ) (prefixBits : Bits time) :
    Circuit.gateCount (model.contextCircuit time prefixBits) ≤
      model.architecture.inputBits := by
  simp only [contextCircuit, Circuit.gateCount]
  calc
    (∑ index : Fin model.architecture.inputBits,
        Circuit.gateCount (model.context time prefixBits index).circuit) ≤
        ∑ _index : Fin model.architecture.inputBits, 1 := by
          apply Finset.sum_le_sum
          intro index _
          exact ContextLiteral.gateCount_circuit_le_one _
    _ = model.architecture.inputBits := by simp

/-- Run the generated AC⁰ circuit after substituting a fixed prefix. -/
def predictionCircuit (model : FixedPrecisionGenerator n traceLength)
    (time : ℕ) (prefixBits : Bits time) : Circuit n 1 :=
  .seq (model.contextCircuit time prefixBits) model.transformer.compile

@[simp] theorem eval_predictionCircuit
    (model : FixedPrecisionGenerator n traceLength)
    (time : ℕ) (prefixBits : Bits time) (input : Bits n) :
    Circuit.eval (model.predictionCircuit time prefixBits) input 0 =
      model.transformer.run (model.contextInput input time prefixBits) := by
  simp [predictionCircuit, Circuit.eval,
    FixedPrecisionTransformer.compile_correct]

/-- Test whether a one-output circuit has the requested Boolean value. -/
def requireValue (circuit : Circuit n 1) (value : Bool) : Circuit n 1 :=
  if value then circuit else .seq circuit .notGate

@[simp] theorem eval_requireValue (circuit : Circuit n 1)
    (value : Bool) (input : Bits n) :
    Circuit.eval (requireValue circuit value) input 0 =
      decide (Circuit.eval circuit input 0 = value) := by
  cases value <;> cases h : Circuit.eval circuit input 0 <;>
    simp [requireValue, Circuit.eval, h]

/-- All fixed-prefix next-token checks for a candidate visible trace. -/
def transcriptCircuit (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) : Circuit n 1 :=
  .seq
    (.bundle fun time =>
      requireValue
        (model.predictionCircuit time
          (candidatePrefix candidate time (Nat.le_of_lt time.isLt)))
        (candidate time))
    (.andGate traceLength)

/-- The next-token check following the candidate trace. -/
def answerCircuit (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (value : Bool) : Circuit n 1 :=
  requireValue
    (model.predictionCircuit traceLength
      (candidatePrefix candidate traceLength (Nat.le_refl _)))
    value

/-- The exact fiber circuit used in the paper: fixed transcript and answer. -/
def fiberCircuit (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (value : Bool) : Circuit n 1 :=
  .seq (.parallel (model.transcriptCircuit candidate)
    (model.answerCircuit candidate value)) (.andGate 2)

/-- A fixed candidate satisfies all autoregressive next-token equations. -/
def AcceptsTranscript (model : FixedPrecisionGenerator n traceLength)
    (input : Bits n) (candidate : Bits traceLength) : Prop :=
  ∀ time : Fin traceLength,
    model.transformer.run
      (model.contextInput input time
        (candidatePrefix candidate time (Nat.le_of_lt time.isLt))) = candidate time

theorem acceptsTranscript_iff
    (model : FixedPrecisionGenerator n traceLength)
    (input : Bits n) (candidate : Bits traceLength) :
    model.AcceptsTranscript input candidate ↔ model.transcript input = candidate := by
  constructor
  · intro accepts
    have hgenerated : ∀ time (htime : time < traceLength),
        model.generatedToken input time = candidate ⟨time, htime⟩ := by
      intro time htime
      induction time using Nat.strong_induction_on with
      | h time ih =>
          rw [generatedToken]
          have hprefix :
              (fun previous : Fin time => model.generatedToken input previous) =
                candidatePrefix candidate time (Nat.le_of_lt htime) := by
            funext previous
            simpa [candidatePrefix] using
              ih previous previous.isLt (previous.isLt.trans htime)
          rw [hprefix]
          exact accepts ⟨time, htime⟩
    funext time
    exact hgenerated time time.isLt
  · intro equality time
    have hprefix :
        (fun previous : Fin time => model.generatedToken input previous) =
          candidatePrefix candidate time (Nat.le_of_lt time.isLt) := by
      funext previous
      have := congrFun equality
        ⟨previous, previous.isLt.trans time.isLt⟩
      exact this
    have htoken : model.generatedToken input time = candidate time := by
      exact congrFun equality time
    rw [generatedToken] at htoken
    change model.transformer.run
      (model.contextInput input time
        (fun previous : Fin time => model.generatedToken input previous)) =
          candidate time at htoken
    rw [hprefix] at htoken
    exact htoken

@[simp] theorem eval_transcriptCircuit
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (input : Bits n) :
    Circuit.eval (model.transcriptCircuit candidate) input 0 =
      decide (model.transcript input = candidate) := by
  apply Bool.eq_iff_iff.mpr
  simp only [transcriptCircuit, Circuit.eval, eval_requireValue,
    eval_predictionCircuit, decide_eq_true_eq]
  change model.AcceptsTranscript input candidate ↔
    model.transcript input = candidate
  exact model.acceptsTranscript_iff input candidate

@[simp] theorem eval_answerCircuit
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (value : Bool) (input : Bits n) :
    Circuit.eval (model.answerCircuit candidate value) input 0 =
      decide (model.transformer.run
        (model.contextInput input traceLength candidate) = value) := by
  have hprefix : candidatePrefix candidate traceLength (Nat.le_refl _) = candidate := by
    funext index
    rfl
  simp [answerCircuit, hprefix]

theorem answer_eq_of_transcript_eq
    (model : FixedPrecisionGenerator n traceLength)
    (input : Bits n) (candidate : Bits traceLength)
    (htrace : model.transcript input = candidate) :
    model.answer input =
      model.transformer.run (model.contextInput input traceLength candidate) := by
  unfold answer
  rw [generatedToken]
  have hprefix :
      (fun previous : Fin traceLength => model.generatedToken input previous) = candidate := by
    funext previous
    exact congrFun htrace previous
  rw [hprefix]

@[simp] theorem eval_fiberCircuit
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (value : Bool) (input : Bits n) :
    Circuit.eval (model.fiberCircuit candidate value) input 0 =
      decide (model.transcript input = candidate ∧ model.answer input = value) := by
  apply Bool.eq_iff_iff.mpr
  simp only [fiberCircuit, Circuit.eval, eval_transcriptCircuit,
    eval_answerCircuit, decide_eq_true_eq]
  constructor
  · intro hall
    have htrace : model.transcript input = candidate := by
      have h := hall (Fin.castAdd 1 (0 : Fin 1))
      rw [Fin.append_left] at h
      simpa using h
    have hanswer : model.transformer.run
        (model.contextInput input traceLength candidate) = value := by
      have h := hall (Fin.natAdd 1 (0 : Fin 1))
      rw [Fin.append_right] at h
      simpa using h
    refine ⟨htrace, ?_⟩
    rw [model.answer_eq_of_transcript_eq input candidate htrace]
    exact hanswer
  · rintro ⟨htrace, hanswer⟩
    have hanswer' : model.transformer.run
        (model.contextInput input traceLength candidate) = value := by
      rw [← model.answer_eq_of_transcript_eq input candidate htrace]
      exact hanswer
    intro index
    fin_cases index
    · change Circuit.eval (model.transcriptCircuit candidate) input 0 = true
      simpa using htrace
    · change Circuit.eval (model.answerCircuit candidate value) input 0 = true
      simpa using hanswer'

theorem depth_predictionCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (time : ℕ) (prefixBits : Bits time) :
    Circuit.depth (model.predictionCircuit time prefixBits) ≤
      Circuit.depth model.transformer.compile + 1 := by
  simp only [predictionCircuit, Circuit.depth]
  have h := model.depth_contextCircuit_le_one time prefixBits
  omega

theorem gateCount_predictionCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (time : ℕ) (prefixBits : Bits time) :
    Circuit.gateCount (model.predictionCircuit time prefixBits) ≤
      model.architecture.inputBits + Circuit.gateCount model.transformer.compile := by
  simp only [predictionCircuit, Circuit.gateCount]
  exact Nat.add_le_add_right (model.gateCount_contextCircuit_le time prefixBits) _

theorem depth_requireValue_le (circuit : Circuit n 1) (value : Bool) :
    Circuit.depth (requireValue circuit value) ≤ Circuit.depth circuit + 1 := by
  cases value <;> simp [requireValue, Circuit.depth]

theorem gateCount_requireValue_le (circuit : Circuit n 1) (value : Bool) :
    Circuit.gateCount (requireValue circuit value) ≤
      Circuit.gateCount circuit + 1 := by
  cases value <;> simp [requireValue, Circuit.gateCount]

theorem depth_transcriptCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) :
    Circuit.depth (model.transcriptCircuit candidate) ≤
      Circuit.depth model.transformer.compile + 3 := by
  simp only [transcriptCircuit, Circuit.depth]
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro time _
  exact (depth_requireValue_le _ _).trans (by
    have h := model.depth_predictionCircuit_le time
      (candidatePrefix candidate time (Nat.le_of_lt time.isLt))
    omega)

theorem gateCount_transcriptCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) :
    Circuit.gateCount (model.transcriptCircuit candidate) ≤
      traceLength *
        (model.architecture.inputBits +
          Circuit.gateCount model.transformer.compile + 1) + 1 := by
  simp only [transcriptCircuit, Circuit.gateCount]
  apply Nat.add_le_add_right
  calc
    (∑ time : Fin traceLength,
        Circuit.gateCount
          (requireValue
            (model.predictionCircuit time
              (candidatePrefix candidate time (Nat.le_of_lt time.isLt)))
            (candidate time))) ≤
        ∑ _time : Fin traceLength,
          (model.architecture.inputBits +
            Circuit.gateCount model.transformer.compile + 1) := by
              apply Finset.sum_le_sum
              intro time _
              exact (gateCount_requireValue_le _ _).trans
                (Nat.add_le_add_right
                  (model.gateCount_predictionCircuit_le time
                    (candidatePrefix candidate time (Nat.le_of_lt time.isLt))) 1)
    _ = traceLength *
        (model.architecture.inputBits +
          Circuit.gateCount model.transformer.compile + 1) := by simp

theorem depth_answerCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (value : Bool) :
    Circuit.depth (model.answerCircuit candidate value) ≤
      Circuit.depth model.transformer.compile + 2 := by
  exact (depth_requireValue_le _ _).trans (by
    have h := model.depth_predictionCircuit_le traceLength
      (candidatePrefix candidate traceLength (Nat.le_refl _))
    omega)

theorem gateCount_answerCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (value : Bool) :
    Circuit.gateCount (model.answerCircuit candidate value) ≤
      model.architecture.inputBits +
        Circuit.gateCount model.transformer.compile + 1 := by
  exact (gateCount_requireValue_le _ _).trans
    (Nat.add_le_add_right
      (model.gateCount_predictionCircuit_le traceLength
        (candidatePrefix candidate traceLength (Nat.le_refl _))) 1)

/-- Uniform depth bound for the constructed fixed-prefix fibers. -/
def explicitFiberDepth (model : FixedPrecisionGenerator n traceLength) : ℕ :=
  Circuit.depth model.transformer.compile + 4

/-- Uniform gate bound for the constructed fixed-prefix fibers. -/
def explicitFiberSize (model : FixedPrecisionGenerator n traceLength) : ℕ :=
  (traceLength + 1) *
      (model.architecture.inputBits +
        Circuit.gateCount model.transformer.compile + 1) + 2

theorem depth_fiberCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (value : Bool) :
    Circuit.depth (model.fiberCircuit candidate value) ≤
      model.explicitFiberDepth := by
  simp only [fiberCircuit, explicitFiberDepth, Circuit.depth]
  have htrace := model.depth_transcriptCircuit_le candidate
  have hanswer := model.depth_answerCircuit_le candidate value
  omega

theorem gateCount_fiberCircuit_le
    (model : FixedPrecisionGenerator n traceLength)
    (candidate : Bits traceLength) (value : Bool) :
    Circuit.gateCount (model.fiberCircuit candidate value) ≤
      model.explicitFiberSize := by
  simp only [fiberCircuit, explicitFiberSize, Circuit.gateCount]
  have htrace := model.gateCount_transcriptCircuit_le candidate
  have hanswer := model.gateCount_answerCircuit_le candidate value
  calc
    Circuit.gateCount (model.transcriptCircuit candidate) +
          Circuit.gateCount (model.answerCircuit candidate value) + 1 ≤
        (traceLength *
            (model.architecture.inputBits +
              Circuit.gateCount model.transformer.compile + 1) + 1) +
          (model.architecture.inputBits +
            Circuit.gateCount model.transformer.compile + 1) + 1 := by omega
    _ = (traceLength + 1) *
          (model.architecture.inputBits +
            Circuit.gateCount model.transformer.compile + 1) + 2 := by ring

/-- Exact maximum depth of the finitely many generated fiber circuits. -/
def fiberDepth (model : FixedPrecisionGenerator n traceLength) : ℕ :=
  Finset.univ.sup fun pair : Bits traceLength × Bool =>
    Circuit.depth (model.fiberCircuit pair.1 pair.2)

/-- Exact maximum size of the finitely many generated fiber circuits. -/
def fiberSize (model : FixedPrecisionGenerator n traceLength) : ℕ :=
  Finset.univ.sup fun pair : Bits traceLength × Bool =>
    Circuit.gateCount (model.fiberCircuit pair.1 pair.2)

/-- The actual execution packaged for the information-theoretic theorem. -/
def parityTrace (model : FixedPrecisionGenerator n traceLength)
    (correct : ∀ input, model.answer input = Tal.parity input) :
    ParityTrace n (Bits traceLength) where
  transcript := model.transcript
  answer := model.answer
  answer_correct := correct

/-- Fiber circuits are constructed from the Transformer and fixed-prefix
wiring, rather than supplied as a theorem hypothesis. -/
def fiberCircuitFamily (model : FixedPrecisionGenerator n traceLength)
    (correct : ∀ input, model.answer input = Tal.parity input) :
    FiberCircuitFamily (model.parityTrace correct) model.fiberDepth model.fiberSize where
  circuit := model.fiberCircuit
  correct := model.eval_fiberCircuit
  depth_le := by
    intro candidate value
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Bits traceLength × Bool)))
      (f := fun pair => Circuit.depth (model.fiberCircuit pair.1 pair.2))
      (by simp : (candidate, value) ∈ (Finset.univ : Finset (Bits traceLength × Bool)))
  size_le := by
    intro candidate value
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Bits traceLength × Bool)))
      (f := fun pair => Circuit.gateCount (model.fiberCircuit pair.1 pair.2))
      (by simp : (candidate, value) ∈ (Finset.univ : Finset (Bits traceLength × Bool)))

/-- The same family with the explicit paper-facing depth and gate bounds. -/
def explicitFiberCircuitFamily (model : FixedPrecisionGenerator n traceLength)
    (correct : ∀ input, model.answer input = Tal.parity input) :
    FiberCircuitFamily (model.parityTrace correct)
      model.explicitFiberDepth model.explicitFiberSize where
  circuit := model.fiberCircuit
  correct := model.eval_fiberCircuit
  depth_le := model.depth_fiberCircuit_le
  size_le := model.gateCount_fiberCircuit_le

/-- The execution packaged for an arbitrary Boolean task. -/
def taskTrace (model : FixedPrecisionGenerator n traceLength)
    (target : Bits n → Bool)
    (correct : ∀ input, model.answer input = target input) :
    TaskFootprint.BooleanTrace n target (Bits traceLength) where
  transcript := model.transcript
  answer := model.answer
  answer_correct := correct

/-- The same generated fixed-prefix circuits serve every Boolean target; only
the proved answer-correctness equation changes. -/
def taskFiberCircuitFamily (model : FixedPrecisionGenerator n traceLength)
    (target : Bits n → Bool)
    (correct : ∀ input, model.answer input = target input) :
    TaskFootprint.FiberCircuitFamily (model.taskTrace target correct)
      model.explicitFiberDepth model.explicitFiberSize where
  circuit := model.fiberCircuit
  correct := model.eval_fiberCircuit
  depth_le := model.depth_fiberCircuit_le
  size_le := model.gateCount_fiberCircuit_le

/-- End-to-end footprint theorem for any Boolean task once its circuit
correlation theorem has been proved. -/
theorem task_footprint
    (model : FixedPrecisionGenerator n traceLength)
    (target : Bits n → Bool)
    (correct : ∀ input, model.answer input = target input)
    {rate : ℝ}
    (correlation : TaskFootprint.SignCorrelationBound target
      model.explicitFiberDepth model.explicitFiberSize rate)
    (hpositive : 0 < rate + |TaskFootprint.targetBias target|) :
    -Real.logb 2 (rate + |TaskFootprint.targetBias target|) ≤
      (model.taskTrace target correct).uniformMutualInformation :=
  TaskFootprint.footprint (model.taskTrace target correct)
    (model.taskFiberCircuitFamily target correct) correlation hpositive

/-- End-to-end footprint theorem for an actual autoregressive execution of the
matrix-level fixed-precision Transformer.  Tal is the sole external
circuit-complexity input. -/
theorem footprint
    (tal : Tal.FourierTailTheorem)
    (model : FixedPrecisionGenerator n traceLength)
    (correct : ∀ input, model.answer input = Tal.parity input)
    (hn : 1 ≤ n) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (Real.sqrt (Tal.tailBound model.explicitFiberDepth
          model.explicitFiberSize n)) ≤
      (model.parityTrace correct).uniformMutualInformation :=
  Footprint.footprint_theorem tal (model.parityTrace correct)
    (model.explicitFiberCircuitFamily correct) hn hsize

end FixedPrecisionGenerator

end Autoregressive

