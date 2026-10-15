import MatrixReadout
import CausalMatrix
import EntropyCoding

/-!
# Full-vocabulary separator-terminated matrix autoregression

Each step emits the actual greedy vocabulary token proved in `MatrixReadout`.
Payload tokens are distinct from the separator. The monitor sees the whole
payload word, and the private Boolean answer labels the actual next token
after the separator. All candidate-fiber circuits and their polynomial
architecture budgets are constructed from the matrices and literal context
wiring.
-/

noncomputable section
open scoped BigOperators

namespace TokenAutoregressive

open TransformerAC0 Autoregressive FiniteInformation

structure Core (n : ℕ) where
  architecture : Architecture
  transformer : FixedPrecisionTransformer architecture
  vocabulary_positive : 0 < architecture.vocabulary
  context_positive : 0 < architecture.contextLength
  separator : Fin architecture.vocabulary
  context : (time : ℕ) → (Fin time → Fin architecture.vocabulary) →
    Fin architecture.inputBits → ContextLiteral n
  /-- Restrict only context length and absolute position table at each step. -/
  prefixLength : ℕ → {length : ℕ // 0 < length ∧ length ≤ architecture.contextLength} :=
    fun _ => ⟨architecture.contextLength, context_positive, le_rfl⟩

namespace Core

def stepArchitecture (core : Core n) (time : ℕ) : Architecture :=
  CausalMatrix.architecture core.architecture (core.prefixLength time).val

def stepTransformer (core : Core n) (time : ℕ) : FixedPrecisionTransformer (core.stepArchitecture time) :=
  CausalMatrix.restrictContext core.transformer (core.prefixLength time).val (core.prefixLength time).property.2

def inputWire (core : Core n) (time : ℕ) : Fin (core.stepArchitecture time).inputBits → Fin core.architecture.inputBits :=
  Fin.castLE (Nat.mul_le_mul_right core.architecture.vocabulary (core.prefixLength time).property.2)

def contextInput (core : Core n) (input : Bits n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) : Bits (core.stepArchitecture time).inputBits :=
  fun wire => (core.context time prefixTokens (core.inputWire time wire)).eval input

def generatedToken (core : Core n) (input : Bits n) (time : ℕ) : Fin core.architecture.vocabulary :=
  (core.stepTransformer time).runToken core.vocabulary_positive (core.prefixLength time).property.1
    (core.contextInput input time (fun previous => core.generatedToken input previous))
termination_by time

def contextCircuit (core : Core n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) : Circuit n (core.stepArchitecture time).inputBits :=
  .bundle fun wire => (core.context time prefixTokens (core.inputWire time wire)).circuit

@[simp] theorem eval_contextCircuit (core : Core n) (input : Bits n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) :
    Circuit.eval (core.contextCircuit time prefixTokens) input = core.contextInput input time prefixTokens := by
  funext wire
  simp [contextCircuit, contextInput, Circuit.eval]

theorem contextCircuit_depth_le (core : Core n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) :
    Circuit.depth (core.contextCircuit time prefixTokens) ≤ 1 := by
  simp only [contextCircuit, Circuit.depth]
  exact Finset.sup_le fun wire _ => ContextLiteral.depth_circuit_le_one _

theorem contextCircuit_size_le (core : Core n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) :
    Circuit.gateCount (core.contextCircuit time prefixTokens) ≤ core.architecture.inputBits := by
  simp only [contextCircuit, Circuit.gateCount]
  calc
    (∑ wire : Fin (core.stepArchitecture time).inputBits,
        Circuit.gateCount (core.context time prefixTokens (core.inputWire time wire)).circuit) ≤
        ∑ _wire : Fin (core.stepArchitecture time).inputBits, 1 :=
      Finset.sum_le_sum fun wire _ => ContextLiteral.gateCount_circuit_le_one _
    _ = (core.stepArchitecture time).inputBits := by simp
    _ ≤ core.architecture.inputBits :=
      Nat.mul_le_mul_right core.architecture.vocabulary (core.prefixLength time).property.2

def tokenPredictionCircuit (core : Core n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) (token : Fin core.architecture.vocabulary) :
    Circuit n 1 := .seq (core.contextCircuit time prefixTokens) ((core.stepTransformer time).tokenClassifier token)

@[simp] theorem eval_tokenPredictionCircuit (core : Core n) (input : Bits n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) (token : Fin core.architecture.vocabulary) :
    Circuit.eval (core.tokenPredictionCircuit time prefixTokens token) input 0 =
      decide ((core.stepTransformer time).runToken core.vocabulary_positive (core.prefixLength time).property.1
        (core.contextInput input time prefixTokens) = token) := by
  simp only [tokenPredictionCircuit, Circuit.eval, eval_contextCircuit]
  exact (core.stepTransformer time).eval_tokenClassifier token core.vocabulary_positive (core.prefixLength time).property.1 _

def answerPredictionCircuit (core : Core n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) (value : Bool) : Circuit n 1 :=
  FixedPrecisionGenerator.requireValue
    (.seq (core.contextCircuit time prefixTokens) (core.stepTransformer time).compile) value

@[simp] theorem eval_answerPredictionCircuit (core : Core n) (input : Bits n) (time : ℕ)
    (prefixTokens : Fin time → Fin core.architecture.vocabulary) (value : Bool) :
    Circuit.eval (core.answerPredictionCircuit time prefixTokens value) input 0 =
      decide (core.transformer.outputLabel
        ((core.stepTransformer time).runToken core.vocabulary_positive (core.prefixLength time).property.1
          (core.contextInput input time prefixTokens)) = value) := by
  simp only [answerPredictionCircuit, FixedPrecisionGenerator.eval_requireValue, Circuit.eval,
    eval_contextCircuit, FixedPrecisionTransformer.compile_correct]
  rw [(core.stepTransformer time).run_eq_label_runToken core.vocabulary_positive (core.prefixLength time).property.1]
  rfl

theorem step_size_le (core : Core n) (time : ℕ) :
    TransformerGateCost.total (core.stepTransformer time).arithmetic
        (FixedPrecisionTransformer.sizeBound (core.stepArchitecture time)) ≤
      TransformerGateCost.total core.transformer.arithmetic (FixedPrecisionTransformer.sizeBound core.architecture) :=
  CausalMatrix.gateCost_monotone core.transformer.arithmetic
    (CausalMatrix.sizeBound_prefix core.architecture _ (core.prefixLength time).property.2)

end Core

structure Generator (n bound : ℕ) where
  core : Core n
  terminates : ∀ input : Bits n, ∃ time : ℕ,
    time ≤ bound ∧ core.generatedToken input time = core.separator

namespace Generator

abbrev Nonterminal (model : Generator n bound) :=
  {token : Fin model.core.architecture.vocabulary // token ≠ model.core.separator}

abbrev Transcript (model : Generator n bound) :=
  (length : Fin (bound + 1)) × (Fin length.val → model.Nonterminal)

def length (model : Generator n bound) (input : Bits n) : Fin (bound + 1) :=
  ⟨Nat.find (model.terminates input), by have h := (Nat.find_spec (model.terminates input)).1; omega⟩

theorem separator_at_length (model : Generator n bound) (input : Bits n) :
    model.core.generatedToken input (model.length input) = model.core.separator :=
  (Nat.find_spec (model.terminates input)).2

theorem nonterminal_before_length (model : Generator n bound) (input : Bits n)
    (time : Fin (model.length input).val) : model.core.generatedToken input time ≠ model.core.separator := by
  intro heq
  have hnot := Nat.find_min (model.terminates input) time.isLt
  apply hnot
  exact ⟨by have h := (Nat.find_spec (model.terminates input)).1; have hi := time.isLt; omega, heq⟩

def transcript (model : Generator n bound) (input : Bits n) : model.Transcript :=
  ⟨model.length input, fun time => ⟨model.core.generatedToken input time, model.nonterminal_before_length input time⟩⟩

def answer (model : Generator n bound) (input : Bits n) : Bool :=
  model.core.transformer.outputLabel (model.core.generatedToken input ((model.length input).val + 1))

def candidatePrefix (model : Generator n bound) (candidate : model.Transcript)
    (time : ℕ) (htime : time ≤ candidate.1.val) : Fin time → Fin model.core.architecture.vocabulary :=
  fun previous => (candidate.2 ⟨previous.val, previous.isLt.trans_le htime⟩).val

def payloadTokens (model : Generator n bound) (candidate : model.Transcript) :
    Fin candidate.1.val → Fin model.core.architecture.vocabulary := fun time => (candidate.2 time).val

def AcceptsCandidate (model : Generator n bound) (input : Bits n) (candidate : model.Transcript) : Prop :=
  (∀ time : Fin candidate.1.val, model.core.generatedToken input time = (candidate.2 time).val) ∧
    model.core.generatedToken input candidate.1.val = model.core.separator

theorem acceptsCandidate_iff (model : Generator n bound) (input : Bits n) (candidate : model.Transcript) :
    model.AcceptsCandidate input candidate ↔ model.transcript input = candidate := by
  constructor
  · rintro ⟨hbits, hstop⟩
    have hle : (model.length input).val ≤ candidate.1.val :=
      Nat.find_min' (model.terminates input) ⟨by have h := candidate.1.isLt; omega, hstop⟩
    have hlength : model.length input = candidate.1 := by
      apply Fin.ext
      apply le_antisymm hle
      by_contra hnot
      have hlt : (model.length input).val < candidate.1.val := by omega
      have h := hbits ⟨(model.length input).val, hlt⟩
      have hs := model.separator_at_length input
      have hne := (candidate.2 ⟨(model.length input).val, hlt⟩).property
      simp only at h
      rw [hs] at h
      exact hne h.symm
    unfold transcript
    rcases candidate with ⟨count, tokens⟩
    dsimp only at hlength hbits ⊢
    subst count
    congr 1
    funext time
    exact Subtype.ext (hbits time)
  · intro htrace
    subst candidate
    exact ⟨fun _ => rfl, model.separator_at_length input⟩

theorem prefix_eq_of_tokens (model : Generator n bound) (input : Bits n) (candidate : model.Transcript)
    (htokens : ∀ time : Fin candidate.1.val, model.core.generatedToken input time = (candidate.2 time).val)
    (time : ℕ) (htime : time ≤ candidate.1.val) :
    (fun previous : Fin time => model.core.generatedToken input previous) = model.candidatePrefix candidate time htime := by
  funext previous
  exact htokens ⟨previous.val, previous.isLt.trans_le htime⟩

def payloadCircuit (model : Generator n bound) (candidate : model.Transcript) : Circuit n 1 :=
  .seq (.bundle fun time : Fin candidate.1.val => model.core.tokenPredictionCircuit time
    (model.candidatePrefix candidate time (Nat.le_of_lt time.isLt)) (candidate.2 time).val)
    (.andGate candidate.1.val)

theorem eval_payloadCircuit_iff (model : Generator n bound) (input : Bits n) (candidate : model.Transcript) :
    Circuit.eval (model.payloadCircuit candidate) input 0 = true ↔
      ∀ time : Fin candidate.1.val, model.core.generatedToken input time = (candidate.2 time).val := by
  simp only [payloadCircuit, Circuit.eval, Core.eval_tokenPredictionCircuit, decide_eq_true_eq]
  constructor
  · intro hcheck
    have hgenerated : ∀ time (htime : time < candidate.1.val),
        model.core.generatedToken input time = (candidate.2 ⟨time, htime⟩).val := by
      intro time htime
      induction time using Nat.strong_induction_on with
      | h time ih =>
          rw [Core.generatedToken]
          have hprefix : (fun previous : Fin time => model.core.generatedToken input previous) =
              model.candidatePrefix candidate time (Nat.le_of_lt htime) := by
            funext previous
            exact ih previous previous.isLt (previous.isLt.trans htime)
          rw [hprefix]
          exact hcheck ⟨time, htime⟩
    intro time
    exact hgenerated time time.isLt
  · intro htokens time
    have h := htokens time
    rw [Core.generatedToken, model.prefix_eq_of_tokens input candidate htokens time (Nat.le_of_lt time.isLt)] at h
    exact h

def fiberChecks (model : Generator n bound) (candidate : model.Transcript) (answerBit : Bool) : Fin 3 → Circuit n 1 :=
  ![model.payloadCircuit candidate,
    model.core.tokenPredictionCircuit candidate.1.val (model.payloadTokens candidate) model.core.separator,
    model.core.answerPredictionCircuit (candidate.1.val + 1)
      (Fin.snoc (model.payloadTokens candidate) model.core.separator) answerBit]

def fiberCircuit (model : Generator n bound) (candidate : model.Transcript) (answerBit : Bool) : Circuit n 1 :=
  .seq (.bundle (model.fiberChecks candidate answerBit)) (.andGate 3)

@[simp] theorem eval_fiberCircuit (model : Generator n bound) (input : Bits n)
    (candidate : model.Transcript) (answerBit : Bool) :
    Circuit.eval (model.fiberCircuit candidate answerBit) input 0 =
      decide (model.transcript input = candidate ∧ model.answer input = answerBit) := by
  apply Bool.eq_iff_iff.mpr
  simp [fiberCircuit, fiberChecks, Circuit.eval, Fin.forall_fin_succ,
    eval_payloadCircuit_iff, Core.eval_tokenPredictionCircuit,
    Core.eval_answerPredictionCircuit]
  have hhead : model.candidatePrefix candidate candidate.1.val (Nat.le_refl _) = model.payloadTokens candidate := by
    funext time
    rfl
  constructor
  · rintro ⟨htokens, hsep, hanswer⟩
    have hprefix := model.prefix_eq_of_tokens input candidate htokens candidate.1.val (Nat.le_refl _)
    rw [hhead] at hprefix
    have hstop : model.core.generatedToken input candidate.1.val = model.core.separator := by
      rw [Core.generatedToken, hprefix]
      exact hsep
    have htrace := (model.acceptsCandidate_iff input candidate).mp ⟨htokens, hstop⟩
    have hprefixNext :
        (fun previous : Fin (candidate.1.val + 1) => model.core.generatedToken input previous) =
          Fin.snoc (model.payloadTokens candidate) model.core.separator := by
      funext previous
      refine Fin.lastCases ?_ (fun before => ?_) previous
      · simpa using hstop
      · simpa [payloadTokens] using htokens before
    refine ⟨htrace, ?_⟩
    have hlength : model.length input = candidate.1 := congrArg Sigma.fst htrace
    unfold answer
    rw [hlength, Core.generatedToken, hprefixNext]
    exact hanswer
  · rintro ⟨htrace, hanswer⟩
    have haccept := (model.acceptsCandidate_iff input candidate).mpr htrace
    rcases haccept with ⟨htokens, hstop⟩
    have hprefix := model.prefix_eq_of_tokens input candidate htokens candidate.1.val (Nat.le_refl _)
    rw [hhead] at hprefix
    refine ⟨htokens, ?_, ?_⟩
    · rw [Core.generatedToken, hprefix] at hstop
      exact hstop
    · have hprefixNext :
          (fun previous : Fin (candidate.1.val + 1) => model.core.generatedToken input previous) =
            Fin.snoc (model.payloadTokens candidate) model.core.separator := by
        funext previous
        refine Fin.lastCases ?_ (fun before => ?_) previous
        · simpa using hstop
        · simpa [payloadTokens] using htokens before
      have hlength : model.length input = candidate.1 := congrArg Sigma.fst htrace
      unfold answer at hanswer
      rw [hlength, Core.generatedToken, hprefixNext] at hanswer
      exact hanswer

def predictionDepth (model : Generator n bound) : ℕ :=
  (model.core.architecture.layers + 2) * TransformerDepthCost.stage model.core.transformer.arithmetic + 2

def predictionSize (model : Generator n bound) : ℕ :=
  model.core.architecture.inputBits + TransformerGateCost.total model.core.transformer.arithmetic
    (FixedPrecisionTransformer.sizeBound model.core.architecture) + 1

def fiberDepth (model : Generator n bound) : ℕ := model.predictionDepth + 2
def fiberSize (model : Generator n bound) : ℕ := 3 * (bound + 1) * model.predictionSize + 10

theorem tokenPrediction_depth_le (model : Generator n bound) (time : ℕ)
    (prefixTokens : Fin time → Fin model.core.architecture.vocabulary) (token : Fin model.core.architecture.vocabulary) :
    Circuit.depth (model.core.tokenPredictionCircuit time prefixTokens token) ≤ model.predictionDepth := by
  have hcontext := model.core.contextCircuit_depth_le time prefixTokens
  have htoken := (model.core.stepTransformer time).tokenClassifier_depth_le token
  change Circuit.depth ((model.core.stepTransformer time).tokenClassifier token) ≤
    (model.core.architecture.layers + 2) * TransformerDepthCost.stage model.core.transformer.arithmetic at htoken
  simp only [Core.tokenPredictionCircuit, Circuit.depth, predictionDepth]
  omega

theorem tokenPrediction_size_le (model : Generator n bound) (time : ℕ)
    (prefixTokens : Fin time → Fin model.core.architecture.vocabulary) (token : Fin model.core.architecture.vocabulary) :
    Circuit.gateCount (model.core.tokenPredictionCircuit time prefixTokens token) ≤ model.predictionSize := by
  have hcontext := model.core.contextCircuit_size_le time prefixTokens
  have htoken := ((model.core.stepTransformer time).tokenClassifier_size_le token).trans (model.core.step_size_le time)
  simp only [Core.tokenPredictionCircuit, Circuit.gateCount, predictionSize]
  omega

theorem answerPrediction_depth_le (model : Generator n bound) (time : ℕ)
    (prefixTokens : Fin time → Fin model.core.architecture.vocabulary) (value : Bool) :
    Circuit.depth (model.core.answerPredictionCircuit time prefixTokens value) ≤ model.predictionDepth := by
  have hcontext := model.core.contextCircuit_depth_le time prefixTokens
  have hmatrix := (model.core.stepTransformer time).compile_depth_le_fixed
  change Circuit.depth (model.core.stepTransformer time).compile ≤
    (model.core.architecture.layers + 2) * TransformerDepthCost.stage model.core.transformer.arithmetic at hmatrix
  have hvalue := FixedPrecisionGenerator.depth_requireValue_le
    (.seq (model.core.contextCircuit time prefixTokens) (model.core.stepTransformer time).compile) value
  change Circuit.depth (FixedPrecisionGenerator.requireValue _ value) ≤ _
  simp only [Circuit.depth] at hvalue
  unfold predictionDepth
  omega

theorem answerPrediction_size_le (model : Generator n bound) (time : ℕ)
    (prefixTokens : Fin time → Fin model.core.architecture.vocabulary) (value : Bool) :
    Circuit.gateCount (model.core.answerPredictionCircuit time prefixTokens value) ≤ model.predictionSize := by
  have hcontext := model.core.contextCircuit_size_le time prefixTokens
  have hmatrix := (model.core.stepTransformer time).compile_gateCount_le_total.trans (model.core.step_size_le time)
  have hvalue := FixedPrecisionGenerator.gateCount_requireValue_le
    (.seq (model.core.contextCircuit time prefixTokens) (model.core.stepTransformer time).compile) value
  change Circuit.gateCount (FixedPrecisionGenerator.requireValue _ value) ≤ _
  simp only [Circuit.gateCount] at hvalue
  unfold predictionSize
  omega

theorem payload_depth_le (model : Generator n bound) (candidate : model.Transcript) :
    Circuit.depth (model.payloadCircuit candidate) ≤ model.predictionDepth + 1 := by
  simp only [payloadCircuit, Circuit.depth]
  apply Nat.add_le_add_right
  exact Finset.sup_le fun time _ => model.tokenPrediction_depth_le _ _ _

theorem payload_size_le (model : Generator n bound) (candidate : model.Transcript) :
    Circuit.gateCount (model.payloadCircuit candidate) ≤ candidate.1.val * model.predictionSize + 1 := by
  simp only [payloadCircuit, Circuit.gateCount]
  apply Nat.add_le_add_right
  calc
    (∑ time : Fin candidate.1.val, Circuit.gateCount
        (model.core.tokenPredictionCircuit time
          (model.candidatePrefix candidate time (Nat.le_of_lt time.isLt)) (candidate.2 time).val)) ≤
      ∑ _time : Fin candidate.1.val, model.predictionSize :=
        Finset.sum_le_sum fun time _ => model.tokenPrediction_size_le _ _ _
    _ = candidate.1.val * model.predictionSize := by simp

theorem fiberCheck_depth_le (model : Generator n bound) (candidate : model.Transcript)
    (answerBit : Bool) (index : Fin 3) :
    Circuit.depth (model.fiberChecks candidate answerBit index) ≤ model.predictionDepth + 1 := by
  fin_cases index
  · exact model.payload_depth_le candidate
  · change Circuit.depth (model.core.tokenPredictionCircuit _ _ _) ≤ _
    exact (model.tokenPrediction_depth_le _ _ _).trans (Nat.le_succ _)
  · change Circuit.depth (model.core.answerPredictionCircuit _ _ _) ≤ _
    exact (model.answerPrediction_depth_le _ _ _).trans (Nat.le_succ _)

theorem fiberCheck_size_le (model : Generator n bound) (candidate : model.Transcript)
    (answerBit : Bool) (index : Fin 3) :
    Circuit.gateCount (model.fiberChecks candidate answerBit index) ≤
      (candidate.1.val + 1) * model.predictionSize + 1 := by
  fin_cases index
  · have h := model.payload_size_le candidate
    change Circuit.gateCount (model.payloadCircuit candidate) ≤ _
    nlinarith
  · have h := model.tokenPrediction_size_le candidate.1.val (model.payloadTokens candidate) model.core.separator
    change Circuit.gateCount (model.core.tokenPredictionCircuit candidate.1.val (model.payloadTokens candidate) model.core.separator) ≤ _
    nlinarith
  · have h := model.answerPrediction_size_le (candidate.1.val + 1)
      (Fin.snoc (model.payloadTokens candidate) model.core.separator) answerBit
    change Circuit.gateCount (model.core.answerPredictionCircuit (candidate.1.val + 1)
      (Fin.snoc (model.payloadTokens candidate) model.core.separator) answerBit) ≤ _
    nlinarith

theorem fiberCircuit_depth_le (model : Generator n bound) (candidate : model.Transcript) (answerBit : Bool) :
    Circuit.depth (model.fiberCircuit candidate answerBit) ≤ model.fiberDepth := by
  simp only [fiberCircuit, Circuit.depth, fiberDepth]
  apply Nat.add_le_add_right
  exact Finset.sup_le fun index _ => model.fiberCheck_depth_le candidate answerBit index

theorem fiberCircuit_size_le (model : Generator n bound) (candidate : model.Transcript) (answerBit : Bool) :
    Circuit.gateCount (model.fiberCircuit candidate answerBit) ≤ model.fiberSize := by
  have hsum : (∑ index : Fin 3, Circuit.gateCount (model.fiberChecks candidate answerBit index)) ≤
      3 * ((candidate.1.val + 1) * model.predictionSize + 1) := by
    calc
      _ ≤ ∑ _index : Fin 3, ((candidate.1.val + 1) * model.predictionSize + 1) :=
        Finset.sum_le_sum fun index _ => model.fiberCheck_size_le candidate answerBit index
      _ = _ := by simp
  have hlength : candidate.1.val ≤ bound := by have h := candidate.1.isLt; omega
  simp only [fiberCircuit, Circuit.gateCount, fiberSize]
  nlinarith

def parityTrace (model : Generator n bound) (correct : ∀ input, model.answer input = Tal.parity input) :
    Footprint.ParityTrace n model.Transcript where
  transcript := model.transcript
  answer := model.answer
  answer_correct := correct

def fiberCircuitFamily (model : Generator n bound) (correct : ∀ input, model.answer input = Tal.parity input) :
    Footprint.FiberCircuitFamily (model.parityTrace correct) model.fiberDepth model.fiberSize where
  circuit := model.fiberCircuit
  correct := fun candidate answer input => model.eval_fiberCircuit input candidate answer
  depth_le := model.fiberCircuit_depth_le
  size_le := model.fiberCircuit_size_le

theorem footprint (tal : Tal.FourierTailTheorem) (model : Generator n bound)
    (correct : ∀ input, model.answer input = Tal.parity input) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (Distribution.uniform (Bits n)).mutualInformation id model.transcript := by
  rw [Distribution.mutualInformation_id_eq_entropy]
  have h := Footprint.footprint_from_tal tal (model.parityTrace correct)
    (model.fiberCircuitFamily correct) hn (by unfold fiberSize; omega)
  unfold Footprint.ParityTrace.uniformMutualInformation at h
  rw [← EntropyCoding.uniform_entropy_eq_transcriptEntropy] at h
  exact h

def taskTrace (model : Generator n bound) (target : Bits n → Bool)
    (correct : ∀ input, model.answer input = target input) :
    TaskFootprint.BooleanTrace n target model.Transcript where
  transcript := model.transcript
  answer := model.answer
  answer_correct := correct

def taskFiberCircuitFamily (model : Generator n bound) (target : Bits n → Bool)
    (correct : ∀ input, model.answer input = target input) :
    TaskFootprint.FiberCircuitFamily (model.taskTrace target correct) model.fiberDepth model.fiberSize where
  circuit := model.fiberCircuit
  correct := fun candidate answer input => model.eval_fiberCircuit input candidate answer
  depth_le := model.fiberCircuit_depth_le
  size_le := model.fiberCircuit_size_le

theorem task_footprint (model : Generator n bound) (target : Bits n → Bool)
    (correct : ∀ input, model.answer input = target input) (rate : ℝ)
    (correlation : TaskFootprint.SignCorrelationBound target model.fiberDepth model.fiberSize rate)
    (hpositive : 0 < rate + |TaskFootprint.targetBias target|) :
    -Real.logb 2 (rate + |TaskFootprint.targetBias target|) ≤
      (Distribution.uniform (Bits n)).mutualInformation id model.transcript := by
  rw [Distribution.mutualInformation_id_eq_entropy]
  have h := TaskFootprint.footprint (model.taskTrace target correct)
    (model.taskFiberCircuitFamily target correct) correlation hpositive
  unfold TaskFootprint.BooleanTrace.uniformMutualInformation
    Footprint.ParityTrace.uniformMutualInformation at h
  rw [← EntropyCoding.uniform_entropy_eq_transcriptEntropy] at h
  exact h

theorem nonterminal_card (model : Generator n bound) :
    Fintype.card model.Nonterminal = model.core.architecture.vocabulary - 1 := by
  unfold Nonterminal
  rw [Fintype.card_subtype_compl (fun token => token = model.core.separator)]
  simp [Fintype.card_subtype]

def payload (model : Generator n bound) (candidate : model.Transcript) :
    List (Fin (Fintype.card model.Nonterminal)) :=
  List.ofFn (fun time => Fintype.equivFin model.Nonterminal (candidate.2 time))

theorem payload_injective (model : Generator n bound) : Function.Injective model.payload := by
  intro first second heq
  have hlength := congrArg List.length heq
  simp only [payload, List.length_ofFn] at hlength
  have hcount : first.1 = second.1 := Fin.ext hlength
  rcases first with ⟨firstCount, firstTokens⟩
  rcases second with ⟨secondCount, secondTokens⟩
  dsimp only at hcount
  cases hcount
  congr 1
  funext time
  exact (Fintype.equivFin model.Nonterminal).injective (congrFun (List.ofFn_injective heq) time)

def expectedLength (model : Generator n bound) : ℝ :=
  (Distribution.uniform (Bits n)).expectation (fun input => ((model.length input).val + 1 : ℕ))

theorem entropy_le_expected_length (model : Generator n bound) (hv : 1 < model.core.architecture.vocabulary) :
    (Distribution.uniform (Bits n)).entropy model.transcript ≤
      model.expectedLength * Real.logb 2 (model.core.architecture.vocabulary : ℝ) := by
  have hcard := model.nonterminal_card
  have hpositive : 0 < Fintype.card model.Nonterminal := by omega
  have h := TerminatedCode.entropy_le_expected_terminated_length
    (Distribution.uniform (Bits n)) model.transcript (Fintype.card model.Nonterminal)
    hpositive model.payload model.payload_injective
  have htotal : Fintype.card model.Nonterminal + 1 = model.core.architecture.vocabulary := by omega
  rw [htotal] at h
  simpa [payload, expectedLength, transcript] using h

/-- The paper's full-vocabulary expected-length lower bound for actual greedy
matrix autoregression, with the terminal separator included in trace length. -/
theorem expected_length_lower_bound (tal : Tal.FourierTailTheorem) (model : Generator n bound)
    (correct : ∀ input, model.answer input = Tal.parity input) (hn : 1 ≤ n)
    (hv : 1 < model.core.architecture.vocabulary) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.expectedLength := by
  have hfootprint := model.footprint tal correct hn
  rw [Distribution.mutualInformation_id_eq_entropy] at hfootprint
  have hlog : 0 < Real.logb 2 (model.core.architecture.vocabulary : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hv)
  apply (div_le_iff₀ hlog).mpr
  exact hfootprint.trans (model.entropy_le_expected_length hv)

end Generator

end TokenAutoregressive
