import EntropyCoding

/-!
# Separator-terminated matrix autoregression

The token label and separator flag are readouts of the same matrix model.
The visible trace stops at the first separator, with a uniform finite bound
on its length.  The answer is the next generated token.  This module supplies
the finite transcript space needed for variable-length source coding.
-/

noncomputable section
open scoped BigOperators

namespace TerminatedAutoregressive

open TransformerAC0 Autoregressive FiniteInformation

def separatorModel (data : FixedPrecisionGenerator n bound)
    (separatorLabel : Fin data.architecture.vocabulary → Bool) :
    FixedPrecisionTransformer data.architecture :=
  { data.transformer with outputLabel := separatorLabel }

def separatorAt (data : FixedPrecisionGenerator n bound)
    (separatorLabel : Fin data.architecture.vocabulary → Bool)
    (input : Bits n) (time : ℕ) : Bool :=
  (separatorModel data separatorLabel).run
    (data.contextInput input time (fun previous => data.generatedToken input previous))

/-- A terminating execution uses the same matrices for the token bit and
the separator classifier. Finite termination is part of successful task
computation, as in the paper's maximum trace length. -/
structure Generator (n bound : ℕ) where
  data : FixedPrecisionGenerator n bound
  separatorLabel : Fin data.architecture.vocabulary → Bool
  terminates : ∀ input : Bits n, ∃ time : ℕ,
    time ≤ bound ∧ separatorAt data separatorLabel input time = true

/-- Bounded binary payloads; the terminal separator is implicit. -/
abbrev Transcript (bound : ℕ) := (length : Fin (bound + 1)) × Bits length.val

namespace Generator

variable {n bound : ℕ}

def stop (model : Generator n bound) (input : Bits n) (time : ℕ) : Bool :=
  separatorAt model.data model.separatorLabel input time

def length (model : Generator n bound) (input : Bits n) : Fin (bound + 1) :=
  ⟨Nat.find (model.terminates input), by
    have h := (Nat.find_spec (model.terminates input)).1
    omega⟩

theorem stop_at_length (model : Generator n bound) (input : Bits n) :
    model.stop input (model.length input) = true :=
  (Nat.find_spec (model.terminates input)).2

theorem stop_before_length (model : Generator n bound) (input : Bits n)
    (time : ℕ) (htime : time < model.length input) : model.stop input time = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hstop
  have hbound := (Nat.find_spec (model.terminates input)).1
  have hnot := Nat.find_min (model.terminates input) htime
  apply hnot
  exact ⟨by unfold length at htime; dsimp only at htime; omega, hstop⟩

def transcript (model : Generator n bound) (input : Bits n) : Transcript bound :=
  ⟨model.length input, fun time => model.data.generatedToken input time⟩

def answer (model : Generator n bound) (input : Bits n) : Bool :=
  model.data.generatedToken input ((model.length input).val + 1)

def withLength (model : Generator n bound) (count : ℕ) : FixedPrecisionGenerator n count where
  architecture := model.data.architecture
  transformer := model.data.transformer
  context := model.data.context

@[simp] theorem withLength_generatedToken
    (model : Generator n bound) (count : ℕ) (input : Bits n) (time : ℕ) :
    (model.withLength count).generatedToken input time = model.data.generatedToken input time := by
  induction time using Nat.strong_induction_on with
  | h time ih =>
      rw [FixedPrecisionGenerator.generatedToken, FixedPrecisionGenerator.generatedToken]
      change model.data.transformer.run _ = model.data.transformer.run _
      congr 1
      funext wire
      unfold FixedPrecisionGenerator.contextInput
      congr 2
      funext previous
      exact ih previous previous.isLt

def AcceptsCandidate (model : Generator n bound) (input : Bits n)
    (candidate : Transcript bound) : Prop :=
  (∀ time : Fin candidate.1.val, model.data.generatedToken input time = candidate.2 time) ∧
    (∀ time : Fin candidate.1.val, model.stop input time = false) ∧
      model.stop input candidate.1 = true

theorem acceptsCandidate_iff (model : Generator n bound) (input : Bits n)
    (candidate : Transcript bound) :
    model.AcceptsCandidate input candidate ↔ model.transcript input = candidate := by
  constructor
  · rintro ⟨hbits, hprior, hstop⟩
    have hle : (model.length input).val ≤ candidate.1.val :=
      Nat.find_min' (model.terminates input) ⟨by have h := candidate.1.isLt; omega, hstop⟩
    have hequal : model.length input = candidate.1 := by
      apply Fin.ext
      apply le_antisymm hle
      by_contra hnot
      have hlt : (model.length input).val < candidate.1.val := by omega
      have h := hprior ⟨(model.length input).val, hlt⟩
      have hs := model.stop_at_length input
      simp only at h
      rw [hs] at h
      contradiction
    unfold transcript
    rcases candidate with ⟨count, bits⟩
    dsimp only at hequal hbits ⊢
    rw [hequal]
    congr 1
    funext time
    exact hbits time
  · intro htrace
    have hcount : model.length input = candidate.1 := congrArg Sigma.fst htrace
    subst candidate
    refine ⟨fun _ => rfl, ?_, model.stop_at_length input⟩
    intro time
    exact model.stop_before_length input time time.isLt

def candidatePrefix (candidate : Transcript bound) (time : ℕ) (htime : time ≤ candidate.1.val) : Bits time :=
  fun previous => candidate.2 ⟨previous.val, previous.isLt.trans_le htime⟩

theorem prefix_eq_of_bits (model : Generator n bound) (input : Bits n)
    (candidate : Transcript bound)
    (hbits : ∀ time : Fin candidate.1.val, model.data.generatedToken input time = candidate.2 time)
    (time : ℕ) (htime : time ≤ candidate.1.val) :
    (fun previous : Fin time => model.data.generatedToken input previous) =
      candidatePrefix candidate time htime := by
  funext previous
  exact hbits ⟨previous.val, previous.isLt.trans_le htime⟩

def stopPredictionCircuit (model : Generator n bound) (time : ℕ) (prefixBits : Bits time) : Circuit n 1 :=
  .seq (model.data.contextCircuit time prefixBits) (separatorModel model.data model.separatorLabel).compile

@[simp] theorem eval_stopPredictionCircuit (model : Generator n bound) (input : Bits n)
    (time : ℕ) (prefixBits : Bits time) :
    Circuit.eval (model.stopPredictionCircuit time prefixBits) input 0 =
      (separatorModel model.data model.separatorLabel).run (model.data.contextInput input time prefixBits) := by
  simp [stopPredictionCircuit, Circuit.eval, FixedPrecisionTransformer.compile_correct]

def noStopCircuit (model : Generator n bound) (candidate : Transcript bound) : Circuit n 1 :=
  .seq (.bundle fun time : Fin candidate.1.val =>
    FixedPrecisionGenerator.requireValue
      (model.stopPredictionCircuit time (candidatePrefix candidate time (Nat.le_of_lt time.isLt))) false)
    (.andGate candidate.1.val)

def branchChecks (model : Generator n bound) (candidate : Transcript bound)
    (separatorBit answerBit : Bool) : Fin 5 → Circuit n 1 :=
  ![(model.withLength candidate.1.val).transcriptCircuit candidate.2,
    model.noStopCircuit candidate,
    FixedPrecisionGenerator.requireValue
      (model.stopPredictionCircuit candidate.1.val candidate.2) true,
    FixedPrecisionGenerator.requireValue
      (model.data.predictionCircuit candidate.1.val candidate.2) separatorBit,
    FixedPrecisionGenerator.requireValue
      (model.data.predictionCircuit (candidate.1.val + 1) (Fin.snoc candidate.2 separatorBit)) answerBit]

def branchCircuit (model : Generator n bound) (candidate : Transcript bound)
    (separatorBit answerBit : Bool) : Circuit n 1 :=
  .seq (.bundle (model.branchChecks candidate separatorBit answerBit)) (.andGate 5)

theorem eval_branchCircuit_iff (model : Generator n bound) (input : Bits n)
    (candidate : Transcript bound) (separatorBit answerBit : Bool) :
    Circuit.eval (model.branchCircuit candidate separatorBit answerBit) input 0 = true ↔
      model.AcceptsCandidate input candidate ∧
        model.data.generatedToken input candidate.1.val = separatorBit ∧
        model.data.generatedToken input (candidate.1.val + 1) = answerBit := by
  have hbitsIff : (model.withLength candidate.1.val).transcript input = candidate.2 ↔
      ∀ time : Fin candidate.1.val, model.data.generatedToken input time = candidate.2 time := by
    simp [FixedPrecisionGenerator.transcript, funext_iff]
  have hhead : candidatePrefix candidate candidate.1.val (Nat.le_refl _) = candidate.2 := by
    funext time
    rfl
  simp [branchCircuit, branchChecks, noStopCircuit, Circuit.eval,
    Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    FixedPrecisionGenerator.eval_transcriptCircuit, FixedPrecisionGenerator.eval_requireValue,
    eval_stopPredictionCircuit, FixedPrecisionGenerator.eval_predictionCircuit,
    decide_eq_true_eq, and_true, hbitsIff]
  constructor
  · rintro ⟨hbits, hprior, hstop, hsep, hanswer⟩
    have hprefix := model.prefix_eq_of_bits input candidate hbits candidate.1.val (Nat.le_refl _)
    rw [hhead] at hprefix
    have hprior' : ∀ time : Fin candidate.1.val, model.stop input time = false := by
      intro time
      have h := hprior time
      rw [stop, separatorAt, model.prefix_eq_of_bits input candidate hbits time (Nat.le_of_lt time.isLt)]
      exact h
    have hstop' : model.stop input candidate.1.val = true := by
      rw [stop, separatorAt, hprefix]
      exact hstop
    have hsep' : model.data.generatedToken input candidate.1.val = separatorBit := by
      rw [FixedPrecisionGenerator.generatedToken, hprefix]
      exact hsep
    have hprefixNext :
        (fun previous : Fin (candidate.1.val + 1) => model.data.generatedToken input previous) =
          Fin.snoc candidate.2 separatorBit := by
      funext previous
      refine Fin.lastCases ?_ (fun before => ?_) previous
      · simpa using hsep'
      · simpa using hbits before
    have hanswer' : model.data.generatedToken input (candidate.1.val + 1) = answerBit := by
      rw [FixedPrecisionGenerator.generatedToken, hprefixNext]
      exact hanswer
    exact ⟨⟨hbits, hprior', hstop'⟩, hsep', hanswer'⟩
  · rintro ⟨⟨hbits, hprior, hstop⟩, hsep, hanswer⟩
    have hprefix := model.prefix_eq_of_bits input candidate hbits candidate.1.val (Nat.le_refl _)
    rw [hhead] at hprefix
    refine ⟨hbits, ?_, ?_, ?_, ?_⟩
    · intro time
      have h := hprior time
      rw [stop, separatorAt, model.prefix_eq_of_bits input candidate hbits time (Nat.le_of_lt time.isLt)] at h
      exact h
    · rw [stop, separatorAt, hprefix] at hstop
      exact hstop
    · rw [FixedPrecisionGenerator.generatedToken, hprefix] at hsep
      exact hsep
    · have hprefixNext :
          (fun previous : Fin (candidate.1.val + 1) => model.data.generatedToken input previous) =
            Fin.snoc candidate.2 separatorBit := by
        funext previous
        refine Fin.lastCases ?_ (fun before => ?_) previous
        · simpa using hsep
        · simpa using hbits before
      rw [FixedPrecisionGenerator.generatedToken, hprefixNext] at hanswer
      exact hanswer

/-- The separator label's internal data bit is not part of the visible
payload. Enumerating both possibilities keeps the fiber circuit exact. -/
def fiberCircuit (model : Generator n bound) (candidate : Transcript bound) (answerBit : Bool) : Circuit n 1 :=
  .seq (.parallel (model.branchCircuit candidate false answerBit)
    (model.branchCircuit candidate true answerBit)) (.orGate 2)

@[simp] theorem eval_fiberCircuit (model : Generator n bound) (input : Bits n)
    (candidate : Transcript bound) (answerBit : Bool) :
    Circuit.eval (model.fiberCircuit candidate answerBit) input 0 =
      decide (model.transcript input = candidate ∧ model.answer input = answerBit) := by
  apply Bool.eq_iff_iff.mpr
  simp only [fiberCircuit, Circuit.eval, decide_eq_true_eq]
  rw [Fin.exists_fin_two]
  change (Circuit.eval (model.branchCircuit candidate false answerBit) input 0 = true ∨
      Circuit.eval (model.branchCircuit candidate true answerBit) input 0 = true) ↔ _
  rw [eval_branchCircuit_iff, eval_branchCircuit_iff, model.acceptsCandidate_iff]
  constructor
  · intro h
    rcases h with ⟨htrace, _, hanswer⟩ | ⟨htrace, _, hanswer⟩
    all_goals
      refine ⟨htrace, ?_⟩
      have hlength := congrArg Sigma.fst htrace
      change model.length input = candidate.1 at hlength
      unfold answer
      rw [hlength]
      exact hanswer
  · rintro ⟨htrace, hanswer⟩
    have hlength := congrArg Sigma.fst htrace
    change model.length input = candidate.1 at hlength
    unfold answer at hanswer
    rw [hlength] at hanswer
    cases hbit : model.data.generatedToken input candidate.1.val
    · exact Or.inl ⟨htrace, rfl, hanswer⟩
    · exact Or.inr ⟨htrace, rfl, hanswer⟩

def baseDepth (model : Generator n bound) : ℕ :=
  max (Circuit.depth model.data.transformer.compile)
    (Circuit.depth (separatorModel model.data model.separatorLabel).compile)

def baseSize (model : Generator n bound) : ℕ :=
  model.data.architecture.inputBits +
    max (Circuit.gateCount model.data.transformer.compile)
      (Circuit.gateCount (separatorModel model.data model.separatorLabel).compile) + 1

def fiberDepth (model : Generator n bound) : ℕ := model.baseDepth + 6
def fiberSize (model : Generator n bound) : ℕ := 10 * (bound + 1) * model.baseSize + 20

theorem prediction_depth_le (model : Generator n bound) (time : ℕ) (prefixBits : Bits time) :
    Circuit.depth (model.data.predictionCircuit time prefixBits) ≤ model.baseDepth + 1 :=
  (model.data.depth_predictionCircuit_le time prefixBits).trans
    (Nat.add_le_add_right (Nat.le_max_left _ _) 1)

theorem stopPrediction_depth_le (model : Generator n bound) (time : ℕ) (prefixBits : Bits time) :
    Circuit.depth (model.stopPredictionCircuit time prefixBits) ≤ model.baseDepth + 1 := by
  have h := model.data.depth_contextCircuit_le_one time prefixBits
  simp only [stopPredictionCircuit, Circuit.depth, baseDepth]
  omega

theorem requirePrediction_size_le (model : Generator n bound) (time : ℕ)
    (prefixBits : Bits time) (value : Bool) :
    Circuit.gateCount (FixedPrecisionGenerator.requireValue
      (model.data.predictionCircuit time prefixBits) value) ≤ model.baseSize := by
  have h := model.data.gateCount_predictionCircuit_le time prefixBits
  have hr := FixedPrecisionGenerator.gateCount_requireValue_le
    (model.data.predictionCircuit time prefixBits) value
  unfold baseSize
  omega

theorem requireStopPrediction_size_le (model : Generator n bound) (time : ℕ)
    (prefixBits : Bits time) (value : Bool) :
    Circuit.gateCount (FixedPrecisionGenerator.requireValue
      (model.stopPredictionCircuit time prefixBits) value) ≤ model.baseSize := by
  have h := model.data.gateCount_contextCircuit_le time prefixBits
  have hr := FixedPrecisionGenerator.gateCount_requireValue_le
    (model.stopPredictionCircuit time prefixBits) value
  have hpred : Circuit.gateCount (model.stopPredictionCircuit time prefixBits) ≤
      model.data.architecture.inputBits +
        Circuit.gateCount (separatorModel model.data model.separatorLabel).compile := by
    simp only [stopPredictionCircuit, Circuit.gateCount]
    exact Nat.add_le_add_right h _
  have hbase : model.data.architecture.inputBits +
      Circuit.gateCount (separatorModel model.data model.separatorLabel).compile + 1 ≤ model.baseSize := by
    unfold baseSize
    omega
  exact hr.trans ((Nat.add_le_add_right hpred 1).trans hbase)

theorem noStop_depth_le (model : Generator n bound) (candidate : Transcript bound) :
    Circuit.depth (model.noStopCircuit candidate) ≤ model.baseDepth + 3 := by
  simp only [noStopCircuit, Circuit.depth]
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro time _
  have h := model.stopPrediction_depth_le time (candidatePrefix candidate time (Nat.le_of_lt time.isLt))
  have hr := FixedPrecisionGenerator.depth_requireValue_le
    (model.stopPredictionCircuit time (candidatePrefix candidate time (Nat.le_of_lt time.isLt))) false
  omega

theorem noStop_size_le (model : Generator n bound) (candidate : Transcript bound) :
    Circuit.gateCount (model.noStopCircuit candidate) ≤ candidate.1.val * model.baseSize + 1 := by
  simp only [noStopCircuit, Circuit.gateCount]
  apply Nat.add_le_add_right
  calc
    (∑ time : Fin candidate.1.val, Circuit.gateCount
        (FixedPrecisionGenerator.requireValue
          (model.stopPredictionCircuit time (candidatePrefix candidate time (Nat.le_of_lt time.isLt))) false)) ≤
      ∑ _time : Fin candidate.1.val, model.baseSize := by
        apply Finset.sum_le_sum
        intro time _
        exact model.requireStopPrediction_size_le _ _ false
    _ = candidate.1.val * model.baseSize := by simp

theorem branchCheck_depth_le (model : Generator n bound) (candidate : Transcript bound)
    (separatorBit answerBit : Bool) (index : Fin 5) :
    Circuit.depth (model.branchChecks candidate separatorBit answerBit index) ≤ model.baseDepth + 3 := by
  fin_cases index <;> simp only [branchChecks, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · simpa only [branchChecks, Matrix.cons_val_zero, withLength, baseDepth] using
      ((model.withLength candidate.1.val).depth_transcriptCircuit_le candidate.2).trans
        (Nat.add_le_add_right (Nat.le_max_left _ _) 3)
  · exact model.noStop_depth_le candidate
  · have h := model.stopPrediction_depth_le candidate.1.val candidate.2
    have hr := FixedPrecisionGenerator.depth_requireValue_le
      (model.stopPredictionCircuit candidate.1.val candidate.2) true
    change Circuit.depth (FixedPrecisionGenerator.requireValue
      (model.stopPredictionCircuit candidate.1.val candidate.2) true) ≤ _
    omega
  · have h := model.prediction_depth_le candidate.1.val candidate.2
    have hr := FixedPrecisionGenerator.depth_requireValue_le
      (model.data.predictionCircuit candidate.1.val candidate.2) separatorBit
    change Circuit.depth (FixedPrecisionGenerator.requireValue
      (model.data.predictionCircuit candidate.1.val candidate.2) separatorBit) ≤ _
    omega
  · have h := model.prediction_depth_le (candidate.1.val + 1) (Fin.snoc candidate.2 separatorBit)
    have hr := FixedPrecisionGenerator.depth_requireValue_le
      (model.data.predictionCircuit (candidate.1.val + 1) (Fin.snoc candidate.2 separatorBit)) answerBit
    change Circuit.depth (FixedPrecisionGenerator.requireValue
      (model.data.predictionCircuit (candidate.1.val + 1) (Fin.snoc candidate.2 separatorBit)) answerBit) ≤ _
    omega

theorem branchCheck_size_le (model : Generator n bound) (candidate : Transcript bound)
    (separatorBit answerBit : Bool) (index : Fin 5) :
    Circuit.gateCount (model.branchChecks candidate separatorBit answerBit index) ≤
      (candidate.1.val + 1) * model.baseSize + 1 := by
  have hbase : model.data.architecture.inputBits +
      Circuit.gateCount model.data.transformer.compile + 1 ≤ model.baseSize := by
    unfold baseSize
    omega
  fin_cases index <;> simp only [branchChecks, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · have h := (model.withLength candidate.1.val).gateCount_transcriptCircuit_le candidate.2
    change Circuit.gateCount ((model.withLength candidate.1.val).transcriptCircuit candidate.2) ≤ _
    apply h.trans
    change candidate.1.val * (model.data.architecture.inputBits +
      Circuit.gateCount model.data.transformer.compile + 1) + 1 ≤ _
    nlinarith
  · have h := model.noStop_size_le candidate
    change Circuit.gateCount (model.noStopCircuit candidate) ≤ _
    nlinarith
  · have h := model.requireStopPrediction_size_le candidate.1.val candidate.2 true
    change Circuit.gateCount (FixedPrecisionGenerator.requireValue
      (model.stopPredictionCircuit candidate.1.val candidate.2) true) ≤ _
    nlinarith
  · have h := model.requirePrediction_size_le candidate.1.val candidate.2 separatorBit
    change Circuit.gateCount (FixedPrecisionGenerator.requireValue
      (model.data.predictionCircuit candidate.1.val candidate.2) separatorBit) ≤ _
    nlinarith
  · have h := model.requirePrediction_size_le (candidate.1.val + 1) (Fin.snoc candidate.2 separatorBit) answerBit
    change Circuit.gateCount (FixedPrecisionGenerator.requireValue
      (model.data.predictionCircuit (candidate.1.val + 1) (Fin.snoc candidate.2 separatorBit)) answerBit) ≤ _
    nlinarith

theorem branchCircuit_depth_le (model : Generator n bound) (candidate : Transcript bound)
    (separatorBit answerBit : Bool) :
    Circuit.depth (model.branchCircuit candidate separatorBit answerBit) ≤ model.baseDepth + 4 := by
  simp only [branchCircuit, Circuit.depth]
  apply Nat.add_le_add_right
  exact Finset.sup_le fun index _ => model.branchCheck_depth_le candidate separatorBit answerBit index

theorem branchCircuit_size_le (model : Generator n bound) (candidate : Transcript bound)
    (separatorBit answerBit : Bool) :
    Circuit.gateCount (model.branchCircuit candidate separatorBit answerBit) ≤
      5 * ((candidate.1.val + 1) * model.baseSize + 1) + 1 := by
  simp only [branchCircuit, Circuit.gateCount]
  apply Nat.add_le_add_right
  calc
    (∑ index : Fin 5, Circuit.gateCount (model.branchChecks candidate separatorBit answerBit index)) ≤
        ∑ _index : Fin 5, ((candidate.1.val + 1) * model.baseSize + 1) :=
      Finset.sum_le_sum fun index _ => model.branchCheck_size_le candidate separatorBit answerBit index
    _ = 5 * ((candidate.1.val + 1) * model.baseSize + 1) := by simp

theorem fiberCircuit_depth_le (model : Generator n bound) (candidate : Transcript bound) (answerBit : Bool) :
    Circuit.depth (model.fiberCircuit candidate answerBit) ≤ model.fiberDepth := by
  have hfalse := model.branchCircuit_depth_le candidate false answerBit
  have htrue := model.branchCircuit_depth_le candidate true answerBit
  simp only [fiberCircuit, Circuit.depth, fiberDepth]
  omega

theorem fiberCircuit_size_le (model : Generator n bound) (candidate : Transcript bound) (answerBit : Bool) :
    Circuit.gateCount (model.fiberCircuit candidate answerBit) ≤ model.fiberSize := by
  have hfalse := model.branchCircuit_size_le candidate false answerBit
  have htrue := model.branchCircuit_size_le candidate true answerBit
  have hlength : candidate.1.val ≤ bound := by have h := candidate.1.isLt; omega
  simp only [fiberCircuit, Circuit.gateCount, fiberSize]
  nlinarith

/-- Depth is controlled by the proved constant-precision matrix compiler,
uniformly over all candidate lengths and separator/data labels. -/
theorem fiberDepth_le_architecture (model : Generator n bound) :
    model.fiberDepth ≤
      (model.data.architecture.layers + 2) *
        TransformerDepthCost.stage model.data.transformer.arithmetic + 6 := by
  have hdata := model.data.transformer.compile_depth_le_fixed
  have hstop := (separatorModel model.data model.separatorLabel).compile_depth_le_fixed
  change Circuit.depth (separatorModel model.data model.separatorLabel).compile ≤
      (model.data.architecture.layers + 2) *
        TransformerDepthCost.stage model.data.transformer.arithmetic at hstop
  unfold fiberDepth baseDepth
  omega

/-- Polynomial architecture recurrence bounding the variable-length fibers.
The recurrence does not depend on the candidate trace or matrix entries. -/
theorem fiberSize_le_architecture (model : Generator n bound) :
    model.fiberSize ≤ 10 * (bound + 1) *
      (model.data.architecture.inputBits +
        TransformerGateCost.total model.data.transformer.arithmetic
          (FixedPrecisionTransformer.sizeBound model.data.architecture) + 1) + 20 := by
  have hdata := model.data.transformer.compile_gateCount_le_total
  have hstop := (separatorModel model.data model.separatorLabel).compile_gateCount_le_total
  change Circuit.gateCount (separatorModel model.data model.separatorLabel).compile ≤
      TransformerGateCost.total model.data.transformer.arithmetic
        (FixedPrecisionTransformer.sizeBound model.data.architecture) at hstop
  have hmax := max_le hdata hstop
  unfold fiberSize baseSize
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.add_le_add_left hmax _) 1)) 20

def parityTrace (model : Generator n bound) (correct : ∀ input, model.answer input = Tal.parity input) :
    Footprint.ParityTrace n (Transcript bound) where
  transcript := model.transcript
  answer := model.answer
  answer_correct := correct

def fiberCircuitFamily (model : Generator n bound) (correct : ∀ input, model.answer input = Tal.parity input) :
    Footprint.FiberCircuitFamily (model.parityTrace correct) model.fiberDepth model.fiberSize where
  circuit := model.fiberCircuit
  correct := fun candidate answer input => model.eval_fiberCircuit input candidate answer
  depth_le := model.fiberCircuit_depth_le
  size_le := model.fiberCircuit_size_le

/-- Footprint for the actual variable-length, separator-terminated execution.
The circuit family and its explicit bounds are derived automatically. -/
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
    TaskFootprint.BooleanTrace n target (Transcript bound) where
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

/-- The same variable-length fiber construction handles all Boolean tasks. -/
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

def bitCode (bit : Bool) : Fin 2 := if bit then 1 else 0

theorem bitCode_injective : Function.Injective bitCode := by
  intro left right heq
  cases left <;> cases right <;> simp_all [bitCode]

def payload (candidate : Transcript bound) : List (Fin 2) :=
  List.ofFn (fun time => bitCode (candidate.2 time))

theorem payload_injective : Function.Injective (payload (bound := bound)) := by
  intro first second heq
  have hlength := congrArg List.length heq
  simp only [payload, List.length_ofFn] at hlength
  have hcount : first.1 = second.1 := Fin.ext hlength
  rcases first with ⟨firstCount, firstBits⟩
  rcases second with ⟨secondCount, secondBits⟩
  dsimp only at hcount
  cases hcount
  congr 1
  funext time
  have hcode := List.ofFn_injective heq
  exact bitCode_injective (congrFun hcode time)

def expectedLength (model : Generator n bound) : ℝ :=
  (Distribution.uniform (Bits n)).expectation (fun input => ((model.length input).val + 1 : ℕ))

theorem entropy_le_expected_length (model : Generator n bound) :
    (Distribution.uniform (Bits n)).entropy model.transcript ≤ model.expectedLength * Real.logb 2 3 := by
  have hcoding := TerminatedCode.entropy_le_expected_terminated_length
    (Distribution.uniform (Bits n)) model.transcript 2 (by decide) payload payload_injective
  simpa [payload, expectedLength, transcript] using hcoding

/-- The full expected-length lower bound, including the terminating
separator. No entropy profile or source-coding premise is supplied. -/
theorem expected_length_lower_bound (tal : Tal.FourierTailTheorem) (model : Generator n bound)
    (correct : ∀ input, model.answer input = Tal.parity input) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) / Real.logb 2 3 ≤
      model.expectedLength := by
  have hfootprint := model.footprint tal correct hn
  rw [Distribution.mutualInformation_id_eq_entropy] at hfootprint
  have hlog : 0 < Real.logb 2 (3 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  exact hfootprint.trans model.entropy_le_expected_length

end Generator

end TerminatedAutoregressive
