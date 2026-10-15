import VerifiedMultiplicationSource
import ExactPolylogTrace
import TalComplete

/-! The paper's native four-token multiplication construction with no
external multiplication algorithm or Tal premise. Ordinary NC⁰ PRG security
is the research premise of the combined information/privacy theorem. -/

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace VerifiedMultiplication
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
open VerifiedMultiplicationSource

def model (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :=
  ExactPolylogBit.model machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound stretch hstretch generator n

def inputEncoding (stretch : ℝ) (n : ℕ) (input : Bits (n + n))
    (seed : Bits (PolylogPrivateBit.seedLengths 64 State (Fin 4) coefficient stretch n)) :=
  ExactPolylogBit.inputEncoding (times := times) machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) coefficient stretch n (initialTape n input) seed

def traceModel (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :=
  ExactPolylogTrace.model machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound stretch hstretch generator sources n

def seedLengths (stretch : ℝ) := PolylogPrivateBit.seedLengths 64 State (Fin 4) coefficient stretch

def OutputCorrect (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop := ∀ n, 1 ≤ n →
  ∀ (input : Bits (n + n)) (seed : Bits (seedLengths stretch n)) (output : Fin 2),
    (model stretch hstretch generator n).generatedToken (inputEncoding stretch n input seed)
      ⟨PolylogPrivateBit.payloadLength (times := times) machine SchonhageInitializer.inputTape n + 1 + output.val, by
        change PolylogPrivateBit.payloadLength (times := times) machine SchonhageInitializer.inputTape n + 1 + output.val <
          PolylogPrivateBit.payloadLength (times := times) machine SchonhageInitializer.inputTape n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryOutput (ExactTaskAlphabet.boolCode
        (if output = 0 then some (MultiplicationFootprint.middleBitTarget n input) else none)))

theorem output_correct (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : OutputCorrect stretch hstretch generator := by
  intro n hn input seed output
  rw [model, inputEncoding, ExactPolylogBit.generated_output, middle_bit n hn input]

def Resources (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop :=
  (∃ heads precision : ℕ, ∀ n, (model stretch hstretch generator n).architecture.vocabulary = 4 ∧
    (model stretch hstretch generator n).architecture.layers = 1 ∧
    (model stretch hstretch generator n).architecture.heads = heads ∧
    (model stretch hstretch generator n).parameters.scalarBits = precision) ∧
  (∃ D P : ℕ, ∀ n, (model stretch hstretch generator n).architecture.hiddenWidth ≤ D * (n + 1) ^ 4 ∧
    (model stretch hstretch generator n).architecture.parameterCount ≤ P * (n + 1) ^ 8)

theorem resources (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Resources stretch hstretch generator := by
  exact ⟨ExactPolylogBit.architecture_fixed machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
      SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound stretch hstretch generator,
    ExactPolylogBit.polynomial_resources machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
      SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound stretch hstretch generator⟩

def encodedTrace {codeWidth : ℕ} (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (encoding : Fin 4 → Bits codeWidth)
    (n : ℕ) (input : Bits (n + n)) (seed : Bits (seedLengths stretch n)) :=
  ExactEncryptedAlphabet.encodedTrace ExactTaskAlphabet.binaryAlphabet
    (originalSchedule machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
      (horizonLevel (max 1 (times n))) SchonhageInitializer.inputTape (fun _ : Fin 1 => ((n - 1 : ℕ) : ℤ)))
    (originalTransition machine IntegerMultBounds.Machine.blank)
    ((PolylogPrivateBit.generatorPrefix machine SchonhageInitializer.inputTape coefficient time_bound stretch hstretch generator).generator n)
    (PolylogPrivateBit.outputSources machine SchonhageInitializer.inputTape n)
    (PolylogPrivateBit.decoder machine IntegerMultBounds.Machine.blank SchonhageInitializer.inputTape bit)
    ExactTaskAlphabet.binaryAlphabet.readBit encoding
    (plainPrompt machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
      (horizonLevel (max 1 (times n))) SchonhageInitializer.inputTape (fun _ : Fin 1 => ((n - 1 : ℕ) : ℤ))
      (initialTape n input)) seed

def Privacy (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop :=
  ∀ (codeWidth : ℕ) (encoding : Fin 4 → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n =>
      (PolylogPrivateBit.payloadLength (times := times) machine SchonhageInitializer.inputTape n + 1) * codeWidth)),
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits (n + n))) (predicate : Bits (n + n) → Bool),
      predictionSuccess distribution (encodedTrace stretch hstretch generator encoding n) (monitor.monitor n) predicate ≤
        distribution.bestConstantSuccess predicate + error n

theorem privacy (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom) :
    Privacy stretch hstretch generator := by
  intro codeWidth encoding monitor
  exact ExactPolylogBit.no_readability machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
    SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound stretch hstretch generator
    initialTape secure encoding monitor

def Footprint (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop := ∀ n, 2 ≤ n →
  let M := traceModel stretch hstretch generator n;
  -Real.logb 2 (MultiplicationFootprint.explicitFiberRate n M.fiberDepth M.fiberSize) - (seedLengths stretch n : ℝ) ≤
    (FiniteInformation.Distribution.uniform (Bits (n + n) × Bits (seedLengths stretch n))).mutualInformation Prod.fst M.seededTrace

def LengthBound (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop := ∀ n, 2 ≤ n →
  let M := traceModel stretch hstretch generator n;
  -Real.logb 2 (MultiplicationFootprint.explicitFiberRate n M.fiberDepth M.fiberSize) / Real.logb 2 (4 : ℝ) ≤ M.seededExpectedLength

theorem complete_from_Tal (tal : Tal.FourierTailTheorem) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom) :
    OutputCorrect stretch hstretch generator ∧ Resources stretch hstretch generator ∧
    (∃ C : ℕ, ∀ n, (model stretch hstretch generator n).architecture.contextLength ≤
      C * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3) ∧
    (∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∀ n,
      (seedLengths stretch n : ℝ) ≤ C * (n + 1 : ℝ) ^ alpha) ∧
    Privacy stretch hstretch generator ∧ Footprint stretch hstretch generator ∧ LengthBound stretch hstretch generator := by
  refine ⟨output_correct stretch hstretch generator, resources stretch hstretch generator, ?_, ?_,
    privacy stretch hstretch generator secure, ?_, ?_⟩
  · exact ⟨_, ExactPolylogBit.context_bound machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
      SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound stretch hstretch generator⟩
  · obtain ⟨alpha, hpos, hsub, hbound⟩ := PolylogSeedBudget.sublinear 3
      (size := (PolylogPrivateBit.payloadCoefficient 64 State (Fin 4) coefficient : ℝ)) hstretch
    exact ⟨alpha, _, hpos, hsub, hbound⟩
  · intro n hn
    exact ExactPolylogTrace.multiplication_footprint machine SchonhageInitializer.inputTape IntegerMultBounds.Machine.blank
      SchonhageInitializer.inputTape (fun n => ((n - 1 : ℕ) : ℤ)) bit coefficient time_bound stretch hstretch generator sources
      tal n hn (middle_bit n (by omega))
  · intro n hn
    apply TokenAutoregressive.Generator.seeded_multiplication_expected_length_lower_bound tal _ _ hn (by decide : 1 < 4)
    intro input seed
    unfold traceModel
    rw [ExactPolylogTrace.answer_correct]
    exact middle_bit n (by omega) input

/-- The current headline needs only the permitted generator and PRG-security premise. -/
theorem complete (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom) :
    OutputCorrect stretch hstretch generator ∧ Resources stretch hstretch generator ∧
    (∃ C : ℕ, ∀ n, (model stretch hstretch generator n).architecture.contextLength ≤
      C * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3) ∧
    (∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∀ n,
      (seedLengths stretch n : ℝ) ≤ C * (n + 1 : ℝ) ^ alpha) ∧
    Privacy stretch hstretch generator ∧ Footprint stretch hstretch generator ∧ LengthBound stretch hstretch generator :=
  complete_from_Tal TalComplete.fourierTailTheorem stretch hstretch generator secure

end VerifiedMultiplication
