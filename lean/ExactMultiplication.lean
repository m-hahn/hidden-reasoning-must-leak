import ExactNearLinearTrace

/-! # The permitted multiplication import closes the exact four-token model

The source data is fixed across all operand lengths. Its ordinary time bound
is the only algorithmic field; central-bit correctness is derived from the
permitted import. The native upper and information bounds use that same data.
-/
noncomputable section
namespace ExactMultiplication
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix

structure Source where
  tapes : ℕ
  states : ℕ
  symbols : ℕ
  machine : MultitapeTuring.Machine tapes (Fin states) (Fin symbols)
  inputTape : Fin tapes
  outputTape : Fin tapes
  blank : Fin symbols
  bitSymbol : Bool → Fin symbols
  bit : Fin symbols → Bool
  coefficient : ℕ
  times : ℕ → ℕ
  time_bound : ∀ n, times n ≤ coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1)

def Source.correct (source : Source) : Prop := ∀ N, 1 ≤ N → ∀ input : Bits (N + N),
  source.bit ((source.machine.run (2 ^ horizonLevel (max 1 (source.times N)))
    (MultitapeEfficientPhase.sourceInitial source.machine (bitTape source.blank source.bitSymbol source.inputTape input))).tape
      source.outputTape ((N - 1 : ℕ) : ℤ)) = MultiplicationFootprint.middleBitTarget N input

theorem source_exists (imported : FastMultiplication.MultitapeNLogNTheorem) : ∃ source : Source, source.correct := by
  obtain ⟨tapes, states, symbols, machine, inputTape, outputTape, blank, bitSymbol, bit,
    halted, coefficient, times, _, _, _, htime, hterminal, hcorrect⟩ := imported
  refine ⟨⟨tapes, states, symbols, machine, inputTape, outputTape, blank, bitSymbol, bit, coefficient, times, htime⟩, ?_⟩
  intro N hN input
  change bit ((machine.run (2 ^ horizonLevel (max 1 (times N)))
    (FastMultiplication.initialConfiguration machine inputTape blank bitSymbol input)).tape outputTape ((N - 1 : ℕ) : ℤ)) = _
  rw [machine.terminal_run_after _ (times N) _
    ((Nat.le_max_right 1 (times N)).trans (horizon_covers (max 1 (times N)))) (hterminal _ (hcorrect N input).1)]
  rw [(hcorrect N input).2 ⟨N - 1, by omega⟩, FastMultiplication.middleBit_eq N hN input]

def model (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (N : ℕ) :=
  ExactNearLinear.model source.machine source.inputTape source.blank source.outputTape (fun N => ((N - 1 : ℕ) : ℤ)) source.bit
    source.coefficient source.time_bound stretch hstretch generator N

def seedLengths (source : Source) (stretch : ℝ) :=
  NearLinearPrivateBit.seedLengths source.tapes (Fin source.states) (Fin source.symbols) source.coefficient stretch

def traceModel (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (N : ℕ) :=
  ExactNearLinearTrace.model source.machine source.inputTape source.blank source.bitSymbol source.inputTape source.outputTape
    (fun N => ((N - 1 : ℕ) : ℤ)) source.bit source.coefficient source.time_bound stretch hstretch generator N (N + N)

def OutputCorrect (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop := ∀ N, 1 ≤ N →
  ∀ (input : Bits (N + N)) (seed : Bits (seedLengths source stretch N)) (output : Fin 2),
    (model source stretch hstretch generator N).generatedToken
      (ExactNearLinear.inputEncoding source.machine source.inputTape source.blank source.outputTape
        (fun N => ((N - 1 : ℕ) : ℤ)) source.coefficient stretch N (bitTape source.blank source.bitSymbol source.inputTape input) seed)
      ⟨NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1 + output.val, by
        change NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1 + output.val <
          NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryOutput (ExactTaskAlphabet.boolCode
        (if output = 0 then some (MultiplicationFootprint.middleBitTarget N input) else none)))

def Footprint (tal : Tal.FourierTailTheorem) (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop := ∀ N, 2 ≤ N →
  let M := traceModel source stretch hstretch generator N;
  -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N M.fiberDepth M.fiberSize) - (seedLengths source stretch N : ℝ) ≤
    (FiniteInformation.Distribution.uniform (Bits (N + N) × Bits (seedLengths source stretch N))).mutualInformation Prod.fst M.seededTrace

def encodedTrace {codeWidth : ℕ} (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (encoding : Fin 4 → Bits codeWidth)
    (N : ℕ) (input : Bits (N + N)) (seed : Bits (seedLengths source stretch N)) :=
  ExactEncryptedAlphabet.encodedTrace ExactTaskAlphabet.binaryAlphabet
    (EncryptedMultitapeOutput.originalSchedule source.machine source.inputTape source.blank
      (horizonLevel (max 1 (source.times N))) source.outputTape (fun _ : Fin 1 => ((N - 1 : ℕ) : ℤ)))
    (EncryptedMultitapeOutput.originalTransition source.machine source.blank)
    ((NearLinearPrivateBit.generatorPrefix source.machine source.inputTape source.coefficient source.time_bound stretch hstretch generator).generator N)
    (NearLinearPrivateBit.outputSources source.machine source.inputTape N)
    (NearLinearPrivateBit.decoder source.machine source.blank source.outputTape source.bit) ExactTaskAlphabet.binaryAlphabet.readBit encoding
    (EncryptedMultitapeOutput.plainPrompt source.machine source.inputTape source.blank (horizonLevel (max 1 (source.times N)))
      source.outputTape (fun _ : Fin 1 => ((N - 1 : ℕ) : ℤ)) (bitTape source.blank source.bitSymbol source.inputTape input)) seed

def Privacy (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop :=
  ∀ (codeWidth : ℕ) (encoding : Fin 4 → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun N =>
      (NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1) * codeWidth)),
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ N
      (distribution : FiniteDistribution (Bits (N + N))) (predicate : Bits (N + N) → Bool),
      predictionSuccess distribution (encodedTrace source stretch hstretch generator encoding N) (monitor.monitor N) predicate ≤
        distribution.bestConstantSuccess predicate + error N

def Resources (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop :=
  (∃ heads precision : ℕ, ∀ N, (model source stretch hstretch generator N).architecture.vocabulary = 4 ∧
    (model source stretch hstretch generator N).architecture.layers = 1 ∧
    (model source stretch hstretch generator N).architecture.heads = heads ∧
    (model source stretch hstretch generator N).parameters.scalarBits = precision) ∧
  (∃ D P : ℕ, ∀ N, (model source stretch hstretch generator N).architecture.hiddenWidth ≤ D * (N + 1) ^ 3 ∧
    (model source stretch hstretch generator N).architecture.parameterCount ≤ P * (N + 1) ^ 6)

def LengthBound (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Prop := ∀ N, 2 ≤ N →
  let M := traceModel source stretch hstretch generator N;
  -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N M.fiberDepth M.fiberSize) / Real.logb 2 (4 : ℝ) ≤ M.seededExpectedLength

theorem privacy (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom) :
    Privacy source stretch hstretch generator := by
  intro codeWidth encoding monitor
  exact ExactNearLinear.no_readability source.machine source.inputTape source.blank source.outputTape (fun N => ((N - 1 : ℕ) : ℤ))
    source.bit source.coefficient source.time_bound stretch hstretch generator
    (fun N input => bitTape source.blank source.bitSymbol source.inputTape input) secure encoding monitor

theorem resources (source : Source) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) : Resources source stretch hstretch generator := by
  refine ⟨?_, ExactNearLinear.polynomial_resources source.machine source.inputTape source.blank source.outputTape
    (fun N => ((N - 1 : ℕ) : ℤ)) source.bit source.coefficient source.time_bound stretch hstretch generator⟩
  refine ⟨(model source stretch hstretch generator 0).architecture.heads, (model source stretch hstretch generator 0).parameters.scalarBits, ?_⟩
  intro N
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- No extra source-correctness or simulation premise remains. Both the
complete native answer/EOS and seeded footprint are on the four-token model
with the same fixed source, raw initializer, and numerical matrices. -/
theorem complete (imported : FastMultiplication.MultitapeNLogNTheorem) (tal : Tal.FourierTailTheorem)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)
    (secure : generator.IsPseudorandom) :
    ∃ source : Source,
      OutputCorrect source stretch hstretch generator ∧ Footprint tal source stretch hstretch generator ∧
      (∃ C : ℕ, ∀ N, (model source stretch hstretch generator N).architecture.contextLength ≤
        C * (N + 1) * (Nat.log 2 (N + 1) + 1) ^ 2) ∧
      (∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∀ N,
        (seedLengths source stretch N : ℝ) ≤ C * (N + 1 : ℝ) ^ alpha) ∧
      Privacy source stretch hstretch generator ∧ Resources source stretch hstretch generator ∧ LengthBound source stretch hstretch generator := by
  obtain ⟨source, hcorrect⟩ := source_exists imported
  refine ⟨source, ?_, ?_, ?_, ?_, privacy source stretch hstretch generator secure, resources source stretch hstretch generator, ?_⟩
  · intro N hN input seed output
    rw [model, ExactNearLinear.generated_output, hcorrect N hN input]
  · intro N hN
    exact ExactNearLinearTrace.multiplication_footprint source.machine source.inputTape source.blank source.bitSymbol source.inputTape
      source.outputTape (fun N => ((N - 1 : ℕ) : ℤ)) source.bit source.coefficient source.time_bound stretch hstretch generator
      tal N hN (hcorrect N (by omega))
  · exact ⟨_, ExactNearLinear.context_bound source.machine source.inputTape source.blank source.outputTape
      (fun N => ((N - 1 : ℕ) : ℤ)) source.bit source.coefficient source.time_bound stretch hstretch generator⟩
  · obtain ⟨alpha, hpos, hsub, hbound⟩ := LogSquaredSeedBudget.sublinear
      (size := (NearLinearPrivateBit.payloadCoefficient source.tapes (Fin source.states) (Fin source.symbols) source.coefficient : ℝ)) hstretch
    exact ⟨alpha, _, hpos, hsub, hbound⟩
  · intro N hN
    apply TokenAutoregressive.Generator.seeded_multiplication_expected_length_lower_bound tal _ _ hN (by decide : 1 < 4)
    intro input seed
    unfold traceModel
    rw [ExactNearLinearTrace.answer_correct]
    exact hcorrect N (by omega) input

end ExactMultiplication
