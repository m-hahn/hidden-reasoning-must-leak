import PlainBinaryWord
import ExactMultiplication

/-! # Exact four-token aligned multiplication, with no PRG premise -/
noncomputable section
namespace PlainMultiplication
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput

def model (source : ExactMultiplication.Source) (N : ℕ) :=
  ExactEncryptedAlphabet.model ExactTaskAlphabet.binaryAlphabet
    (originalSchedule source.machine source.inputTape source.blank (horizonLevel (max 1 (source.times N)))
      source.outputTape (fun _ : Fin 1 => ((N - 1 : ℕ) : ℤ)))
    (originalTransition source.machine source.blank)
    (PlainBinaryWord.zeroPad (NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1))
    (NearLinearPrivateBit.outputSources source.machine source.inputTape N)
    (NearLinearPrivateBit.decoder source.machine source.blank source.outputTape source.bit) ExactTaskAlphabet.binaryAlphabet.readBit

def inputEncoding (source : ExactMultiplication.Source) (N : ℕ) (input : Bits (N + N)) :=
  ExactEncryptedAlphabet.inputEncoding ExactTaskAlphabet.binaryAlphabet
    (plainPrompt source.machine source.inputTape source.blank (horizonLevel (max 1 (source.times N)))
      source.outputTape (fun _ : Fin 1 => ((N - 1 : ℕ) : ℤ)) (bitTape source.blank source.bitSymbol source.inputTape input))
    (fun index : Fin 0 => Fin.elim0 index)

theorem generated_output (source : ExactMultiplication.Source) (N : ℕ) (input : Bits (N + N)) (output : Fin 2) :
    (model source N).generatedToken (inputEncoding source N input)
      ⟨NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1 + output.val, by
        change NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1 + output.val <
          NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryOutput (ExactTaskAlphabet.boolCode (if output = 0 then
        some (source.bit ((source.machine.run (2 ^ horizonLevel (max 1 (source.times N)))
          (MultitapeEfficientPhase.sourceInitial source.machine (bitTape source.blank source.bitSymbol source.inputTape input))).tape
            source.outputTape ((N - 1 : ℕ) : ℤ))) else none))) := by
  letI : Inhabited (SimulatorSymbol (Fin source.symbols)) := ⟨(source.blank, false)⟩
  letI : Inhabited (SimulatorControl source.tapes (Fin source.states) (Fin source.symbols)) :=
    ⟨MultitapeEfficientPhase.initialControl source.machine source.blank⟩
  unfold model inputEncoding NearLinearPrivateBit.payloadLength
  rw [ExactEncryptedAlphabet.output_correct]
  unfold NearLinearPrivateBit.outputSources
  rw [block_plain]
  unfold NearLinearPrivateBit.decoder decode
  rw [RoutedMatrix.decodeIndicator_indicator]
  simp only [ObliviousMatrix.label, ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply, ObliviousMatrix.controlOf,
    ObliviousProgram.Program.traceToken_control, MultitapeOutputMatrix.output_cell_correct]
  rfl

def contextCoefficient (source : ExactMultiplication.Source) :=
  2 * NearLinearPrivateBit.payloadCoefficient source.tapes (Fin source.states) (Fin source.symbols) source.coefficient +
    2 * vocabulary source.tapes (Fin source.states) (Fin source.symbols) + 3

theorem context_bound (source : ExactMultiplication.Source) (N : ℕ) :
    (model source N).architecture.contextLength + 1 ≤ contextCoefficient source * (N + 1) * (Nat.log 2 (N + 1) + 1) ^ 2 := by
  have hp := NearLinearPrivateBit.payload_bound source.machine source.inputTape source.coefficient source.time_bound N
  have hone : 1 ≤ (N + 1) * (Nat.log 2 (N + 1) + 1) ^ 2 := by
    have hpow := Nat.one_le_pow 2 (Nat.log 2 (N + 1) + 1) (by omega)
    nlinarith
  rw [model, ExactEncryptedAlphabet.context_length]
  simp only [Nat.zero_add]
  change (eventCount source.machine source.inputTape (horizonLevel (max 1 (source.times N))) 0 + 2) *
      vocabulary source.tapes (Fin source.states) (Fin source.symbols) +
    NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 3 ≤ _
  unfold contextCoefficient NearLinearPrivateBit.payloadLength at *
  nlinarith

def padFamily (source : ExactMultiplication.Source) : NC0GeneratorFamily (fun _ => 0)
    (fun N => NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1) where
  locality := 0
  generator _ := PlainBinaryWord.zeroPad _

theorem polynomial_resources (source : ExactMultiplication.Source) :
    ∃ D P : ℕ, ∀ N, (model source N).architecture.hiddenWidth ≤ D * (N + 1) ^ 3 ∧
      (model source N).architecture.parameterCount ≤ P * (N + 1) ^ 6 := by
  apply ExactEncryptedAlphabet.polynomial_resources ExactTaskAlphabet.binaryAlphabet
    (fun N => originalSchedule source.machine source.inputTape source.blank (horizonLevel (max 1 (source.times N)))
      source.outputTape (fun _ : Fin 1 => ((N - 1 : ℕ) : ℤ)))
    (originalTransition source.machine source.blank) (padFamily source)
    (NearLinearPrivateBit.outputSources source.machine source.inputTape)
    (fun _ => NearLinearPrivateBit.decoder source.machine source.blank source.outputTape source.bit) ExactTaskAlphabet.binaryAlphabet.readBit
    (4 * contextCoefficient source) 3
  intro N
  change (model source N).architecture.contextLength + 1 ≤ _
  have hc := context_bound source N
  have hlog : Nat.log 2 (N + 1) + 1 ≤ 2 * (N + 1) := by have h := Nat.log_le_self 2 (N + 1); omega
  have hs := Nat.mul_le_mul_left (contextCoefficient source * (N + 1)) (Nat.pow_le_pow_left hlog 2)
  nlinarith [show (N + 1) ^ 3 = (N + 1) * (N + 1) ^ 2 by ring]

theorem architecture_fixed (source : ExactMultiplication.Source) : ∃ heads precision : ℕ, ∀ N,
    (model source N).architecture.vocabulary = 4 ∧ (model source N).architecture.layers = 1 ∧
    (model source N).architecture.heads = heads ∧ (model source N).parameters.scalarBits = precision := by
  refine ⟨(model source 0).architecture.heads, (model source 0).parameters.scalarBits, ?_⟩
  intro N
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The aligned native bit/EOS upper construction needs only the expressly
permitted multiplication theorem; neither Tal nor PRG security is a premise. -/
theorem complete (imported : FastMultiplication.MultitapeNLogNTheorem) :
    ∃ source : ExactMultiplication.Source,
      (∀ N, 1 ≤ N → ∀ (input : Bits (N + N)) (output : Fin 2),
        (model source N).generatedToken (inputEncoding source N input)
          ⟨NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1 + output.val, by
            change NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 1 + output.val <
              NearLinearPrivateBit.payloadLength (times := source.times) source.machine source.inputTape N + 3
            have h := output.isLt; omega⟩ =
          ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryOutput (ExactTaskAlphabet.boolCode
            (if output = 0 then some (MultiplicationFootprint.middleBitTarget N input) else none)))) ∧
      (∀ N, (model source N).architecture.contextLength + 1 ≤ contextCoefficient source * (N + 1) * (Nat.log 2 (N + 1) + 1) ^ 2) ∧
      (∃ D P : ℕ, ∀ N, (model source N).architecture.hiddenWidth ≤ D * (N + 1) ^ 3 ∧
        (model source N).architecture.parameterCount ≤ P * (N + 1) ^ 6) ∧
      (∃ heads precision : ℕ, ∀ N, (model source N).architecture.vocabulary = 4 ∧
        (model source N).architecture.layers = 1 ∧ (model source N).architecture.heads = heads ∧
        (model source N).parameters.scalarBits = precision) := by
  obtain ⟨source, hcorrect⟩ := ExactMultiplication.source_exists imported
  refine ⟨source, ?_, context_bound source, polynomial_resources source, architecture_fixed source⟩
  intro N hN input output
  rw [generated_output, hcorrect N hN input]

end PlainMultiplication
