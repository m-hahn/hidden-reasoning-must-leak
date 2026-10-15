import EncryptedReadout
import MultitapeOutputMatrix

/-!
# Efficient multitape computation with encrypted reasoning and all output bits

The reasoning prefix includes the actual source computation and its read-only
output-cell observations, encoded and encrypted bit by bit during generation.
After its own separator, the same matrices decrypt these observed blocks and
emit exactly the plaintext output bits. No output word is a prompt input.
-/

noncomputable section
namespace EncryptedMultitapeOutput
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
variable {extra n seedLength locality : ℕ}

def eventCount (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (level extra : ℕ) :=
  eventSteps machine anchor level + extra + 1

def originalSchedule (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  BinarySchedule.schedule (EncryptedObliviousMatrix.schedule
    (MultitapeOutputMatrix.program machine anchor blank level outputTape cells) (eventCount machine anchor level extra))
    (ObliviousMatrix.vocabulary_positive (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol))

def originalTransition (machine : MultitapeTuring.Machine tapes State Symbol) (blank : Symbol) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  BinarySchedule.transition (ObliviousMatrix.vocabulary_positive
      (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol))
    (ObliviousMatrix.transition (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol)) (fun _ => false)

def plainPrompt (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (tape : Fin tapes → ℤ → Symbol) :=
  BinarySchedule.prompt (ObliviousMatrix.prompt (MultitapeOutputMatrix.program machine anchor blank level outputTape cells)
    (eventCount machine anchor level extra) tape)

def sources (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (level : ℕ) :
    Fin (extra + 1) → Fin (vocabulary tapes State Symbol) → Fin (eventCount machine anchor level extra * vocabulary tapes State Symbol) :=
  fun output bit => finProdFinEquiv (⟨eventSteps machine anchor level + output.val,
    by have ho := output.isLt; unfold eventCount; omega⟩, bit)

def decode (machine : MultitapeTuring.Machine tapes State Symbol) (blank : Symbol) (outputTape : Fin tapes) (bit : Symbol → Bool) :
    Bits (vocabulary tapes State Symbol) → Bool :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  fun word => ObliviousMatrix.label (Symbol := SimulatorSymbol Symbol)
    (fun control : SimulatorControl tapes State Symbol => bit (control.auxiliary.scanned outputTape))
    (RoutedMatrix.decodeIndicator ObliviousMatrix.vocabulary_positive word)

def model (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (bit : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality) :=
  EncryptedReadout.model (originalSchedule machine anchor blank level outputTape cells) (originalTransition machine blank)
    generator (sources machine anchor level) (decode machine blank outputTape bit)

def inputEncoding (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) :=
  ProtocolEncryptedBinary.inputEncoding (plainPrompt machine anchor blank level outputTape cells tape) seed

theorem block_plain (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (tape : Fin tapes → ℤ → Symbol) (output : Fin (extra + 1)) :
    (fun codeBit => EncryptedBinaryMatrix.plainTranscript (originalSchedule machine anchor blank level outputTape cells)
      (originalTransition machine blank) (plainPrompt machine anchor blank level outputTape cells tape)
      (sources machine anchor level output codeBit)) =
      RoutedMatrix.indicator (ObliviousMatrix.traceEncoding
        ((MultitapeOutputMatrix.program machine anchor blank level outputTape cells).traceToken tape
          (eventSteps machine anchor level + output.val))) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  funext codeBit
  unfold EncryptedBinaryMatrix.plainTranscript originalSchedule originalTransition plainPrompt
  rw [BinarySchedule.token_correct]
  have hnot : (sources machine anchor level output codeBit).castSucc.val ≠ eventCount machine anchor level extra *
      ObliviousMatrix.vocabulary (SimulatorControl tapes State Symbol) (SimulatorSymbol Symbol) :=
    Nat.ne_of_lt (sources machine anchor level output codeBit).isLt
  simp only [BinarySchedule.target, hnot, ↓reduceIte, BinarySchedule.tokenBit_bitToken]
  have hevent : BinarySchedule.eventTime (ObliviousMatrix.vocabulary_positive
      (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol))
      (sources machine anchor level output codeBit).castSucc =
      ⟨eventSteps machine anchor level + output.val, by have h := output.isLt; unfold eventCount; omega⟩ := by
    apply Fin.ext
    change (codeBit.val + vocabulary tapes State Symbol * (eventSteps machine anchor level + output.val)) /
      vocabulary tapes State Symbol = eventSteps machine anchor level + output.val
    simpa only [Nat.mul_comm, Nat.add_comm] using
      BinarySchedule.quotient_block ObliviousMatrix.vocabulary_positive (eventSteps machine anchor level + output.val) codeBit
  have hbit : BinarySchedule.codeBit (ObliviousMatrix.vocabulary_positive
      (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol))
      (sources machine anchor level output codeBit).castSucc = codeBit := by
    apply Fin.ext
    change (codeBit.val + vocabulary tapes State Symbol * (eventSteps machine anchor level + output.val)) %
      vocabulary tapes State Symbol = codeBit.val
    simpa only [Nat.mul_comm, Nat.add_comm] using BinarySchedule.remainder_block (eventSteps machine anchor level + output.val) codeBit
  rw [hevent, hbit, EncryptedObliviousMatrix.token_correct]

theorem generated_output (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (bit : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality)
    (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) (output : Fin (extra + 1)) :
    (model machine anchor blank level outputTape cells bit generator).generatedToken
      (inputEncoding machine anchor blank level outputTape cells tape seed)
      ⟨eventCount machine anchor level extra * vocabulary tapes State Symbol + 1 + output.val, by
        change eventCount machine anchor level extra * vocabulary tapes State Symbol + 1 + output.val <
          eventCount machine anchor level extra * vocabulary tapes State Symbol + extra + 2
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (EncryptedMatrix.answerPacket 2
        (bit ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells output)))) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  unfold model inputEncoding
  rw [EncryptedReadout.output_correct, block_plain]
  unfold decode
  rw [RoutedMatrix.decodeIndicator_indicator]
  simp only [ObliviousMatrix.label, ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply,
    ObliviousMatrix.controlOf, ObliviousProgram.Program.traceToken_control, MultitapeOutputMatrix.output_cell_correct]

def finiteLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :
    Fin ((eventCount machine anchor level extra + 2) * vocabulary tapes State Symbol) → Autoregressive.ContextLiteral n := fun wire =>
  let pair := finProdFinEquiv.symm wire
  Fin.cases (.constant (decide (pair.2 = ObliviousMatrix.tokenCode (.inl (MultitapeEfficientPhase.initialControl machine blank)))))
    (fun time => MultitapeMatrix.tapeLiteral blank bitSymbol inputTape n
      ((MultitapeOutputMatrix.program machine anchor blank level outputTape cells).position time.val)
      (fun value => decide (pair.2 = ObliviousMatrix.tokenCode (.inr (.inl value))))) pair.1

theorem finiteLiteral_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ)
    (input : Bits n) (wire : Fin ((eventCount machine anchor level extra + 2) * vocabulary tapes State Symbol)) :
    (finiteLiteral machine anchor blank bitSymbol inputTape n level outputTape cells wire).eval input =
      RoutedMatrix.promptInput (ObliviousMatrix.prompt (MultitapeOutputMatrix.program machine anchor blank level outputTape cells)
        (eventCount machine anchor level extra) (bitTape blank bitSymbol inputTape input)) wire := by
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [finiteLiteral, RoutedMatrix.promptInput, ObliviousMatrix.front, vocabulary, Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun time => ?_) position
  · simp only [ObliviousMatrix.prompt, ObliviousMatrix.front, vocabulary, Equiv.symm_apply_apply, Fin.cases_zero, Autoregressive.ContextLiteral.eval]
    rfl
  · simp only [Fin.cases_succ, MultitapeMatrix.tapeLiteral_correct, ObliviousMatrix.prompt, ObliviousMatrix.front, vocabulary, Equiv.symm_apply_apply]
    rfl

def inputLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  ProtocolEncryptedBinary.inputLiteral (BinaryMatrix.promptLiteral
    (finiteLiteral machine anchor blank bitSymbol inputTape n level outputTape cells)) seedLength

theorem inputLiteral_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ)
    (input : Bits n) (seed : Bits seedLength) (wire) :
    (inputLiteral machine anchor blank bitSymbol inputTape n seedLength level outputTape cells wire).eval (Fin.append input seed) =
      inputEncoding machine anchor blank level outputTape cells (bitTape blank bitSymbol inputTape input) seed wire := by
  apply ProtocolEncryptedBinary.inputLiteral_correct
  intro wire
  exact BinaryMatrix.promptLiteral_correct _ input _
    (finiteLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cells input) wire

theorem one_layer (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (bit : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank level outputTape cells bit generator).architecture.layers = 1 := rfl

theorem heads_fixed (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (bit : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank level outputTape cells bit generator).architecture.heads =
      EncryptedMatrix.headCount 2 (2 * vocabulary tapes State Symbol) locality + EncryptedReadout.readHeads (vocabulary tapes State Symbol) locality := rfl

theorem context_length (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (bit : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank level outputTape cells bit generator).architecture.contextLength =
      seedLength + 2 * eventCount machine anchor level extra * vocabulary tapes State Symbol + 2 * vocabulary tapes State Symbol + extra + 1 := by
  change seedLength + (eventCount machine anchor level extra + 2) * vocabulary tapes State Symbol +
    (eventCount machine anchor level extra * vocabulary tapes State Symbol + extra + 1) = _
  ring

def outputHeads (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] (locality : ℕ) :=
  EncryptedMatrix.headCount 2 (2 * vocabulary tapes State Symbol) locality +
    EncryptedReadout.readHeads (vocabulary tapes State Symbol) locality

def outputOpcodes (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] (locality : ℕ) :=
  EncryptedMatrix.opcodeCount 2 (2 * vocabulary tapes State Symbol)
    (MultitapeMatrix.opcodes tapes State Symbol * (vocabulary tapes State Symbol + 1)) locality +
    EncryptedReadout.readOpcodes (vocabulary tapes State Symbol) locality + 1

theorem precision_fixed (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (bit : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank level outputTape cells bit generator).parameters.scalarBits =
      RoutedMatrix.precision (EncryptedMatrix.packetCount 2 + 1)
        (outputHeads tapes State Symbol locality) (outputOpcodes tapes State Symbol locality) := rfl

theorem dimension_linear (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (bit : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank level outputTape cells bit generator).architecture.hiddenWidth ≤
      2 * RoutedMatrix.dimensionConstant (EncryptedMatrix.packetCount 2 + 1)
        (outputHeads tapes State Symbol locality) (outputOpcodes tapes State Symbol locality) *
      ((model machine anchor blank level outputTape cells bit generator).architecture.contextLength + 1) :=
  RoutedMatrix.hidden_dimension_linear

theorem parameters_quadratic (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (bit : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank level outputTape cells bit generator).architecture.parameterCount ≤
      (3 * (EncryptedMatrix.packetCount 2 + 1) * RoutedMatrix.dimensionConstant (EncryptedMatrix.packetCount 2 + 1)
        (outputHeads tapes State Symbol locality) (outputOpcodes tapes State Symbol locality) +
      4 * (3 * outputHeads tapes State Symbol locality + 2) *
        RoutedMatrix.dimensionConstant (EncryptedMatrix.packetCount 2 + 1)
          (outputHeads tapes State Symbol locality) (outputOpcodes tapes State Symbol locality) ^ 2) *
      ((model machine anchor blank level outputTape cells bit generator).architecture.contextLength + 1) ^ 2 :=
  RoutedMatrix.parameter_count_quadratic

def inputCircuit (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  Circuit.bundle fun wire => (inputLiteral machine anchor blank bitSymbol inputTape n seedLength level outputTape cells wire).circuit

theorem inputCircuit_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ)
    (input : Bits n) (seed : Bits seedLength) :
    Circuit.eval (inputCircuit machine anchor blank bitSymbol inputTape n seedLength level outputTape cells) (Fin.append input seed) =
      inputEncoding machine anchor blank level outputTape cells (bitTape blank bitSymbol inputTape input) seed := by
  funext wire
  simp only [inputCircuit, Circuit.eval, Autoregressive.ContextLiteral.eval_circuit]
  exact inputLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cells input seed wire

theorem inputCircuit_depth (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :
    Circuit.depth (inputCircuit machine anchor blank bitSymbol inputTape n seedLength level outputTape cells) ≤ 1 := by
  simp only [inputCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => Autoregressive.ContextLiteral.depth_circuit_le_one _

end EncryptedMultitapeOutput
