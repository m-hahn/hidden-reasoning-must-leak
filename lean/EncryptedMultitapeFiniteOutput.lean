import EncryptedFiniteReadout
import EncryptedMultitapeOutput
import DelimitedWord

/-!
# Native finite and first-EOS source output words

Output observations come from actual final multitape memory. Finite output
symbols, including EOS, are emitted by the encrypted numerical model itself.
First-EOS decoding covers empty and input-dependent-length output strings.
-/

noncomputable section
namespace EncryptedMultitapeFiniteOutput
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes extra seedLength locality : ℕ} {State Symbol Output : Type*}
variable [Fintype State] [Fintype Symbol] [Fintype Output] [Inhabited Output]

def outputCode : Output ≃ Fin (Fintype.card Output) := Fintype.equivFin _

def decode (machine : MultitapeTuring.Machine tapes State Symbol) (blank : Symbol)
    (outputTape : Fin tapes) (read : Symbol → Output) : Bits (vocabulary tapes State Symbol) → Fin (Fintype.card Output) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  fun word => outputCode (read ((ObliviousMatrix.controlOf (ObliviousMatrix.tokenCode.symm
    (RoutedMatrix.decodeIndicator ObliviousMatrix.vocabulary_positive word))).auxiliary.scanned outputTape))

def model (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (read : Symbol → Output)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality) :=
  EncryptedFiniteReadout.model (originalSchedule machine anchor blank level outputTape cells)
    (originalTransition machine blank) generator (sources machine anchor level) (fun _ => decode machine blank outputTape read)

def inputEncoding (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) :=
  EncryptedFiniteReadout.inputEncoding (outputCard := Fintype.card Output)
    (plainPrompt machine anchor blank level outputTape cells tape) seed

theorem generated_output (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (read : Symbol → Output)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality)
    (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) (output : Fin (extra + 1)) :
    (model machine anchor blank level outputTape cells read generator).generatedToken
      (inputEncoding (Output := Output) machine anchor blank level outputTape cells tape seed)
      ⟨eventCount machine anchor level extra * vocabulary tapes State Symbol + 1 + output.val, by
        change eventCount machine anchor level extra * vocabulary tapes State Symbol + 1 + output.val <
          eventCount machine anchor level extra * vocabulary tapes State Symbol + extra + 2
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (EncryptedFiniteReadout.result (outputCode
        (read ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells output))))) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  unfold model inputEncoding
  rw [EncryptedFiniteReadout.output_correct, block_plain]
  unfold decode
  rw [RoutedMatrix.decodeIndicator_indicator]
  simp only [ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply, ObliviousMatrix.controlOf,
    ObliviousProgram.Program.traceToken_control, MultitapeOutputMatrix.output_cell_correct]

def decodeToken : Fin (EncryptedMatrix.packetCount 2 + Fintype.card Output + 1) → Output :=
  Fin.lastCases default (Fin.addCases (fun _ => default) outputCode.symm)

@[simp] theorem decodeToken_result (symbol : Output) :
    decodeToken (ProtocolMatrix.dataToken (EncryptedFiniteReadout.result (outputCode symbol))) = symbol := by
  simp [decodeToken, ProtocolMatrix.dataToken, EncryptedFiniteReadout.result]

def emittedSymbols (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (read : Symbol → Output)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality)
    (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) : List Output :=
  List.ofFn (fun output : Fin (extra + 1) => decodeToken
    ((model machine anchor blank level outputTape cells read generator).generatedToken
      (inputEncoding (Output := Output) machine anchor blank level outputTape cells tape seed)
      ⟨eventCount machine anchor level extra * vocabulary tapes State Symbol + 1 + output.val, by
        change eventCount machine anchor level extra * vocabulary tapes State Symbol + 1 + output.val <
          eventCount machine anchor level extra * vocabulary tapes State Symbol + extra + 2
        have h := output.isLt; omega⟩))

theorem emittedSymbols_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (read : Symbol → Output)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * vocabulary tapes State Symbol + 1) locality)
    (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) :
    emittedSymbols machine anchor blank level outputTape cells read generator tape seed =
      List.ofFn (fun output : Fin (extra + 1) =>
        read ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells output))) := by
  simp only [emittedSymbols, generated_output, decodeToken_result]

theorem whole_word_correct {Alphabet : Type*} [Fintype Alphabet]
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (time : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (read : Symbol → Option Alphabet)
    (generator : LocalGenerator seedLength
      (eventCount machine anchor (horizonLevel (max 1 time)) extra * vocabulary tapes State Symbol + 1) locality)
    (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) (word : List Alphabet)
    (length_bound : word.length < extra + 1)
    (terminal : ∀ symbols, machine.transition
      (machine.run time (MultitapeEfficientPhase.sourceInitial machine tape)).state symbols =
      ((machine.run time (MultitapeEfficientPhase.sourceInitial machine tape)).state, symbols, fun _ => ObliviousPhase.Direction.stay))
    (source_correct : ∀ output : Fin (extra + 1),
      read ((machine.run time (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells output)) = word[output.val]?) :
    DelimitedWord.decode (emittedSymbols machine anchor blank (horizonLevel (max 1 time)) outputTape cells read generator tape seed) = word := by
  rw [emittedSymbols_correct]
  rw [machine.terminal_run_after _ time _
    ((Nat.le_max_right 1 time).trans (ObliviousPhase.horizon_covers (max 1 time))) terminal]
  simp_rw [source_correct]
  exact DelimitedWord.decode_getElem word (extra + 1) length_bound

def inputLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  EncryptedFiniteReadout.inputLiteral (BinaryMatrix.promptLiteral
    (EncryptedMultitapeOutput.finiteLiteral machine anchor blank bitSymbol inputTape n level outputTape cells))
    seedLength (Fintype.card Output)

theorem inputLiteral_correct {n : ℕ} (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (input : Bits n) (seed : Bits seedLength) (wire) :
    (inputLiteral (Output := Output) machine anchor blank bitSymbol inputTape n seedLength level outputTape cells wire).eval (Fin.append input seed) =
      inputEncoding (Output := Output) machine anchor blank level outputTape cells (bitTape blank bitSymbol inputTape input) seed wire := by
  apply EncryptedFiniteReadout.inputLiteral_correct
  intro wire
  exact BinaryMatrix.promptLiteral_correct _ input _
    (EncryptedMultitapeOutput.finiteLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cells input) wire

def inputCircuit (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  Circuit.bundle fun wire => (inputLiteral (Output := Output) machine anchor blank bitSymbol inputTape n seedLength level outputTape cells wire).circuit

theorem inputCircuit_correct {n : ℕ} (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (input : Bits n) (seed : Bits seedLength) :
    Circuit.eval (inputCircuit (Output := Output) machine anchor blank bitSymbol inputTape n seedLength level outputTape cells) (Fin.append input seed) =
      inputEncoding (Output := Output) machine anchor blank level outputTape cells (bitTape blank bitSymbol inputTape input) seed := by
  funext wire
  simp only [inputCircuit, Circuit.eval, Autoregressive.ContextLiteral.eval_circuit]
  exact inputLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cells input seed wire

theorem inputCircuit_depth (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :
    Circuit.depth (inputCircuit (Output := Output) machine anchor blank bitSymbol inputTape n seedLength level outputTape cells) ≤ 1 := by
  simp only [inputCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => Autoregressive.ContextLiteral.depth_circuit_le_one _

end EncryptedMultitapeFiniteOutput
