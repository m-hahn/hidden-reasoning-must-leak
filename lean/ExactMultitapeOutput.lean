import ExactTaskAlphabet
import EncryptedMultitapeFiniteOutput

/-! # Native multitape outputs and raw initialization in a shared task alphabet -/

noncomputable section
namespace ExactMultitapeOutput
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes extra seedLength locality vocabulary : ℕ} {State Symbol Output : Type*}
variable [Fintype State] [Fintype Symbol] [Fintype Output] [Inhabited Output]

def model (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card Output))
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (read : Symbol → Output)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * MultitapeMatrix.vocabulary tapes State Symbol + 1) locality)
    (label : Fin vocabulary → Bool) :=
  ExactEncryptedAlphabet.model alphabet (originalSchedule machine anchor blank level outputTape cells)
    (originalTransition machine blank) generator (sources machine anchor level)
    (fun _ => EncryptedMultitapeFiniteOutput.decode machine blank outputTape read) label

def inputEncoding (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card Output))
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) :=
  ExactEncryptedAlphabet.inputEncoding alphabet (plainPrompt machine anchor blank level outputTape cells tape) seed

theorem generated_output (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card Output))
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (read : Symbol → Output)
    (generator : LocalGenerator seedLength (eventCount machine anchor level extra * MultitapeMatrix.vocabulary tapes State Symbol + 1) locality)
    (label : Fin vocabulary → Bool) (tape : Fin tapes → ℤ → Symbol) (seed : Bits seedLength) (output : Fin (extra + 1)) :
    (model alphabet machine anchor blank level outputTape cells read generator label).generatedToken
      (inputEncoding alphabet machine anchor blank level outputTape cells tape seed)
      ⟨eventCount machine anchor level extra * MultitapeMatrix.vocabulary tapes State Symbol + 1 + output.val, by
        change eventCount machine anchor level extra * MultitapeMatrix.vocabulary tapes State Symbol + 1 + output.val <
          eventCount machine anchor level extra * MultitapeMatrix.vocabulary tapes State Symbol + extra + 2
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (alphabet.output (EncryptedMultitapeFiniteOutput.outputCode
        (read ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells output))))) := by
  unfold model inputEncoding
  rw [ExactEncryptedAlphabet.generated_correct]
  change ExactEncryptedAlphabet.protocolErase alphabet
    ((EncryptedMultitapeFiniteOutput.model machine anchor blank level outputTape cells read generator).generatedToken
      (EncryptedMultitapeFiniteOutput.inputEncoding machine anchor blank level outputTape cells tape seed) _) = _
  rw [EncryptedMultitapeFiniteOutput.generated_output, ExactEncryptedAlphabet.protocolErase_data,
    ExactEncryptedAlphabet.erase_result]

def inputLiteral (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card Output))
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  ExactEncryptedAlphabet.inputLiteral alphabet (BinaryMatrix.promptLiteral
    (finiteLiteral machine anchor blank bitSymbol inputTape n level outputTape cells)) seedLength

theorem inputLiteral_correct {n : ℕ} (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card Output))
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (input : Bits n) (seed : Bits seedLength) (wire) :
    (inputLiteral alphabet machine anchor blank bitSymbol inputTape n seedLength level outputTape cells wire).eval (Fin.append input seed) =
      inputEncoding alphabet machine anchor blank level outputTape cells (bitTape blank bitSymbol inputTape input) seed wire := by
  apply ExactEncryptedAlphabet.inputLiteral_correct
  intro wire
  exact BinaryMatrix.promptLiteral_correct _ input _
    (finiteLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cells input) wire

def inputCircuit (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card Output))
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  Circuit.bundle fun wire => (inputLiteral alphabet machine anchor blank bitSymbol inputTape n seedLength level outputTape cells wire).circuit

theorem inputCircuit_correct {n : ℕ} (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card Output))
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (input : Bits n) (seed : Bits seedLength) :
    Circuit.eval (inputCircuit alphabet machine anchor blank bitSymbol inputTape n seedLength level outputTape cells) (Fin.append input seed) =
      inputEncoding alphabet machine anchor blank level outputTape cells (bitTape blank bitSymbol inputTape input) seed := by
  funext wire
  simp only [inputCircuit, Circuit.eval, Autoregressive.ContextLiteral.eval_circuit]
  exact inputLiteral_correct alphabet machine anchor blank bitSymbol inputTape level outputTape cells input seed wire

theorem inputCircuit_depth (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card Output))
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :
    Circuit.depth (inputCircuit alphabet machine anchor blank bitSymbol inputTape n seedLength level outputTape cells) ≤ 1 := by
  simp only [inputCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => Autoregressive.ContextLiteral.depth_circuit_le_one _

end ExactMultitapeOutput
