import ExactMultitapeOutput
import PolynomialWordOutput

/-! # Unconditional whole-word multitape simulation in four tokens

The explicit zero pad has no seed and no security premise. It specializes
the checked local constructor to ordinary, unencrypted reasoning. Source
time derives the output capacity, including a native first EOS.
-/
noncomputable section
namespace PlainBinaryWord
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]

def zeroPad (outputs : ℕ) : LocalGenerator 0 outputs 0 where
  generate _ _ := false
  dependency _ index := Fin.elim0 index
  locality_correct _ _ _ _ := rfl

section Family
variable {times : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (read : Symbol → Option Bool)

def payloadLength (n : ℕ) :=
  eventCount machine anchor (horizonLevel (max 1 (times n))) (PolynomialWordOutput.extras times n) * vocabulary tapes State Symbol

def padFamily : NC0GeneratorFamily (fun _ => 0) (fun n => payloadLength (times := times) machine anchor n + 1) where
  locality := 0
  generator n := zeroPad _

def model (n : ℕ) :=
  ExactMultitapeOutput.model ExactTaskAlphabet.binaryAlphabet machine anchor blank (horizonLevel (max 1 (times n))) outputTape
    (PolynomialWordOutput.cells times n) read (zeroPad (payloadLength (times := times) machine anchor n + 1))
    ExactTaskAlphabet.binaryAlphabet.readBit

def inputEncoding (n : ℕ) (input : Bits n) :=
  ExactMultitapeOutput.inputEncoding ExactTaskAlphabet.binaryAlphabet machine anchor blank (horizonLevel (max 1 (times n))) outputTape
    (PolynomialWordOutput.cells times n) (bitTape blank bitSymbol inputTape input) (fun index : Fin 0 => Fin.elim0 index)

def generatedWord (n : ℕ) (input : Bits n) : List Bool :=
  DelimitedWord.decode (List.ofFn (fun output : Fin (PolynomialWordOutput.extras times n + 1) =>
    ExactTaskAlphabet.decodeBinaryToken ((model (times := times) machine anchor blank outputTape read n).generatedToken
      (inputEncoding (times := times) machine anchor blank bitSymbol inputTape outputTape n input)
      ⟨payloadLength (times := times) machine anchor n + 1 + output.val, by
        change payloadLength (times := times) machine anchor n + 1 + output.val <
          payloadLength (times := times) machine anchor n + PolynomialWordOutput.extras times n + 2
        have h := output.isLt; omega⟩)))

theorem word_correct (n : ℕ) (input : Bits n) (word : List Bool) (blank_eos : read blank = none)
    (terminal : ∀ symbols, machine.transition
      (machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state symbols =
      ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state, symbols, fun _ => Direction.stay))
    (source_correct : ∀ position : ℕ,
      read ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine
        (bitTape blank bitSymbol inputTape input))).tape outputTape (position : ℤ)) = word[position]?) :
    generatedWord (times := times) machine anchor blank bitSymbol inputTape outputTape read n input = word := by
  unfold generatedWord model inputEncoding payloadLength
  simp only [ExactMultitapeOutput.generated_output, ExactTaskAlphabet.decodeBinaryToken_output]
  rw [machine.terminal_run_after _ (times n) _
    ((Nat.le_max_right 1 (times n)).trans (horizon_covers (max 1 (times n)))) terminal]
  simp only [PolynomialWordOutput.cells, source_correct]
  change DelimitedWord.decode (List.ofFn (fun output : Fin (PolynomialWordOutput.extras times n + 1) =>
    ExactTaskAlphabet.decodeBinaryToken (ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryOutput (ExactTaskAlphabet.boolCode word[output.val]?))))) = word
  simp only [ExactTaskAlphabet.decodeBinaryToken_output]
  apply DelimitedWord.decode_getElem
  have h := MultitapeOutputCapacity.word_length machine blank bitSymbol inputTape outputTape input (times n) read blank_eos word source_correct
  unfold PolynomialWordOutput.extras
  omega

theorem whole_function_correct (function : ∀ n, Bits n → List Bool) (blank_eos : read blank = none)
    (terminal : ∀ n (input : Bits n) symbols, machine.transition
      (machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state symbols =
      ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state, symbols, fun _ => Direction.stay))
    (source_correct : ∀ n (input : Bits n) (position : ℕ),
      read ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine
        (bitTape blank bitSymbol inputTape input))).tape outputTape (position : ℤ)) = (function n input)[position]?) :
    ∀ n (input : Bits n), generatedWord (times := times) machine anchor blank bitSymbol inputTape outputTape read n input = function n input := by
  intro n input
  exact word_correct machine anchor blank bitSymbol inputTape outputTape read n input (function n input) blank_eos (terminal n input) (source_correct n input)

theorem architecture_fixed : ∃ heads precision : ℕ, ∀ n,
    (model (times := times) machine anchor blank outputTape read n).architecture.vocabulary = 4 ∧
    (model (times := times) machine anchor blank outputTape read n).architecture.layers = 1 ∧
    (model (times := times) machine anchor blank outputTape read n).architecture.heads = heads ∧
    (model (times := times) machine anchor blank outputTape read n).parameters.scalarBits = precision := by
  refine ⟨(model (times := times) machine anchor blank outputTape read 0).architecture.heads,
    (model (times := times) machine anchor blank outputTape read 0).parameters.scalarBits, ?_⟩
  intro n
  exact ⟨rfl, rfl, rfl, rfl⟩

def contextCoefficient (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] (coefficient exponent : ℕ) :=
  2 * PrivateOutput.payloadCoefficient tapes State Symbol coefficient (coefficient + 1) exponent +
    2 * vocabulary tapes State Symbol + coefficient + 3

theorem context_bound (coefficient exponent : ℕ) (hexponent : 1 ≤ exponent)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) (n : ℕ) :
    (model (times := times) machine anchor blank outputTape read n).architecture.contextLength + 1 ≤
      contextCoefficient tapes State Symbol coefficient exponent * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
  have hp := PrivateOutput.payload_bound machine anchor (times n) (PolynomialWordOutput.extras times n) n coefficient (coefficient + 1) exponent
    (htime n) (PolynomialWordOutput.capacityBounds times coefficient exponent htime hexponent n)
  have hout := PolynomialWordOutput.capacityBounds times coefficient exponent htime hexponent n
  have hout' : PolynomialWordOutput.extras times n + 1 ≤
      (coefficient + 1) * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by nlinarith
  have hone : 1 ≤ (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
    have hpow := Nat.one_le_pow exponent (n + 1) (by omega)
    nlinarith
  rw [model, ExactMultitapeOutput.model, ExactEncryptedAlphabet.context_length]
  simp only [Nat.zero_add]
  change (eventCount machine anchor (horizonLevel (max 1 (times n))) (PolynomialWordOutput.extras times n) + 2) *
    vocabulary tapes State Symbol + payloadLength (times := times) machine anchor n + PolynomialWordOutput.extras times n + 2 ≤ _
  unfold contextCoefficient payloadLength
  nlinarith

theorem polynomial_resources (coefficient exponent : ℕ) (hexponent : 1 ≤ exponent)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ D P : ℕ, ∀ n,
      (model (times := times) machine anchor blank outputTape read n).architecture.hiddenWidth ≤ D * (n + 1) ^ (exponent + 1) ∧
      (model (times := times) machine anchor blank outputTape read n).architecture.parameterCount ≤ P * (n + 1) ^ (2 * (exponent + 1)) := by
  apply ExactEncryptedAlphabet.polynomial_resources ExactTaskAlphabet.binaryAlphabet
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (PolynomialWordOutput.cells times n))
    (originalTransition machine blank) (padFamily (times := times) machine anchor)
    (fun n => sources machine anchor (horizonLevel (max 1 (times n))))
    (fun _ _ => EncryptedMultitapeFiniteOutput.decode machine blank outputTape read) ExactTaskAlphabet.binaryAlphabet.readBit
    (2 * contextCoefficient tapes State Symbol coefficient exponent) (exponent + 1)
  intro n
  change (model (times := times) machine anchor blank outputTape read n).architecture.contextLength + 1 ≤ _
  have hc := context_bound machine anchor blank outputTape read coefficient exponent hexponent htime n
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have h := Nat.log_le_self 2 (n + 1); omega
  have hs := Nat.mul_le_mul_left (contextCoefficient tapes State Symbol coefficient exponent * (n + 1) ^ exponent) hlog
  rw [pow_succ]
  nlinarith

end Family
end PlainBinaryWord
