import ExactMultitapeOutput
import PolynomialWordOutput

/-! # Whole polynomial-time binary words in exactly {0,1,EOS,SEP}

The output budget follows from unit-motion source time.  Neither the answer,
its length, a simulation certificate, nor a security certificate is prompt
data.  Only raw input bits and raw seed bits are supplied.
-/
noncomputable section
namespace ExactBinaryWord
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
section Family
variable {times : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (read : Symbol → Option Bool)
variable (coefficient exponent : ℕ) (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
variable (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
variable (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)

def model (n : ℕ) :=
  ExactMultitapeOutput.model ExactTaskAlphabet.binaryAlphabet machine anchor blank (horizonLevel (max 1 (times n))) outputTape
    (PolynomialWordOutput.cells times n) read
    ((PrivateOutput.generatorPrefix machine anchor coefficient (coefficient + 1) exponent htime
      (PolynomialWordOutput.capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator).generator n)
    ExactTaskAlphabet.binaryAlphabet.readBit

def inputEncoding (n : ℕ) (input : Bits n)
    (seed : Bits (PolynomialWordOutput.seedLengths (tapes := tapes) (State := State) (Symbol := Symbol) coefficient exponent stretch n)) :=
  ExactMultitapeOutput.inputEncoding ExactTaskAlphabet.binaryAlphabet machine anchor blank (horizonLevel (max 1 (times n))) outputTape
    (PolynomialWordOutput.cells times n) (bitTape blank bitSymbol inputTape input) seed

def generatedWord (n : ℕ) (input : Bits n)
    (seed : Bits (PolynomialWordOutput.seedLengths (tapes := tapes) (State := State) (Symbol := Symbol) coefficient exponent stretch n)) : List Bool :=
  DelimitedWord.decode (List.ofFn (fun output : Fin (PolynomialWordOutput.extras times n + 1) =>
    ExactTaskAlphabet.decodeBinaryToken ((model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).generatedToken
      (inputEncoding machine anchor blank bitSymbol inputTape outputTape coefficient exponent stretch n input seed)
      ⟨eventCount machine anchor (horizonLevel (max 1 (times n))) (PolynomialWordOutput.extras times n) * MultitapeMatrix.vocabulary tapes State Symbol + 1 + output.val, by
        change eventCount machine anchor (horizonLevel (max 1 (times n))) (PolynomialWordOutput.extras times n) * MultitapeMatrix.vocabulary tapes State Symbol + 1 + output.val <
          eventCount machine anchor (horizonLevel (max 1 (times n))) (PolynomialWordOutput.extras times n) * MultitapeMatrix.vocabulary tapes State Symbol + PolynomialWordOutput.extras times n + 2
        have h := output.isLt; omega⟩)))

theorem generatedWord_eq (n : ℕ) (input : Bits n)
    (seed : Bits (PolynomialWordOutput.seedLengths (tapes := tapes) (State := State) (Symbol := Symbol) coefficient exponent stretch n)) :
    generatedWord machine anchor blank bitSymbol inputTape outputTape read coefficient exponent htime hexponent stretch hstretch generator n input seed =
      PolynomialWordOutput.generatedWord machine anchor blank bitSymbol inputTape outputTape read coefficient exponent htime hexponent stretch hstretch generator n input seed := by
  unfold generatedWord model inputEncoding PolynomialWordOutput.generatedWord PrivateWordOutput.generatedWord
  simp only [ExactMultitapeOutput.generated_output, EncryptedMultitapeFiniteOutput.emittedSymbols_correct]
  congr 2
  funext output
  exact ExactTaskAlphabet.decodeBinaryToken_output _

theorem word_correct (n : ℕ) (input : Bits n)
    (seed : Bits (PolynomialWordOutput.seedLengths (tapes := tapes) (State := State) (Symbol := Symbol) coefficient exponent stretch n))
    (word : List Bool) (blank_eos : read blank = none)
    (terminal : ∀ symbols, machine.transition
      (machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state symbols =
      ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state, symbols, fun _ => Direction.stay))
    (source_correct : ∀ position : ℕ,
      read ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine
        (bitTape blank bitSymbol inputTape input))).tape outputTape (position : ℤ)) = word[position]?) :
    generatedWord machine anchor blank bitSymbol inputTape outputTape read coefficient exponent htime hexponent stretch hstretch generator n input seed = word := by
  rw [generatedWord_eq]
  exact PolynomialWordOutput.word_correct machine anchor blank bitSymbol inputTape outputTape read coefficient exponent htime hexponent
    stretch hstretch generator n input seed word blank_eos terminal source_correct

/-- An ordinary polynomial-time machine computing a total binary-string
function is compiled to a native first-EOS Transformer computing that whole
function. Output length is derived from source time, not a premise. -/
theorem whole_function_correct (function : ∀ n, Bits n → List Bool) (blank_eos : read blank = none)
    (terminal : ∀ n (input : Bits n) symbols, machine.transition
      (machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state symbols =
      ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state, symbols, fun _ => Direction.stay))
    (source_correct : ∀ n (input : Bits n) (position : ℕ),
      read ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine
        (bitTape blank bitSymbol inputTape input))).tape outputTape (position : ℤ)) = (function n input)[position]?) :
    ∀ n (input : Bits n)
      (seed : Bits (PolynomialWordOutput.seedLengths (tapes := tapes) (State := State) (Symbol := Symbol) coefficient exponent stretch n)),
      generatedWord machine anchor blank bitSymbol inputTape outputTape read coefficient exponent htime hexponent stretch hstretch generator n input seed = function n input := by
  intro n input seed
  exact word_correct machine anchor blank bitSymbol inputTape outputTape read coefficient exponent htime hexponent stretch hstretch generator
    n input seed (function n input) blank_eos (terminal n input) (source_correct n input)

theorem architecture_fixed : ∃ heads precision : ℕ, ∀ n,
    (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.vocabulary = 4 ∧
    (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.layers = 1 ∧
    (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.heads = heads ∧
    (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).parameters.scalarBits = precision := by
  refine ⟨(model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator 0).architecture.heads,
    (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator 0).parameters.scalarBits, ?_⟩
  intro n
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem context_bound (n : ℕ) :
    (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.contextLength + 1 ≤
      PrivateOutput.contextCoefficient tapes State Symbol coefficient (coefficient + 1) exponent stretch *
        (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) :=
  PolynomialWordOutput.context_bound machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n

theorem polynomial_resources :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ^ (exponent + 1) ∧
      (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ (2 * (exponent + 1)) := by
  apply ExactEncryptedAlphabet.polynomial_resources ExactTaskAlphabet.binaryAlphabet
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (PolynomialWordOutput.cells times n))
    (originalTransition machine blank)
    (PrivateOutput.generatorPrefix machine anchor coefficient (coefficient + 1) exponent htime
      (PolynomialWordOutput.capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator)
    (fun n => sources machine anchor (horizonLevel (max 1 (times n))))
    (fun _ _ => EncryptedMultitapeFiniteOutput.decode machine blank outputTape read) ExactTaskAlphabet.binaryAlphabet.readBit
    (2 * PrivateOutput.contextCoefficient tapes State Symbol coefficient (coefficient + 1) exponent stretch) (exponent + 1)
  intro n
  change (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.contextLength + 1 ≤ _
  have hc := context_bound machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have h := Nat.log_le_self 2 (n + 1); omega
  have hs := Nat.mul_le_mul_left (PrivateOutput.contextCoefficient tapes State Symbol coefficient (coefficient + 1) exponent stretch * (n + 1) ^ exponent) hlog
  rw [pow_succ]
  nlinarith

theorem no_readability {codeWidth : ℕ} (secure : generator.IsPseudorandom)
    (encoding : Fin 4 → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n =>
      (eventCount machine anchor (horizonLevel (max 1 (times n))) (PolynomialWordOutput.extras times n) * MultitapeMatrix.vocabulary tapes State Symbol + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => ExactEncryptedAlphabet.encodedTrace ExactTaskAlphabet.binaryAlphabet
          (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (PolynomialWordOutput.cells times n))
          (originalTransition machine blank)
          ((PrivateOutput.generatorPrefix machine anchor coefficient (coefficient + 1) exponent htime
            (PolynomialWordOutput.capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator).generator n)
          (sources machine anchor (horizonLevel (max 1 (times n))))
          (fun _ => EncryptedMultitapeFiniteOutput.decode machine blank outputTape read) ExactTaskAlphabet.binaryAlphabet.readBit encoding
          (plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (PolynomialWordOutput.cells times n)
            (bitTape blank bitSymbol inputTape input)) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  simpa only [ExactEncryptedAlphabet.encodedTrace_eq_original, PrivateWordOutput.encodedTrace] using
    PolynomialWordOutput.no_readability machine anchor blank bitSymbol inputTape outputTape read coefficient exponent htime hexponent stretch hstretch generator secure
      (fun token => encoding (ExactEncryptedAlphabet.protocolErase ExactTaskAlphabet.binaryAlphabet token)) monitor

end Family
end ExactBinaryWord
