import PrivateOutput
import EncryptedMultitapeFiniteOutput

/-!
# Derived-budget private computation of whole first-EOS output strings

The machine premises are precisely ordinary source-time, terminal-state,
and source-output correctness statements. All Transformer construction,
encryption, seed capacity, and cryptographic reindexing are proved locally.
-/

noncomputable section
namespace PrivateWordOutput
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes : ℕ} {State Symbol Alphabet : Type*}
variable [Fintype State] [Fintype Symbol] [Fintype Alphabet]

section Family
variable {times extras : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (outputTape : Fin tapes) (cells : ∀ n, Fin (extras n + 1) → ℤ) (read : Symbol → Option Alphabet)
variable (coefficient outputCoefficient exponent : ℕ)
variable (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
variable (houtput : ∀ n, extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
variable (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
variable (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)

def model (n : ℕ) :=
  EncryptedMultitapeFiniteOutput.model machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n) read
    ((PrivateOutput.generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator).generator n)

def generatedWord (n : ℕ) (tape : Fin tapes → ℤ → Symbol)
    (seed : Bits (PrivateOutput.seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch n)) : List Alphabet :=
  DelimitedWord.decode (EncryptedMultitapeFiniteOutput.emittedSymbols machine anchor blank
    (horizonLevel (max 1 (times n))) outputTape (cells n) read
    ((PrivateOutput.generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator).generator n)
    tape seed)

/-- Empty strings and input-dependent output lengths are both included.
The public polynomial output capacity does not fix the answer's length. -/
theorem word_correct (n : ℕ) (tape : Fin tapes → ℤ → Symbol)
    (seed : Bits (PrivateOutput.seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch n)) (word : List Alphabet)
    (length_bound : word.length < extras n + 1)
    (terminal : ∀ symbols, machine.transition
      (machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine tape)).state symbols =
      ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine tape)).state, symbols, fun _ => Direction.stay))
    (source_correct : ∀ output : Fin (extras n + 1),
      read ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells n output)) = word[output.val]?) :
    generatedWord machine anchor blank outputTape cells read coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n tape seed = word :=
  EncryptedMultitapeFiniteOutput.whole_word_correct machine anchor blank (times n) outputTape (cells n) read _ tape seed word length_bound terminal source_correct

theorem context_bound (n : ℕ) :
    (model machine anchor blank outputTape cells read coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.contextLength + 1 ≤
      PrivateOutput.contextCoefficient tapes State Symbol coefficient outputCoefficient exponent stretch *
        (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) :=
  PrivateOutput.context_bound machine anchor blank outputTape cells (fun _ => false) coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n

def encodedTrace {codeWidth : ℕ}
    (encoding : Fin (EncryptedMatrix.packetCount 2 + Fintype.card (Option Alphabet) + 1) → Bits codeWidth)
    (n : ℕ) (tape : Fin tapes → ℤ → Symbol)
    (seed : Bits (PrivateOutput.seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch n)) :=
  EncryptedFiniteReadout.encodedTrace
    (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n))
    (originalTransition machine blank)
    ((PrivateOutput.generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator).generator n)
    (sources machine anchor (horizonLevel (max 1 (times n))))
    (fun _ => EncryptedMultitapeFiniteOutput.decode machine blank outputTape read) encoding
    (plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n) tape) seed

/-- Every polynomial monitor of every actual reasoning token and separator
has negligible advantage over the best constant guess, for every input
distribution and predicate. Plaintext answers are outside that prefix. -/
theorem no_readability {codeWidth : ℕ} (bitSymbol : Bool → Symbol) (inputTape : Fin tapes)
    (secure : generator.IsPseudorandom)
    (encoding : Fin (EncryptedMatrix.packetCount 2 + Fintype.card (Option Alphabet) + 1) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n =>
      (eventCount machine anchor (horizonLevel (max 1 (times n))) (extras n) * vocabulary tapes State Symbol + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => encodedTrace machine anchor blank outputTape cells read coefficient outputCoefficient exponent
          htime houtput hexponent stretch hstretch generator encoding n (bitTape blank bitSymbol inputTape input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n :=
  EncryptedFiniteReadout.no_readability_finite
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n))
    (originalTransition machine blank) (fun n => sources machine anchor (horizonLevel (max 1 (times n))))
    (fun _ _ => EncryptedMultitapeFiniteOutput.decode machine blank outputTape read)
    (fun n input => plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n) (bitTape blank bitSymbol inputTape input))
    (PrivateOutput.generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator)
    (PrivateOutput.generatorPrefix_secure machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator secure)
    encoding monitor (2 * PrivateOutput.payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent) (exponent + 1)
    (fun n => PrivateOutput.payload_polynomial_bound machine anchor (times n) (extras n) n coefficient outputCoefficient exponent (htime n) (houtput n))

theorem polynomial_resources :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (model machine anchor blank outputTape cells read coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ^ (exponent + 1) ∧
      (model machine anchor blank outputTape cells read coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ (2 * (exponent + 1)) := by
  apply EncryptedFiniteReadout.polynomial_resources
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n))
    (originalTransition machine blank)
    (PrivateOutput.generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator)
    (fun n => sources machine anchor (horizonLevel (max 1 (times n))))
    (fun _ _ => EncryptedMultitapeFiniteOutput.decode machine blank outputTape read)
    (2 * PrivateOutput.contextCoefficient tapes State Symbol coefficient outputCoefficient exponent stretch) (exponent + 1)
  intro n
  have hcontext := context_bound machine anchor blank outputTape cells read coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have h := Nat.log_le_self 2 (n + 1); omega
  have hscale := Nat.mul_le_mul_left
    (PrivateOutput.contextCoefficient tapes State Symbol coefficient outputCoefficient exponent stretch * (n + 1) ^ exponent) hlog
  change (model machine anchor blank outputTape cells read coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.contextLength + 1 ≤ _
  rw [pow_succ]
  nlinarith

end Family
end PrivateWordOutput
