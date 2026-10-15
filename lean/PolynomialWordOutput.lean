import PrivateWordOutput
import MultitapeOutputCapacity

/-!
# Whole polynomial-time outputs with a derived, not assumed, output budget

The source is an ordinary unit-motion multitape machine, initialized from
raw input bits. Its EOS/word representation and terminal state express that
it computes the requested function. The public output capacity is derived
from source time; no separate output-length or simulation certificate is
an assumption.
-/

noncomputable section
namespace PolynomialWordOutput
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix
variable {tapes : ℕ} {State Symbol Alphabet : Type*}
variable [Fintype State] [Fintype Symbol] [Fintype Alphabet]

def extras (times : ℕ → ℕ) (n : ℕ) := n + times n
def cells (times : ℕ → ℕ) (n : ℕ) (output : Fin (extras times n + 1)) : ℤ := output.val

def capacityBounds (times : ℕ → ℕ) (coefficient exponent : ℕ)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) (hexponent : 1 ≤ exponent) :
    ∀ n, extras times n + 1 ≤ (coefficient + 1) * (n + 1) ^ exponent :=
  fun n => MultitapeOutputCapacity.capacity_polynomial (times n) n coefficient exponent hexponent (htime n)

section Family
variable {times : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (read : Symbol → Option Alphabet)
variable (coefficient exponent : ℕ) (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
variable (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
variable (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)

def model (n : ℕ) :=
  PrivateWordOutput.model machine anchor blank outputTape (cells times) read coefficient (coefficient + 1) exponent
    htime (capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator n

def seedLengths := PrivateOutput.seedLengths tapes State Symbol coefficient (coefficient + 1) exponent stretch

def generatedWord (n : ℕ) (input : Bits n) (seed : Bits (seedLengths (tapes := tapes) (State := State) (Symbol := Symbol) coefficient exponent stretch n)) :=
  PrivateWordOutput.generatedWord machine anchor blank outputTape (cells times) read coefficient (coefficient + 1) exponent
    htime (capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator n
    (bitTape blank bitSymbol inputTape input) seed

theorem word_correct (n : ℕ) (input : Bits n)
    (seed : Bits (seedLengths (tapes := tapes) (State := State) (Symbol := Symbol) coefficient exponent stretch n))
    (word : List Alphabet) (blank_eos : read blank = none)
    (terminal : ∀ symbols, machine.transition
      (machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state symbols =
      ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state,
        symbols, fun _ => Direction.stay))
    (source_correct : ∀ position : ℕ,
      read ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine
        (bitTape blank bitSymbol inputTape input))).tape outputTape (position : ℤ)) = word[position]?) :
    generatedWord machine anchor blank bitSymbol inputTape outputTape read coefficient exponent htime hexponent stretch hstretch generator n input seed = word := by
  apply PrivateWordOutput.word_correct
  · have hlength := MultitapeOutputCapacity.word_length machine blank bitSymbol inputTape outputTape input (times n) read blank_eos word source_correct
    change word.length < n + times n + 1
    omega
  · exact terminal
  · intro output
    exact source_correct output.val

theorem context_bound (n : ℕ) :
    (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.contextLength + 1 ≤
      PrivateOutput.contextCoefficient tapes State Symbol coefficient (coefficient + 1) exponent stretch *
        (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) :=
  PrivateWordOutput.context_bound machine anchor blank outputTape (cells times) read coefficient (coefficient + 1) exponent
    htime (capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator n

theorem polynomial_resources :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ^ (exponent + 1) ∧
      (model machine anchor blank outputTape read coefficient exponent htime hexponent stretch hstretch generator n).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ (2 * (exponent + 1)) :=
  PrivateWordOutput.polynomial_resources machine anchor blank outputTape (cells times) read coefficient (coefficient + 1) exponent
    htime (capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator

theorem no_readability {codeWidth : ℕ} (secure : generator.IsPseudorandom)
    (encoding : Fin (EncryptedMatrix.packetCount 2 + Fintype.card (Option Alphabet) + 1) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n =>
      (EncryptedMultitapeOutput.eventCount machine anchor (horizonLevel (max 1 (times n))) (extras times n) * vocabulary tapes State Symbol + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => PrivateWordOutput.encodedTrace machine anchor blank outputTape (cells times) read coefficient (coefficient + 1) exponent
          htime (capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator encoding n
          (bitTape blank bitSymbol inputTape input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n :=
  PrivateWordOutput.no_readability machine anchor blank outputTape (cells times) read coefficient (coefficient + 1) exponent
    htime (capacityBounds times coefficient exponent htime hexponent) hexponent stretch hstretch generator bitSymbol inputTape secure encoding monitor

end Family
end PolynomialWordOutput
