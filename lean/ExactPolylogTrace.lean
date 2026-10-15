import ExactPolylogBit
import ExactProtocolToken
import MultitapeLiteralInitialization

/-! Native first-separator information bounds for log-cubed computations,
with constant-or-single-bit initialization on arbitrary source tapes. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace ExactPolylogTrace
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
open MultitapeLiteralInitialization
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
section Family
variable {times : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (outputTape : Fin tapes) (cells : ℕ → ℤ) (bit : Symbol → Bool)
variable (coefficient : ℕ) (htime : ∀ n, times n ≤ coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 2)
variable (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)
variable (sourcesOf : ∀ n, Fin tapes → ℤ → SymbolSource (n + n) Symbol)

def literal (n : ℕ) := binaryLiteral machine anchor blank (sourcesOf n)
  (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n)

def plain (n : ℕ) (input : Bits (n + n)) :=
  plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n)
    (initialTape (sourcesOf n) input)

theorem literal_correct (n : ℕ) (input : Bits (n + n)) (wire) :
    (literal (times := times) machine anchor blank outputTape cells sourcesOf n wire).eval input =
      RoutedMatrix.promptInput (plain (times := times) machine anchor blank outputTape cells sourcesOf n input) wire :=
  binaryLiteral_correct machine anchor blank (sourcesOf n) _ outputTape _ input wire

def model (n : ℕ) :=
  ExactProtocolToken.tokenGenerator ExactTaskAlphabet.binaryAlphabet
    (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank) ((PolylogPrivateBit.generatorPrefix machine anchor coefficient htime stretch hstretch generator).generator n)
    (PolylogPrivateBit.outputSources machine anchor n) (PolylogPrivateBit.decoder machine blank outputTape bit) ExactTaskAlphabet.binaryAlphabet.readBit
    (plain (times := times) machine anchor blank outputTape cells sourcesOf n)
    (literal (times := times) machine anchor blank outputTape cells sourcesOf n)
    (literal_correct (times := times) machine anchor blank outputTape cells sourcesOf n)

theorem answer_correct (n : ℕ) (input : Bits (n + n))
    (seed : Bits (PolylogPrivateBit.seedLengths tapes State Symbol coefficient stretch n)) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator sourcesOf n).answer (Fin.append input seed) =
      bit ((machine.run (2 ^ horizonLevel (max 1 (times n)))
        (MultitapeEfficientPhase.sourceInitial machine (initialTape (sourcesOf n) input))).tape outputTape (cells n)) := by
  unfold model
  rw [ExactProtocolToken.native_answer]
  change (ExactPolylogBit.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).parameters.outputLabel
    ((ExactPolylogBit.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).generatedToken
      (ExactPolylogBit.inputEncoding machine anchor blank outputTape cells coefficient stretch n (initialTape (sourcesOf n) input) seed) _) = _
  have h := ExactPolylogBit.generated_output machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n
    (initialTape (sourcesOf n) input) seed (0 : Fin 2)
  simp only [Fin.val_zero, Nat.add_zero, ite_true] at h
  change (ExactPolylogBit.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).parameters.outputLabel
    ((ExactPolylogBit.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).generatedToken
      (ExactPolylogBit.inputEncoding machine anchor blank outputTape cells coefficient stretch n (initialTape (sourcesOf n) input) seed)
      ⟨PolylogPrivateBit.payloadLength (times := times) machine anchor n + 1, by
        change PolylogPrivateBit.payloadLength (times := times) machine anchor n + 1 <
          PolylogPrivateBit.payloadLength (times := times) machine anchor n + 3; omega⟩) = _
  rw [h, ExactTaskAlphabet.binaryOutput_some]
  change ProtocolMatrix.label ExactTaskAlphabet.binaryAlphabet.readBit
    (ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryAlphabet.bit _)) = _
  simp only [ProtocolMatrix.label, ProtocolMatrix.dataToken, Fin.lastCases_castSucc,
    ExactTaskAlphabet.binaryAlphabet.readBit_bit]

theorem multiplication_footprint (tal : Tal.FourierTailTheorem) (n : ℕ) (hn : 2 ≤ n)
    (source_correct : ∀ input : Bits (n + n),
      bit ((machine.run (2 ^ horizonLevel (max 1 (times n)))
        (MultitapeEfficientPhase.sourceInitial machine (initialTape (sourcesOf n) input))).tape outputTape (cells n)) =
          MultiplicationFootprint.middleBitTarget n input) :
    let M := model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator sourcesOf n;
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate n M.fiberDepth M.fiberSize) -
      (PolylogPrivateBit.seedLengths tapes State Symbol coefficient stretch n : ℝ) ≤
        (FiniteInformation.Distribution.uniform (Bits (n + n) × Bits (PolylogPrivateBit.seedLengths tapes State Symbol coefficient stretch n))).mutualInformation Prod.fst M.seededTrace := by
  apply TokenAutoregressive.Generator.seeded_multiplication_footprint tal _ _ hn
  intro input seed
  rw [answer_correct]
  exact source_correct input

end Family
end ExactPolylogTrace
