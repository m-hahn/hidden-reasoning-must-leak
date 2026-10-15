import ExactNearLinear
import ExactProtocolToken

/-! # Native seeded information bounds for the four-token near-linear model -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ExactNearLinearTrace
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
section Family
variable {times : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ℕ → ℤ) (bit : Symbol → Bool)
variable (coefficient : ℕ) (htime : ∀ n, times n ≤ coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1))
variable (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)

def literal (n rawSize : ℕ) := BinaryMatrix.promptLiteral
  (finiteLiteral machine anchor blank bitSymbol inputTape rawSize (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))

def plain (n rawSize : ℕ) (input : Bits rawSize) :=
  plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n)
    (bitTape blank bitSymbol inputTape input)

theorem literal_correct (n rawSize : ℕ) (input : Bits rawSize) (wire) :
    (literal (times := times) machine anchor blank bitSymbol inputTape outputTape cells n rawSize wire).eval input =
      RoutedMatrix.promptInput (plain (times := times) machine anchor blank bitSymbol inputTape outputTape cells n rawSize input) wire :=
  BinaryMatrix.promptLiteral_correct _ input _
    (finiteLiteral_correct machine anchor blank bitSymbol inputTape (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n) input) wire

def model (n rawSize : ℕ) :=
  ExactProtocolToken.tokenGenerator ExactTaskAlphabet.binaryAlphabet
    (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank) ((NearLinearPrivateBit.generatorPrefix machine anchor coefficient htime stretch hstretch generator).generator n)
    (NearLinearPrivateBit.outputSources machine anchor n) (NearLinearPrivateBit.decoder machine blank outputTape bit) ExactTaskAlphabet.binaryAlphabet.readBit
    (plain (times := times) machine anchor blank bitSymbol inputTape outputTape cells n rawSize)
    (literal (times := times) machine anchor blank bitSymbol inputTape outputTape cells n rawSize)
    (literal_correct (times := times) machine anchor blank bitSymbol inputTape outputTape cells n rawSize)

theorem answer_correct (n rawSize : ℕ) (input : Bits rawSize)
    (seed : Bits (NearLinearPrivateBit.seedLengths tapes State Symbol coefficient stretch n)) :
    (model machine anchor blank bitSymbol inputTape outputTape cells bit coefficient htime stretch hstretch generator n rawSize).answer (Fin.append input seed) =
      bit ((machine.run (2 ^ horizonLevel (max 1 (times n)))
        (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).tape outputTape (cells n)) := by
  unfold model
  rw [ExactProtocolToken.native_answer]
  change (ExactNearLinear.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).parameters.outputLabel
    ((ExactNearLinear.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).generatedToken
      (ExactNearLinear.inputEncoding machine anchor blank outputTape cells coefficient stretch n (bitTape blank bitSymbol inputTape input) seed) _) = _
  have h := ExactNearLinear.generated_output machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n
    (bitTape blank bitSymbol inputTape input) seed (0 : Fin 2)
  simp only [Fin.val_zero, Nat.add_zero, ite_true] at h
  change (ExactNearLinear.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).parameters.outputLabel
    ((ExactNearLinear.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).generatedToken
      (ExactNearLinear.inputEncoding machine anchor blank outputTape cells coefficient stretch n (bitTape blank bitSymbol inputTape input) seed)
      ⟨NearLinearPrivateBit.payloadLength (times := times) machine anchor n + 1, by
        change NearLinearPrivateBit.payloadLength (times := times) machine anchor n + 1 < NearLinearPrivateBit.payloadLength (times := times) machine anchor n + 3; omega⟩) = _
  rw [h]
  rw [ExactTaskAlphabet.binaryOutput_some]
  change ProtocolMatrix.label ExactTaskAlphabet.binaryAlphabet.readBit (ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryAlphabet.bit _)) = _
  simp only [ProtocolMatrix.label, ProtocolMatrix.dataToken, Fin.lastCases_castSucc, ExactTaskAlphabet.binaryAlphabet.readBit_bit]

theorem multiplication_footprint (tal : Tal.FourierTailTheorem) (N : ℕ) (hN : 2 ≤ N)
    (source_correct : ∀ input : Bits (N + N),
      bit ((machine.run (2 ^ horizonLevel (max 1 (times N)))
        (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).tape outputTape (cells N)) =
          MultiplicationFootprint.middleBitTarget N input) :
    let M := model machine anchor blank bitSymbol inputTape outputTape cells bit coefficient htime stretch hstretch generator N (N + N);
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N M.fiberDepth M.fiberSize) -
      (NearLinearPrivateBit.seedLengths tapes State Symbol coefficient stretch N : ℝ) ≤
        (FiniteInformation.Distribution.uniform (Bits (N + N) × Bits (NearLinearPrivateBit.seedLengths tapes State Symbol coefficient stretch N))).mutualInformation Prod.fst M.seededTrace := by
  apply TokenAutoregressive.Generator.seeded_multiplication_footprint tal _ _ hN
  intro input seed
  rw [answer_correct]
  exact source_correct input

end Family
end ExactNearLinearTrace
