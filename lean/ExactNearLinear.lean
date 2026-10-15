import ExactMultitapeOutput
import PrivateMultiplication

/-! # Four-token native near-linear private bit computations -/
noncomputable section
namespace ExactNearLinear
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
section Family
variable {times : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (outputTape : Fin tapes) (cells : ℕ → ℤ) (bit : Symbol → Bool)
variable (coefficient : ℕ) (htime : ∀ n, times n ≤ coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1))
variable (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)

def model (n : ℕ) :=
  ExactEncryptedAlphabet.model ExactTaskAlphabet.binaryAlphabet
    (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank) ((NearLinearPrivateBit.generatorPrefix machine anchor coefficient htime stretch hstretch generator).generator n)
    (NearLinearPrivateBit.outputSources machine anchor n) (NearLinearPrivateBit.decoder machine blank outputTape bit)
    ExactTaskAlphabet.binaryAlphabet.readBit

def inputEncoding (n : ℕ) (tape : Fin tapes → ℤ → Symbol)
    (seed : Bits (NearLinearPrivateBit.seedLengths tapes State Symbol coefficient stretch n)) :=
  ExactEncryptedAlphabet.inputEncoding ExactTaskAlphabet.binaryAlphabet
    (plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n) tape) seed

theorem generated_output (n : ℕ) (tape : Fin tapes → ℤ → Symbol)
    (seed : Bits (NearLinearPrivateBit.seedLengths tapes State Symbol coefficient stretch n)) (output : Fin 2) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).generatedToken
      (inputEncoding machine anchor blank outputTape cells coefficient stretch n tape seed)
      ⟨NearLinearPrivateBit.payloadLength (times := times) machine anchor n + 1 + output.val, by
        change NearLinearPrivateBit.payloadLength (times := times) machine anchor n + 1 + output.val <
          NearLinearPrivateBit.payloadLength (times := times) machine anchor n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryOutput (ExactTaskAlphabet.boolCode
        (if output = 0 then some (bit ((machine.run (2 ^ horizonLevel (max 1 (times n)))
          (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells n))) else none))) := by
  unfold model inputEncoding
  rw [ExactEncryptedAlphabet.generated_correct]
  change ExactEncryptedAlphabet.protocolErase ExactTaskAlphabet.binaryAlphabet
    ((NearLinearPrivateBit.model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).generatedToken
      (NearLinearPrivateBit.inputEncoding machine anchor blank outputTape cells coefficient stretch n tape seed) _) = _
  rw [NearLinearPrivateBit.generated_output, ExactEncryptedAlphabet.protocolErase_data, ExactEncryptedAlphabet.erase_result]
  rfl

theorem context_bound (n : ℕ) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.contextLength ≤
      (⌈SeedBudget.coefficient (LogSquaredSeedBudget.degree stretch) stretch
        (LogSquaredSeedBudget.adjustedSize stretch (NearLinearPrivateBit.payloadCoefficient tapes State Symbol coefficient))⌉₊ +
        2 * NearLinearPrivateBit.payloadCoefficient tapes State Symbol coefficient + 2 * MultitapeMatrix.vocabulary tapes State Symbol + 2) *
        (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 2 :=
  NearLinearPrivateBit.context_bound machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n

theorem no_readability {Input : ℕ → Type*} [∀ n, Fintype (Input n)] [∀ n, Nonempty (Input n)] {codeWidth : ℕ}
    (tapesOf : ∀ n, Input n → Fin tapes → ℤ → Symbol) (secure : generator.IsPseudorandom)
    (encoding : Fin 4 → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (NearLinearPrivateBit.payloadLength (times := times) machine anchor n + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Input n)) (predicate : Input n → Bool),
      predictionSuccess distribution
        (fun input seed => ExactEncryptedAlphabet.encodedTrace ExactTaskAlphabet.binaryAlphabet
          (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
          (originalTransition machine blank) ((NearLinearPrivateBit.generatorPrefix machine anchor coefficient htime stretch hstretch generator).generator n)
          (NearLinearPrivateBit.outputSources machine anchor n) (NearLinearPrivateBit.decoder machine blank outputTape bit)
          ExactTaskAlphabet.binaryAlphabet.readBit encoding
          (plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n) (tapesOf n input)) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  simpa only [ExactEncryptedAlphabet.encodedTrace_eq_original] using
    NearLinearPrivateBit.no_readability machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator
      tapesOf secure (fun token => encoding (ExactEncryptedAlphabet.protocolErase ExactTaskAlphabet.binaryAlphabet token)) monitor

theorem one_layer (n : ℕ) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.layers = 1 := rfl

theorem heads_fixed (n : ℕ) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.heads =
      ExactEncryptedAlphabet.headCount (2 * MultitapeMatrix.vocabulary tapes State Symbol)
        (MultitapeMatrix.vocabulary tapes State Symbol) generator.locality := rfl

theorem polynomial_resources :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ^ 3 ∧
      (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ 6 := by
  let C := ⌈SeedBudget.coefficient (LogSquaredSeedBudget.degree stretch) stretch
      (LogSquaredSeedBudget.adjustedSize stretch (NearLinearPrivateBit.payloadCoefficient tapes State Symbol coefficient))⌉₊ +
    2 * NearLinearPrivateBit.payloadCoefficient tapes State Symbol coefficient + 2 * MultitapeMatrix.vocabulary tapes State Symbol + 3
  apply ExactEncryptedAlphabet.polynomial_resources ExactTaskAlphabet.binaryAlphabet
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank) (NearLinearPrivateBit.generatorPrefix machine anchor coefficient htime stretch hstretch generator)
    (NearLinearPrivateBit.outputSources machine anchor) (fun _ => NearLinearPrivateBit.decoder machine blank outputTape bit)
    ExactTaskAlphabet.binaryAlphabet.readBit (4 * C) 3
  intro n
  change (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.contextLength + 1 ≤ _
  have hc := context_bound machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n
  have hone : 1 ≤ (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 2 := by
    have hpow := Nat.one_le_pow 2 (Nat.log 2 (n + 1) + 1) (by omega)
    nlinarith
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have h := Nat.log_le_self 2 (n + 1); omega
  have hmul := Nat.mul_le_mul_left (C * (n + 1)) (Nat.pow_le_pow_left hlog 2)
  dsimp [C] at hmul ⊢
  nlinarith [show (n + 1) ^ 3 = (n + 1) * (n + 1) ^ 2 by ring]

end Family
end ExactNearLinear
