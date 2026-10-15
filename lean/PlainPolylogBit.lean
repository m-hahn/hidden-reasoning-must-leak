import PlainBinaryWord
import PolylogPrivateBit

/-! Seed-free four-token bit/EOS simulation with log-cubed context.
Resource proofs remain generic in the fixed machine data and its runtime
coefficient; no concrete transition table is evaluated by these proofs. -/

noncomputable section
namespace PlainPolylogBit
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
section Family
variable {times : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (outputTape : Fin tapes) (cells : ℕ → ℤ) (bit : Symbol → Bool)
variable (coefficient : ℕ) (htime : ∀ n, times n ≤ coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 2)

def model (n : ℕ) :=
  ExactEncryptedAlphabet.model ExactTaskAlphabet.binaryAlphabet
    (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank)
    (PlainBinaryWord.zeroPad (PolylogPrivateBit.payloadLength (times := times) machine anchor n + 1))
    (PolylogPrivateBit.outputSources machine anchor n) (PolylogPrivateBit.decoder machine blank outputTape bit)
    ExactTaskAlphabet.binaryAlphabet.readBit

def inputEncoding (n : ℕ) (tape : Fin tapes → ℤ → Symbol) :=
  ExactEncryptedAlphabet.inputEncoding ExactTaskAlphabet.binaryAlphabet
    (plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n) tape)
    (fun index : Fin 0 => Fin.elim0 index)

theorem generated_output (n : ℕ) (tape : Fin tapes → ℤ → Symbol) (output : Fin 2) :
    (model (times := times) machine anchor blank outputTape cells bit n).generatedToken
      (inputEncoding (times := times) machine anchor blank outputTape cells n tape)
      ⟨PolylogPrivateBit.payloadLength (times := times) machine anchor n + 1 + output.val, by
        change PolylogPrivateBit.payloadLength (times := times) machine anchor n + 1 + output.val <
          PolylogPrivateBit.payloadLength (times := times) machine anchor n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (ExactTaskAlphabet.binaryOutput (ExactTaskAlphabet.boolCode (if output = 0 then
        some (bit ((machine.run (2 ^ horizonLevel (max 1 (times n)))
          (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells n))) else none))) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) :=
    ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  unfold model inputEncoding PolylogPrivateBit.payloadLength
  rw [ExactEncryptedAlphabet.output_correct]
  unfold PolylogPrivateBit.outputSources
  rw [block_plain]
  unfold PolylogPrivateBit.decoder decode
  rw [RoutedMatrix.decodeIndicator_indicator]
  simp only [ObliviousMatrix.label, ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply, ObliviousMatrix.controlOf,
    ObliviousProgram.Program.traceToken_control, MultitapeOutputMatrix.output_cell_correct]
  rfl

def contextCoefficient (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] (coefficient : ℕ) : ℕ :=
  2 * PolylogPrivateBit.payloadCoefficient tapes State Symbol coefficient +
    2 * vocabulary tapes State Symbol + 3

include htime in
theorem context_bound (n : ℕ) :
    (model (times := times) machine anchor blank outputTape cells bit n).architecture.contextLength + 1 ≤
      contextCoefficient tapes State Symbol coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3 := by
  have hp := PolylogPrivateBit.payload_bound machine anchor coefficient htime n
  have hone : 1 ≤ (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3 := by
    have hpow := Nat.one_le_pow 3 (Nat.log 2 (n + 1) + 1) (by omega)
    nlinarith
  rw [model, ExactEncryptedAlphabet.context_length]
  simp only [Nat.zero_add]
  change (eventCount machine anchor (horizonLevel (max 1 (times n))) 0 + 2) *
      vocabulary tapes State Symbol + PolylogPrivateBit.payloadLength (times := times) machine anchor n + 3 ≤ _
  unfold contextCoefficient PolylogPrivateBit.payloadLength at *
  nlinarith

def padFamily : NC0GeneratorFamily (fun _ => 0)
    (fun n => PolylogPrivateBit.payloadLength (times := times) machine anchor n + 1) where
  locality := 0
  generator _ := PlainBinaryWord.zeroPad _

include coefficient htime in
theorem polynomial_resources : ∃ D P : ℕ, ∀ n,
    (model (times := times) machine anchor blank outputTape cells bit n).architecture.hiddenWidth ≤ D * (n + 1) ^ 4 ∧
    (model (times := times) machine anchor blank outputTape cells bit n).architecture.parameterCount ≤ P * (n + 1) ^ 8 := by
  apply ExactEncryptedAlphabet.polynomial_resources ExactTaskAlphabet.binaryAlphabet
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank) (padFamily (times := times) machine anchor)
    (PolylogPrivateBit.outputSources machine anchor)
    (fun _ => PolylogPrivateBit.decoder machine blank outputTape bit)
    ExactTaskAlphabet.binaryAlphabet.readBit (8 * contextCoefficient tapes State Symbol coefficient) 4
  intro n
  change (model (times := times) machine anchor blank outputTape cells bit n).architecture.contextLength + 1 ≤ _
  have hc := context_bound machine anchor blank outputTape cells bit coefficient htime n
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have h := Nat.log_le_self 2 (n + 1); omega
  have hs := Nat.mul_le_mul_left (contextCoefficient tapes State Symbol coefficient * (n + 1)) (Nat.pow_le_pow_left hlog 3)
  nlinarith [show (n + 1) ^ 4 = (n + 1) * (n + 1) ^ 3 by ring]

theorem architecture_fixed : ∃ heads precision : ℕ, ∀ n,
    (model (times := times) machine anchor blank outputTape cells bit n).architecture.vocabulary = 4 ∧
    (model (times := times) machine anchor blank outputTape cells bit n).architecture.layers = 1 ∧
    (model (times := times) machine anchor blank outputTape cells bit n).architecture.heads = heads ∧
    (model (times := times) machine anchor blank outputTape cells bit n).parameters.scalarBits = precision := by
  refine ⟨(model (times := times) machine anchor blank outputTape cells bit 0).architecture.heads,
    (model (times := times) machine anchor blank outputTape cells bit 0).parameters.scalarBits, ?_⟩
  intro n
  exact ⟨rfl, rfl, rfl, rfl⟩

end Family
end PlainPolylogBit
