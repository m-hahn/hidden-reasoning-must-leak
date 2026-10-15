import PolylogSeedBudget
import PolylogSourceUpper
import EncryptedMultitapeFiniteOutput
import PrivatePolynomialTime

/-!
# Private near-linear source computations, with a native answer and EOS

An N log² N source time bound yields N log³ N binary reasoning. Every
ordinary NC⁰ stretch greater than one suffices for a derived sublinear seed.
No stronger quadratic-time/stretch hypothesis is used.
-/

noncomputable section
namespace PolylogPrivateBit
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]

def payloadCoefficient (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] (coefficient : ℕ) :=
  (PolylogSourceUpper.traceConstant tapes 2 coefficient + 1) * vocabulary tapes State Symbol + 1

def seedLengths (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] (coefficient : ℕ) (stretch : ℝ) :=
  PolylogSeedBudget.length 3 stretch (payloadCoefficient tapes State Symbol coefficient)

section Family
variable {times : ℕ → ℕ}
variable (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
variable (outputTape : Fin tapes) (cells : ℕ → ℤ) (bit : Symbol → Bool)
variable (coefficient : ℕ) (htime : ∀ n, times n ≤ coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 2)
variable (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)

def payloadLength (n : ℕ) := eventCount machine anchor (horizonLevel (max 1 (times n))) 0 * vocabulary tapes State Symbol

include htime in
theorem payload_bound (n : ℕ) : payloadLength (times := times) machine anchor n + 1 ≤
    payloadCoefficient tapes State Symbol coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3 := by
  have h := PolylogSourceUpper.trace_bound machine anchor 2 coefficient n (times n) (htime n)
  simp only [PolylogSourceUpper.logFactor, Nat.reduceAdd] at h
  have hone : 1 ≤ (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3 := by
    have hpow := Nat.one_le_pow 3 (Nat.log 2 (n + 1) + 1) (by omega)
    nlinarith
  change eventSteps machine anchor (horizonLevel (max 1 (times n))) ≤ _ at h
  unfold payloadLength eventCount payloadCoefficient
  nlinarith

include htime hstretch in
theorem capacity (n : ℕ) : payloadLength (times := times) machine anchor n + 1 ≤
    ⌊(seedLengths tapes State Symbol coefficient stretch n : ℝ) ^ stretch⌋₊ := by
  apply PolylogSeedBudget.floor_capacity 3 hstretch (by positivity)
  have h := payload_bound machine anchor coefficient htime n
  exact_mod_cast h

def generatorPrefix : NC0GeneratorFamily (seedLengths tapes State Symbol coefficient stretch)
    (fun n => payloadLength (times := times) machine anchor n + 1) :=
  PRGRestriction.family (PRGReindex.family generator (seedLengths tapes State Symbol coefficient stretch))
    (capacity machine anchor coefficient htime stretch hstretch)

theorem generatorPrefix_secure (secure : generator.IsPseudorandom) :
    (generatorPrefix machine anchor coefficient htime stretch hstretch generator).IsPseudorandom := by
  apply PRGRestriction.secure
  obtain ⟨degree, _, hinverse⟩ := PolylogSeedBudget.inverse_bound 3
    (size := (payloadCoefficient tapes State Symbol coefficient : ℝ)) hstretch
  apply PRGReindex.secure generator secure _ degree
  intro n
  exact (hinverse n).trans (Nat.pow_le_pow_left (Nat.le_succ _) degree)

def outputCode : Option Bool ≃ Fin (Fintype.card (Option Bool)) := Fintype.equivFin _

def outputSources (n : ℕ) : Fin 2 → Fin (vocabulary tapes State Symbol) → Fin (payloadLength (times := times) machine anchor n) :=
  fun _ => sources (extra := 0) machine anchor (horizonLevel (max 1 (times n))) 0

def decoder : Fin 2 → Bits (vocabulary tapes State Symbol) → Fin (Fintype.card (Option Bool)) :=
  fun output word => outputCode (if output = 0 then some (decode machine blank outputTape bit word) else none)

def model (n : ℕ) :=
  EncryptedFiniteReadout.model (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank) ((generatorPrefix machine anchor coefficient htime stretch hstretch generator).generator n)
    (outputSources machine anchor n) (decoder machine blank outputTape bit)

def inputEncoding (n : ℕ) (tape : Fin tapes → ℤ → Symbol)
    (seed : Bits (seedLengths tapes State Symbol coefficient stretch n)) :=
  EncryptedFiniteReadout.inputEncoding (outputCard := Fintype.card (Option Bool))
    (plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n) tape) seed

theorem generated_output (n : ℕ) (tape : Fin tapes → ℤ → Symbol)
    (seed : Bits (seedLengths tapes State Symbol coefficient stretch n)) (output : Fin 2) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).generatedToken
      (inputEncoding machine anchor blank outputTape cells coefficient stretch n tape seed)
      ⟨payloadLength (times := times) machine anchor n + 1 + output.val, by
        change payloadLength (times := times) machine anchor n + 1 + output.val < payloadLength (times := times) machine anchor n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (EncryptedFiniteReadout.result (outputCode (if output = 0 then
        some (bit ((machine.run (2 ^ horizonLevel (max 1 (times n))) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells n))) else none))) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  unfold model inputEncoding payloadLength
  rw [EncryptedFiniteReadout.output_correct]
  unfold outputSources
  rw [block_plain]
  unfold decoder decode
  rw [RoutedMatrix.decodeIndicator_indicator]
  simp only [ObliviousMatrix.label, ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply, ObliviousMatrix.controlOf,
    ObliviousProgram.Program.traceToken_control, MultitapeOutputMatrix.output_cell_correct]

theorem context_bound (n : ℕ) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.contextLength ≤
      (⌈SeedBudget.coefficient (PolylogSeedBudget.degree stretch) stretch
        (PolylogSeedBudget.adjustedSize 3 stretch (payloadCoefficient tapes State Symbol coefficient))⌉₊ +
        2 * payloadCoefficient tapes State Symbol coefficient + 2 * vocabulary tapes State Symbol + 2) *
        (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3 := by
  have hb := PolylogSeedBudget.degree_bounds hstretch
  have hseed := SeedBudget.seed_polynomial_bound (size := PolylogSeedBudget.adjustedSize 3 stretch
    (payloadCoefficient tapes State Symbol coefficient)) (by linarith : 0 < PolylogSeedBudget.degree stretch) hb.2 n
  change seedLengths tapes State Symbol coefficient stretch n ≤ _ at hseed
  have hp := payload_bound machine anchor coefficient htime n
  have hscale : n + 1 ≤ (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3 := by
    have hpow := Nat.one_le_pow 3 (Nat.log 2 (n + 1) + 1) (by omega)
    nlinarith
  have hs := hseed.trans (Nat.mul_le_mul_left _ hscale)
  rw [model, EncryptedFiniteReadout.context_length]
  change seedLengths tapes State Symbol coefficient stretch n +
    (eventCount machine anchor (horizonLevel (max 1 (times n))) 0 + 2) * vocabulary tapes State Symbol +
    (payloadLength (times := times) machine anchor n) + 1 + 1 ≤ _
  unfold payloadLength at hp ⊢
  nlinarith

theorem no_readability {Input : ℕ → Type*} [∀ n, Fintype (Input n)] [∀ n, Nonempty (Input n)] {codeWidth : ℕ}
    (tapesOf : ∀ n, Input n → Fin tapes → ℤ → Symbol) (secure : generator.IsPseudorandom)
    (encoding : Fin (EncryptedMatrix.packetCount 2 + Fintype.card (Option Bool) + 1) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (payloadLength (times := times) machine anchor n + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Input n)) (predicate : Input n → Bool),
      predictionSuccess distribution
        (fun input seed => EncryptedFiniteReadout.encodedTrace
          (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
          (originalTransition machine blank) ((generatorPrefix machine anchor coefficient htime stretch hstretch generator).generator n)
          (outputSources machine anchor n) (decoder machine blank outputTape bit) encoding
          (plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n) (tapesOf n input)) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  apply EncryptedFiniteReadout.no_readability_finite
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank) (outputSources machine anchor) (fun _ => decoder machine blank outputTape bit)
    (fun n input => plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n) (tapesOf n input))
    (generatorPrefix machine anchor coefficient htime stretch hstretch generator)
    (generatorPrefix_secure machine anchor coefficient htime stretch hstretch generator secure)
    encoding monitor (8 * payloadCoefficient tapes State Symbol coefficient) 4
  intro n
  have hp := payload_bound machine anchor coefficient htime n
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have h := Nat.log_le_self 2 (n + 1); omega
  have hsquare := Nat.pow_le_pow_left hlog 3
  have hmul := Nat.mul_le_mul_left (payloadCoefficient tapes State Symbol coefficient * (n + 1)) hsquare
  change payloadLength (times := times) machine anchor n ≤ _
  nlinarith [show (n + 1) ^ 4 = (n + 1) * (n + 1) ^ 3 by ring]

theorem one_layer (n : ℕ) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.layers = 1 := rfl

theorem heads_fixed (n : ℕ) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.heads =
      EncryptedMultitapeOutput.outputHeads tapes State Symbol generator.locality := rfl

theorem precision_fixed (n : ℕ) :
    (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).parameters.scalarBits =
      RoutedMatrix.precision (EncryptedMatrix.packetCount 2 + Fintype.card (Option Bool) + 1)
        (EncryptedMultitapeOutput.outputHeads tapes State Symbol generator.locality)
        (EncryptedMatrix.opcodeCount 2 (2 * vocabulary tapes State Symbol)
          (MultitapeMatrix.opcodes tapes State Symbol * (vocabulary tapes State Symbol + 1)) generator.locality +
          EncryptedFiniteReadout.readOpcodes (vocabulary tapes State Symbol) (Fintype.card (Option Bool)) generator.locality + 1) := rfl

theorem polynomial_resources :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ^ 4 ∧
      (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ 8 := by
  let C := ⌈SeedBudget.coefficient (PolylogSeedBudget.degree stretch) stretch
      (PolylogSeedBudget.adjustedSize 3 stretch (payloadCoefficient tapes State Symbol coefficient))⌉₊ +
    2 * payloadCoefficient tapes State Symbol coefficient + 2 * vocabulary tapes State Symbol + 3
  apply EncryptedFiniteReadout.polynomial_resources
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (fun _ : Fin 1 => cells n))
    (originalTransition machine blank) (generatorPrefix machine anchor coefficient htime stretch hstretch generator)
    (outputSources machine anchor) (fun _ => decoder machine blank outputTape bit) (8 * C) 4
  intro n
  change (model machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n).architecture.contextLength + 1 ≤ _
  have hc := context_bound machine anchor blank outputTape cells bit coefficient htime stretch hstretch generator n
  have hone : 1 ≤ (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 3 := by
    have hpow := Nat.one_le_pow 3 (Nat.log 2 (n + 1) + 1) (by omega)
    nlinarith
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have h := Nat.log_le_self 2 (n + 1); omega
  have hsquare := Nat.pow_le_pow_left hlog 3
  have hmul := Nat.mul_le_mul_left (C * (n + 1)) hsquare
  dsimp [C] at hmul ⊢
  nlinarith [show (n + 1) ^ 4 = (n + 1) * (n + 1) ^ 3 by ring]

end Family
end PolylogPrivateBit
