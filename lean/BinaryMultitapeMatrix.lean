import MultitapeMatrix
import BinaryObliviousMatrix

/-!
# Efficient multitape computation with actual binary payloads

This composes the proved machine compiler, finite-opcode binary expansion,
and on-the-fly binary encryption. The final answer is computed by reading
the actual source output tape; only the internal event payload is encrypted.
-/

noncomputable section
namespace BinaryMultitapeMatrix
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
variable {n seedLength locality : ℕ}

def model (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  BinaryObliviousMatrix.model (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
    (eventSteps machine anchor level) (fun control => decode (control.auxiliary.scanned outputTape))

def inputEncoding (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (input : Bits n) :=
  BinaryObliviousMatrix.inputEncoding (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
    (eventSteps machine anchor level) input

theorem output_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (input : Bits n) :
    (model machine anchor blank bitSymbol inputTape n level outputTape cell decode).answer
      (inputEncoding machine anchor blank bitSymbol inputTape level outputTape cell input) =
        decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine
          (bitTape blank bitSymbol inputTape input))).tape outputTape cell) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  have he := BinaryObliviousMatrix.output_correct (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
    (eventSteps machine anchor level) (fun control => decode (control.auxiliary.scanned outputTape)) input
  have h := MultitapeMatrix.bit_output_correct machine anchor blank bitSymbol inputTape level outputTape cell decode input
  exact he.trans (by simpa only [bitModel, bitInput, bitPrompt, ObliviousMatrix.output_correct] using h)

def encryptedModel (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  BinaryObliviousMatrix.encryptedModel (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
    (eventSteps machine anchor level) (fun control => decode (control.auxiliary.scanned outputTape)) generator

def encryptedInput (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (input : Bits n) (seed : Bits seedLength) :=
  BinaryObliviousMatrix.encryptedInput (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
    (eventSteps machine anchor level) input seed

theorem encrypted_output_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality)
    (input : Bits n) (seed : Bits seedLength) :
    (encryptedModel machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).answer
      (encryptedInput machine anchor blank bitSymbol inputTape level outputTape cell input seed) =
        decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine
          (bitTape blank bitSymbol inputTape input))).tape outputTape cell) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  have he := BinaryObliviousMatrix.encrypted_output_correct
    (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell) (eventSteps machine anchor level)
    (fun control => decode (control.auxiliary.scanned outputTape)) generator input seed
  have h := MultitapeMatrix.bit_output_correct machine anchor blank bitSymbol inputTape level outputTape cell decode input
  exact he.trans (by simpa only [bitModel, bitInput, bitPrompt, ObliviousMatrix.output_correct] using h)

def inputCircuit (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :=
  Circuit.seq (MultitapeMatrix.inputCircuit machine anchor blank bitSymbol inputTape n level outputTape cell)
    (BinaryMatrix.inputCircuit (ObliviousMatrix.front (eventSteps machine anchor level)) (vocabulary tapes State Symbol))

theorem inputCircuit_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (input : Bits n) :
    Circuit.eval (inputCircuit machine anchor blank bitSymbol inputTape n level outputTape cell) input =
      inputEncoding machine anchor blank bitSymbol inputTape level outputTape cell input := by
  simp only [inputCircuit, Circuit.eval, MultitapeMatrix.inputCircuit_correct, bitInput, BinaryMatrix.inputCircuit_correct]
  rfl

theorem inputCircuit_depth (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :
    Circuit.depth (inputCircuit machine anchor blank bitSymbol inputTape n level outputTape cell) ≤ 2 := by
  exact Nat.add_le_add (MultitapeMatrix.inputCircuit_depth machine anchor blank bitSymbol inputTape n level outputTape cell)
    (BinaryMatrix.inputCircuit_depth _ _)

theorem binary_count_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (steps : ℕ) (hsteps : 1 ≤ steps) :
    eventSteps machine anchor (horizonLevel steps) * vocabulary tapes State Symbol ≤
      ((4 * (248 * tapes + 1)) * vocabulary tapes State Symbol) * steps * (Nat.log 2 steps + 1) := by
  have h := Nat.mul_le_mul_right (vocabulary tapes State Symbol) (MultitapeMatrix.transcript_count_bound machine anchor steps hsteps)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

def transcript (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality)
    (input : Bits n) (seed : Bits seedLength) : Bits (eventSteps machine anchor level * vocabulary tapes State Symbol) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  EncryptedBinaryMatrix.transcript
    (BinarySchedule.schedule
      (EncryptedObliviousMatrix.schedule (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
        (eventSteps machine anchor level)) ObliviousMatrix.vocabulary_positive)
    (BinarySchedule.transition ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition
      (ObliviousMatrix.label (fun control => decode (control.auxiliary.scanned outputTape)))) BinarySchedule.tokenBit generator
    (BinarySchedule.prompt (bitPrompt machine anchor blank bitSymbol inputTape level outputTape cell input)) seed

/-- Every polynomial monitor of the actual binary payload is covered by
PRG security. The polynomial trace length is derived from source time;
zero-time horizons are normalized without an additional positivity premise. -/
theorem no_readability {seedLengths times : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ℕ → ℤ) (decode : Symbol → Bool)
    (generator : NC0GeneratorFamily seedLengths
      (fun n => eventSteps machine anchor (horizonLevel (max 1 (times n))) * vocabulary tapes State Symbol + 1))
    (secure : generator.IsPseudorandom)
    (monitor : PolynomialMonitorFamily
      (fun n => eventSteps machine anchor (horizonLevel (max 1 (times n))) * vocabulary tapes State Symbol))
    (coefficient exponent : ℕ) (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => transcript machine anchor blank bitSymbol inputTape (horizonLevel (max 1 (times n)))
          outputTape (cells n) decode (generator.generator n) input seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  apply EncryptedBinaryMatrix.no_readability
    (fun n => BinarySchedule.schedule
      (EncryptedObliviousMatrix.schedule
        (bitProgram machine anchor blank bitSymbol inputTape n (horizonLevel (max 1 (times n))) outputTape (cells n))
        (eventSteps machine anchor (horizonLevel (max 1 (times n))))) ObliviousMatrix.vocabulary_positive)
    (BinarySchedule.transition ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition
      (ObliviousMatrix.label (fun control => decode (control.auxiliary.scanned outputTape)))) BinarySchedule.tokenBit
    (fun n input => BinarySchedule.prompt
      (bitPrompt machine anchor blank bitSymbol inputTape (horizonLevel (max 1 (times n))) outputTape (cells n) input))
    generator secure monitor
    (((4 * (248 * tapes + 1)) * (coefficient + 2) ^ 2) * vocabulary tapes State Symbol) (2 * exponent)
  intro n
  have hp : 1 ≤ (n + 1) ^ exponent := Nat.one_le_pow _ _ (by omega)
  have ht : max 1 (times n) ≤ (coefficient + 1) * (n + 1) ^ exponent := by
    apply max_le <;> have h := time_bound n <;> nlinarith
  have he := Nat.mul_le_mul_right (vocabulary tapes State Symbol)
    (MultitapeMatrix.event_polynomial_bound machine anchor (max 1 (times n)) n (coefficient + 1) exponent (Nat.le_max_left _ _) ht)
  simpa only [Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he

end BinaryMultitapeMatrix
