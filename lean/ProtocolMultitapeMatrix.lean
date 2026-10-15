import ProtocolEncryptedBinary
import BinaryMultitapeMatrix
import ProtocolToken

/-!
# Efficient source computation with the complete native binary protocol

The actual model emits binary ciphertext, then its own separator, then the
plaintext source output bit. Its prompt is a depth-one literal encoding of
raw input and seed; no source execution or pad is precomputed.
-/

noncomputable section
namespace ProtocolMultitapeMatrix
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
variable {n seedLength locality : ℕ}

def schedule (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  BinarySchedule.schedule
    (EncryptedObliviousMatrix.schedule (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
      (eventSteps machine anchor level))
    (ObliviousMatrix.vocabulary_positive (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol))

def transition (machine : MultitapeTuring.Machine tapes State Symbol) (blank : Symbol)
    (outputTape : Fin tapes) (decode : Symbol → Bool) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  BinarySchedule.transition (ObliviousMatrix.vocabulary_positive
      (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol))
    (ObliviousMatrix.transition (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol))
    (ObliviousMatrix.label (Symbol := SimulatorSymbol Symbol) (fun control => decode (control.auxiliary.scanned outputTape)))

def plainPrompt (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (input : Bits n) :=
  BinarySchedule.prompt (bitPrompt machine anchor blank bitSymbol inputTape level outputTape cell input)

def plainLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :=
  BinaryMatrix.promptLiteral (MultitapeMatrix.inputLiteral machine anchor blank bitSymbol inputTape n level outputTape cell)

theorem plainLiteral_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (input : Bits n) (wire) :
    (plainLiteral machine anchor blank bitSymbol inputTape n level outputTape cell wire).eval input =
      RoutedMatrix.promptInput (plainPrompt machine anchor blank bitSymbol inputTape level outputTape cell input) wire :=
  BinaryMatrix.promptLiteral_correct _ input _
    (MultitapeMatrix.inputLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cell input) wire

def model (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality) :=
  ProtocolEncryptedBinary.model (schedule machine anchor blank bitSymbol inputTape n level outputTape cell)
    (transition machine blank outputTape decode) BinarySchedule.tokenBit generator

def inputEncoding (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (input : Bits n) (seed : Bits seedLength) :=
  ProtocolEncryptedBinary.inputEncoding (plainPrompt machine anchor blank bitSymbol inputTape level outputTape cell input) seed

theorem output_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality)
    (input : Bits n) (seed : Bits seedLength) :
    (model machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).answer
      (inputEncoding machine anchor blank bitSymbol inputTape level outputTape cell input seed) =
        decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine
          (bitTape blank bitSymbol inputTape input))).tape outputTape cell) := by
  have he := ProtocolEncryptedBinary.output_correct
    (schedule machine anchor blank bitSymbol inputTape n level outputTape cell)
    (transition machine blank outputTape decode) BinarySchedule.tokenBit generator
    (plainPrompt machine anchor blank bitSymbol inputTape level outputTape cell input) seed
  have hb := EncryptedBinaryMatrix.output_correct
    (schedule machine anchor blank bitSymbol inputTape n level outputTape cell)
    (transition machine blank outputTape decode) BinarySchedule.tokenBit generator
    (plainPrompt machine anchor blank bitSymbol inputTape level outputTape cell input) seed
  exact he.trans (hb.symm.trans (BinaryMultitapeMatrix.encrypted_output_correct
    machine anchor blank bitSymbol inputTape level outputTape cell decode generator input seed))

def inputLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :=
  ProtocolEncryptedBinary.inputLiteral
    (BinaryMatrix.promptLiteral (MultitapeMatrix.inputLiteral machine anchor blank bitSymbol inputTape n level outputTape cell)) seedLength

theorem inputLiteral_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (input : Bits n) (seed : Bits seedLength) (wire) :
    (inputLiteral machine anchor blank bitSymbol inputTape n seedLength level outputTape cell wire).eval (Fin.append input seed) =
      inputEncoding machine anchor blank bitSymbol inputTape level outputTape cell input seed wire := by
  apply ProtocolEncryptedBinary.inputLiteral_correct
  intro wire
  exact BinaryMatrix.promptLiteral_correct _ input _
    (MultitapeMatrix.inputLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cell input) wire

def transcript (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality)
    (input : Bits n) (seed : Bits seedLength) : Bits (eventSteps machine anchor level * vocabulary tapes State Symbol) :=
  ProtocolEncryptedBinary.transcript (schedule machine anchor blank bitSymbol inputTape n level outputTape cell)
    (transition machine blank outputTape decode) BinarySchedule.tokenBit generator
    (plainPrompt machine anchor blank bitSymbol inputTape level outputTape cell input) seed

theorem transcript_eq_original (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality)
    (input : Bits n) (seed : Bits seedLength) :
    transcript machine anchor blank bitSymbol inputTape level outputTape cell decode generator input seed =
      BinaryMultitapeMatrix.transcript machine anchor blank bitSymbol inputTape level outputTape cell decode generator input seed :=
  ProtocolEncryptedBinary.transcript_eq_original _ _ _ _ _ _

theorem payload_polynomial_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (time n coefficient exponent : ℕ) (bounded : time ≤ coefficient * (n + 1) ^ exponent) :
    eventSteps machine anchor (horizonLevel (max 1 time)) * vocabulary tapes State Symbol ≤
      (((4 * (248 * tapes + 1)) * (coefficient + 2) ^ 2) * vocabulary tapes State Symbol) * (n + 1) ^ (2 * exponent) := by
  have hp : 1 ≤ (n + 1) ^ exponent := Nat.one_le_pow _ _ (by omega)
  have ht : max 1 time ≤ (coefficient + 1) * (n + 1) ^ exponent := by
    apply max_le <;> nlinarith
  have h := Nat.mul_le_mul_right (vocabulary tapes State Symbol)
    (MultitapeMatrix.event_polynomial_bound machine anchor (max 1 time) n (coefficient + 1) exponent (Nat.le_max_left _ _) ht)
  simpa only [Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

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
  simp_rw [transcript_eq_original]
  exact BinaryMultitapeMatrix.no_readability machine anchor blank bitSymbol inputTape outputTape cells decode
    generator secure monitor coefficient exponent time_bound

theorem one_layer (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).architecture.layers = 1 := rfl

theorem heads_fixed (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).architecture.heads =
      EncryptedMatrix.headCount 2 (2 * vocabulary tapes State Symbol) locality := rfl

theorem precision_fixed (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).parameters.scalarBits =
      RoutedMatrix.precision (EncryptedMatrix.packetCount 2 + 1)
        (EncryptedMatrix.headCount 2 (2 * vocabulary tapes State Symbol) locality)
        (EncryptedMatrix.opcodeCount 2 (2 * vocabulary tapes State Symbol)
          (opcodes tapes State Symbol * (vocabulary tapes State Symbol + 1)) locality + 1) := rfl

theorem context_length (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality) :
    (model machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).architecture.contextLength =
      seedLength + 2 * vocabulary tapes State Symbol * eventSteps machine anchor level + 2 * vocabulary tapes State Symbol + 1 := by
  change seedLength + (eventSteps machine anchor level + 2) * vocabulary tapes State Symbol +
    (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) = _
  ring

def inputCircuit (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :
    Circuit (n + seedLength) ((seedLength + (eventSteps machine anchor level + 2) * vocabulary tapes State Symbol) *
      (EncryptedMatrix.packetCount 2 + 1)) :=
  .bundle fun wire => (inputLiteral machine anchor blank bitSymbol inputTape n seedLength level outputTape cell wire).circuit

theorem inputCircuit_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (input : Bits n) (seed : Bits seedLength) :
    Circuit.eval (inputCircuit machine anchor blank bitSymbol inputTape n seedLength level outputTape cell) (Fin.append input seed) =
      inputEncoding machine anchor blank bitSymbol inputTape level outputTape cell input seed := by
  funext wire
  simp only [inputCircuit, Circuit.eval, Autoregressive.ContextLiteral.eval_circuit]
  exact inputLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cell input seed wire

theorem inputCircuit_depth (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :
    Circuit.depth (inputCircuit machine anchor blank bitSymbol inputTape n seedLength level outputTape cell) ≤ 1 := by
  simp only [inputCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => Autoregressive.ContextLiteral.depth_circuit_le_one _

/-- First-separator transcript of the same native numerical source model,
so the privacy construction also has the paper's concrete information tax. -/
def tokenModel (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality) :=
  ProtocolToken.tokenGenerator (schedule machine anchor blank bitSymbol inputTape n level outputTape cell)
    (transition machine blank outputTape decode) BinarySchedule.tokenBit generator
    (plainPrompt machine anchor blank bitSymbol inputTape level outputTape cell)
    (plainLiteral machine anchor blank bitSymbol inputTape n level outputTape cell)
    (plainLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cell)

theorem tokenModel_answer (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality)
    (input : Bits n) (seed : Bits seedLength) :
    (tokenModel machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).answer (Fin.append input seed) =
      decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine
        (bitTape blank bitSymbol inputTape input))).tape outputTape cell) := by
  have ha := ProtocolToken.answer_correct (schedule machine anchor blank bitSymbol inputTape n level outputTape cell)
    (transition machine blank outputTape decode) BinarySchedule.tokenBit generator
    (plainPrompt machine anchor blank bitSymbol inputTape level outputTape cell)
    (plainLiteral machine anchor blank bitSymbol inputTape n level outputTape cell)
    (plainLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cell) input seed
  have hb := ProtocolEncryptedBinary.output_correct (schedule machine anchor blank bitSymbol inputTape n level outputTape cell)
    (transition machine blank outputTape decode) BinarySchedule.tokenBit generator
    (plainPrompt machine anchor blank bitSymbol inputTape level outputTape cell input) seed
  exact ha.trans (hb.symm.trans (output_correct machine anchor blank bitSymbol inputTape level outputTape cell decode generator input seed))

theorem parity_leakage (tal : Tal.FourierTailTheorem)
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength (eventSteps machine anchor level * vocabulary tapes State Symbol + 1) locality)
    (correct : ∀ input : Bits n, decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine
      (bitTape blank bitSymbol inputTape input))).tape outputTape cell) = Tal.parity input) (hn : 1 ≤ n) :
    let result := tokenModel machine anchor blank bitSymbol inputTape n level outputTape cell decode generator;
    -Real.logb 2 (Real.sqrt (Tal.tailBound result.fiberDepth result.fiberSize n)) - (seedLength : ℝ) ≤
      (FiniteInformation.Distribution.uniform (Bits n × Bits seedLength)).mutualInformation Prod.fst result.seededTrace := by
  apply TokenAutoregressive.Generator.seeded_footprint tal _ _ hn
  intro input seed
  rw [tokenModel_answer]
  exact correct input

end ProtocolMultitapeMatrix
