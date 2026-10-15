import MultitapeMatrix
import EncryptedEfficientMatrix
import EncryptedSerialization

/-!
# On-the-fly encrypted efficient multitape matrix execution

The plaintext program is the proved recursive multitape compiler plus its
final output-cell read. Encryption is carried out by the actual shared
numerical matrix model, and the seed/prompt adapter uses only raw literals.
-/

noncomputable section
namespace EncryptedMultitapeMatrix
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix

variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
variable {n seedLength locality : ℕ}

def model (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine anchor level * vocabulary tapes State Symbol + vocabulary tapes State Symbol) locality) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  EncryptedObliviousMatrix.model (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
    (eventSteps machine anchor level) (fun control => decode (control.auxiliary.scanned outputTape)) generator

def inputEncoding (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (input : Bits n) (seed : Bits seedLength) :=
  RoutedMatrix.promptInput (EncryptedMatrix.prompt (bitPrompt machine anchor blank bitSymbol inputTape level outputTape cell input) seed)

theorem output_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine anchor level * vocabulary tapes State Symbol + vocabulary tapes State Symbol) locality)
    (input : Bits n) (seed : Bits seedLength) :
    (model machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).answer
      (inputEncoding machine anchor blank bitSymbol inputTape level outputTape cell input seed) =
        decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine
          (bitTape blank bitSymbol inputTape input))).tape outputTape cell) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  have he := EncryptedObliviousMatrix.output_correct
    (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
    (eventSteps machine anchor level) (fun control => decode (control.auxiliary.scanned outputTape)) generator input seed
  have h := MultitapeMatrix.bit_output_correct machine anchor blank bitSymbol inputTape level outputTape cell decode input
  exact he.trans (by simpa only [bitModel, bitInput, bitPrompt, ObliviousMatrix.output_correct] using h)

def inputLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :
    Fin ((seedLength + ObliviousMatrix.front (eventSteps machine anchor level)) *
      EncryptedMatrix.packetCount (vocabulary tapes State Symbol)) → Autoregressive.ContextLiteral (n + seedLength) :=
  fun wire =>
    let pair := finProdFinEquiv.symm wire
    Fin.addCases
      (fun index => EfficientMatrix.bitLiteral
        (decide (pair.2 = EncryptedMatrix.seedPacket (vocabulary tapes State Symbol) false))
        (decide (pair.2 = EncryptedMatrix.seedPacket (vocabulary tapes State Symbol) true)) (Fin.natAdd n index))
      (fun position => match EncryptedMatrix.packetCode.symm pair.2 with
        | .inl token => EncryptedEfficientMatrix.liftLiteral
            (MultitapeMatrix.inputLiteral machine anchor blank bitSymbol inputTape n level outputTape cell
              (finProdFinEquiv (position, token)))
        | .inr _ => .constant false) pair.1

theorem inputLiteral_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (input : Bits n) (seed : Bits seedLength)
    (wire : Fin ((seedLength + ObliviousMatrix.front (eventSteps machine anchor level)) *
      EncryptedMatrix.packetCount (vocabulary tapes State Symbol))) :
    (inputLiteral machine anchor blank bitSymbol inputTape n seedLength level outputTape cell wire).eval (Fin.append input seed) =
      inputEncoding machine anchor blank bitSymbol inputTape level outputTape cell input seed wire := by
  obtain ⟨⟨position, packet⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [inputLiteral, inputEncoding, RoutedMatrix.promptInput, Equiv.symm_apply_apply]
  refine Fin.addCases (fun index => ?_) (fun index => ?_) position
  · simp only [Fin.addCases_left, EfficientMatrix.eval_bitLiteral, Fin.append_right]
    cases h : seed index <;> simp [EncryptedMatrix.prompt, h]
  · simp only [Fin.addCases_right]
    obtain ⟨value, rfl⟩ := EncryptedMatrix.packetCode.surjective packet
    cases value with
    | inl token =>
        simp only [Equiv.symm_apply_apply, EncryptedEfficientMatrix.eval_liftLiteral, MultitapeMatrix.inputLiteral_correct]
        simp [bitInput, RoutedMatrix.promptInput, EncryptedMatrix.prompt, EncryptedMatrix.plainPacket]
    | inr value =>
        simp [Autoregressive.ContextLiteral.eval, EncryptedMatrix.prompt, EncryptedMatrix.plainPacket]

def inputCircuit (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n seedLength level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :=
  Circuit.bundle fun wire => (inputLiteral machine anchor blank bitSymbol inputTape n seedLength level outputTape cell wire).circuit

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

def transcript (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine anchor level * vocabulary tapes State Symbol + vocabulary tapes State Symbol) locality)
    (input : Bits n) (seed : Bits seedLength) : Bits (eventSteps machine anchor level * vocabulary tapes State Symbol) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  EncryptedMatrix.transcript
    (EncryptedObliviousMatrix.schedule (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell)
      (eventSteps machine anchor level)) ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition
    (ObliviousMatrix.label (fun control => decode (control.auxiliary.scanned outputTape))) generator
    (bitPrompt machine anchor blank bitSymbol inputTape level outputTape cell input) seed

theorem ciphertext_polynomial_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (steps n coefficient exponent : ℕ) (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent) :
    eventSteps machine anchor (horizonLevel steps) * vocabulary tapes State Symbol ≤
      (((4 * (248 * tapes + 1)) * (coefficient + 1) ^ 2) * vocabulary tapes State Symbol) * (n + 1) ^ (2 * exponent) := by
  have h := Nat.mul_le_mul_right (vocabulary tapes State Symbol)
    (MultitapeMatrix.event_polynomial_bound machine anchor steps n coefficient exponent hsteps htime)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Privacy of the actual emitted ciphertext, with its polynomial length
derived from the source time bound and the proved multitape compiler. -/
theorem no_readability {seedLengths times : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ℕ → ℤ) (decode : Symbol → Bool)
    (generator : NC0GeneratorFamily seedLengths
      (fun n => eventSteps machine anchor (horizonLevel (times n)) * vocabulary tapes State Symbol + vocabulary tapes State Symbol))
    (secure : generator.IsPseudorandom)
    (monitor : PolynomialMonitorFamily
      (fun n => eventSteps machine anchor (horizonLevel (times n)) * vocabulary tapes State Symbol))
    (coefficient exponent : ℕ) (time_positive : ∀ n, 1 ≤ times n)
    (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => transcript machine anchor blank bitSymbol inputTape (horizonLevel (times n)) outputTape (cells n) decode
          (generator.generator n) input seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  exact EncryptedObliviousMatrix.no_readability
    (fun n => bitProgram machine anchor blank bitSymbol inputTape n (horizonLevel (times n)) outputTape (cells n))
    (fun control => decode (control.auxiliary.scanned outputTape)) generator secure monitor
    (((4 * (248 * tapes + 1)) * (coefficient + 1) ^ 2) * vocabulary tapes State Symbol) (2 * exponent)
    (fun n => ciphertext_polynomial_bound machine anchor (times n) n coefficient exponent (time_positive n) (time_bound n))

theorem precision_fixed (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine anchor level * vocabulary tapes State Symbol + vocabulary tapes State Symbol) locality) :
    (model machine anchor blank bitSymbol inputTape n level outputTape cell decode generator).parameters.scalarBits =
      RoutedMatrix.precision (EncryptedMatrix.packetCount (vocabulary tapes State Symbol))
        (EncryptedMatrix.headCount (vocabulary tapes State Symbol) 2 locality)
        (EncryptedMatrix.opcodeCount (vocabulary tapes State Symbol) 2 (opcodes tapes State Symbol) locality) := rfl

end EncryptedMultitapeMatrix
