import EncryptedObliviousMatrix
import EfficientMatrix

/-!
# Efficient source computation with on-the-fly matrix encryption

This uses the expanded single-tape phase compiler, not the configuration-
in-control shortcut. The encrypted model shares one numerical parameter
set across growing contexts. Its initialization is a depth-one raw input
and raw seed adapter, and encryption does not add generation events.
-/

noncomputable section
namespace EncryptedEfficientMatrix
open TransformerAC0 Encryption ObliviousPhase EfficientMatrix

variable {State Symbol : Type*} [Fintype State] [Fintype Symbol]
variable {n seedLength locality : ℕ}

abbrev vocabulary (State Symbol : Type*) [Fintype State] [Fintype Symbol] :=
  ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol)
abbrev opcodes (State Symbol : Type*) [Fintype State] [Fintype Symbol] :=
  ObliviousMatrix.opcodes (SimulatorControl State Symbol) (SimulatorSymbol Symbol)

def matrixModel (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n level : ℕ) (finish : State → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine level * vocabulary State Symbol + vocabulary State Symbol) locality) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl State Symbol) := ⟨EfficientPhase.initialControl machine blank⟩
  EncryptedObliviousMatrix.model (EfficientPhase.bitProgram machine blank bitSymbol n level)
    (eventSteps machine level) (fun control => finish control.auxiliary.state) generator

def inputEncoding (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (input : Bits n) (seed : Bits seedLength) :=
  RoutedMatrix.promptInput (EncryptedMatrix.prompt (symbolicPrompt machine blank bitSymbol level input) seed)

theorem matrix_output (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (finish : State → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine level * vocabulary State Symbol + vocabulary State Symbol) locality)
    (input : Bits n) (seed : Bits seedLength) :
    (matrixModel machine blank bitSymbol n level finish generator).answer
      (inputEncoding machine blank bitSymbol level input seed) =
        finish (machine.run (2 ^ level)
          (EfficientPhase.sourceInitial machine (EfficientPhase.bitTape blank bitSymbol input))).state := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl State Symbol) := ⟨EfficientPhase.initialControl machine blank⟩
  change (EncryptedObliviousMatrix.model (EfficientPhase.bitProgram machine blank bitSymbol n level)
    (eventSteps machine level) (fun control => finish control.auxiliary.state) generator).answer
      (EncryptedObliviousMatrix.inputEncoding (EfficientPhase.bitProgram machine blank bitSymbol n level)
        (eventSteps machine level) input seed) = _
  rw [EncryptedObliviousMatrix.output_correct, eventSteps_succ]
  exact congrArg finish (EfficientPhase.bitProgram_correct machine blank bitSymbol level input).1

theorem padded_matrix_output (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (steps : ℕ) (finish : State → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine (horizonLevel steps) * vocabulary State Symbol + vocabulary State Symbol) locality)
    (input : Bits n) (seed : Bits seedLength)
    (terminal : ∀ symbol, machine.transition
      (machine.run steps (EfficientPhase.sourceInitial machine (EfficientPhase.bitTape blank bitSymbol input))).state symbol =
      ((machine.run steps (EfficientPhase.sourceInitial machine (EfficientPhase.bitTape blank bitSymbol input))).state,
        symbol, Direction.stay)) :
    (matrixModel machine blank bitSymbol n (horizonLevel steps) finish generator).answer
      (inputEncoding machine blank bitSymbol (horizonLevel steps) input seed) =
        finish (machine.run steps (EfficientPhase.sourceInitial machine (EfficientPhase.bitTape blank bitSymbol input))).state := by
  rw [matrix_output, EfficientPhase.terminal_run_after machine _ steps _ (horizon_covers steps) terminal]

def liftLiteral (literal : Autoregressive.ContextLiteral n) : Autoregressive.ContextLiteral (n + seedLength) :=
  match literal with
  | .constant bit => .constant bit
  | .positive index => .positive (Fin.castAdd seedLength index)
  | .negative index => .negative (Fin.castAdd seedLength index)

theorem eval_liftLiteral (literal : Autoregressive.ContextLiteral n) (input : Bits n) (seed : Bits seedLength) :
    (liftLiteral literal).eval (Fin.append input seed) = literal.eval input := by
  cases literal <;> simp [liftLiteral, Autoregressive.ContextLiteral.eval]

def inputLiteral (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n seedLength level : ℕ) :
    Fin ((seedLength + ObliviousMatrix.front (eventSteps machine level)) *
      EncryptedMatrix.packetCount (vocabulary State Symbol)) → Autoregressive.ContextLiteral (n + seedLength) :=
  fun wire =>
    let pair := finProdFinEquiv.symm wire
    Fin.addCases
      (fun index => bitLiteral
        (decide (pair.2 = EncryptedMatrix.seedPacket (vocabulary State Symbol) false))
        (decide (pair.2 = EncryptedMatrix.seedPacket (vocabulary State Symbol) true)) (Fin.natAdd n index))
      (fun position => match EncryptedMatrix.packetCode.symm pair.2 with
        | .inl token => liftLiteral (EfficientMatrix.inputLiteral machine blank bitSymbol n level
            (finProdFinEquiv (position, token)))
        | .inr _ => .constant false) pair.1

theorem inputEncoding_literal (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (input : Bits n) (seed : Bits seedLength)
    (wire : Fin ((seedLength + ObliviousMatrix.front (eventSteps machine level)) *
      EncryptedMatrix.packetCount (vocabulary State Symbol))) :
    (inputLiteral machine blank bitSymbol n seedLength level wire).eval (Fin.append input seed) =
      inputEncoding machine blank bitSymbol level input seed wire := by
  obtain ⟨⟨position, packet⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [inputLiteral, inputEncoding, RoutedMatrix.promptInput, Equiv.symm_apply_apply]
  refine Fin.addCases (fun index => ?_) (fun index => ?_) position
  · simp only [Fin.addCases_left, eval_bitLiteral, Fin.append_right]
    cases h : seed index <;> simp [EncryptedMatrix.prompt, h]
  · simp only [Fin.addCases_right]
    obtain ⟨value, rfl⟩ := EncryptedMatrix.packetCode.surjective packet
    cases value with
    | inl token =>
        simp only [Equiv.symm_apply_apply, eval_liftLiteral, EfficientMatrix.inputEncoding_literal]
        simp [EfficientMatrix.inputEncoding, RoutedMatrix.promptInput, EncryptedMatrix.prompt,
          EncryptedMatrix.plainPacket]
    | inr value =>
        simp [Autoregressive.ContextLiteral.eval, EncryptedMatrix.prompt, EncryptedMatrix.plainPacket]

def inputCircuit (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n seedLength level : ℕ) := Circuit.bundle fun wire =>
  (inputLiteral machine blank bitSymbol n seedLength level wire).circuit

theorem inputCircuit_correct (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (input : Bits n) (seed : Bits seedLength) :
    Circuit.eval (inputCircuit machine blank bitSymbol n seedLength level) (Fin.append input seed) =
      inputEncoding machine blank bitSymbol level input seed := by
  funext wire
  simp only [inputCircuit, Circuit.eval, Autoregressive.ContextLiteral.eval_circuit]
  exact inputEncoding_literal machine blank bitSymbol level input seed wire

theorem inputCircuit_depth (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n seedLength level : ℕ) : Circuit.depth (inputCircuit machine blank bitSymbol n seedLength level) ≤ 1 := by
  simp only [inputCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => Autoregressive.ContextLiteral.depth_circuit_le_one _

theorem inputCircuit_size (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n seedLength level : ℕ) : Circuit.gateCount (inputCircuit machine blank bitSymbol n seedLength level) ≤
      (seedLength + ObliviousMatrix.front (eventSteps machine level)) * EncryptedMatrix.packetCount (vocabulary State Symbol) := by
  simp only [inputCircuit, Circuit.gateCount]
  calc
    _ ≤ ∑ _wire : Fin ((seedLength + ObliviousMatrix.front (eventSteps machine level)) *
        EncryptedMatrix.packetCount (vocabulary State Symbol)), 1 :=
      Finset.sum_le_sum fun _ _ => Autoregressive.ContextLiteral.gateCount_circuit_le_one _
    _ = _ := by simp

theorem matrix_precision_fixed (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n level : ℕ) (finish : State → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine level * vocabulary State Symbol + vocabulary State Symbol) locality) :
    (matrixModel machine blank bitSymbol n level finish generator).parameters.scalarBits =
      RoutedMatrix.precision (EncryptedMatrix.packetCount (vocabulary State Symbol))
        (EncryptedMatrix.headCount (vocabulary State Symbol) 2 locality)
        (EncryptedMatrix.opcodeCount (vocabulary State Symbol) 2 (opcodes State Symbol) locality) := rfl

omit [Fintype State] [Fintype Symbol] in
theorem generated_count_bound (machine : Machine State Symbol) (steps : ℕ) (hsteps : 1 ≤ steps) :
    eventSteps machine (horizonLevel steps) + 1 ≤ 992 * steps * (Nat.log 2 steps + 1) :=
  EfficientMatrix.generated_count_bound machine steps hsteps

def transcript (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (finish : State → Bool)
    (generator : LocalGenerator seedLength
      (eventSteps machine level * vocabulary State Symbol + vocabulary State Symbol) locality)
    (input : Bits n) (seed : Bits seedLength) : Bits (eventSteps machine level * vocabulary State Symbol) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl State Symbol) := ⟨EfficientPhase.initialControl machine blank⟩
  EncryptedMatrix.transcript
    (EncryptedObliviousMatrix.schedule (EfficientPhase.bitProgram machine blank bitSymbol n level) (eventSteps machine level))
    ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition
    (ObliviousMatrix.label (fun control => finish control.auxiliary.state)) generator
    (symbolicPrompt machine blank bitSymbol level input) seed

theorem ciphertext_count_bound (machine : Machine State Symbol) (steps : ℕ) (hsteps : 1 ≤ steps) :
    eventSteps machine (horizonLevel steps) * vocabulary State Symbol ≤
      (992 * vocabulary State Symbol) * steps * (Nat.log 2 steps + 1) := by
  have he := generated_count_bound machine steps hsteps
  nlinarith

theorem ciphertext_polynomial_bound (machine : Machine State Symbol) (steps n coefficient exponent : ℕ)
    (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent) :
    eventSteps machine (horizonLevel steps) * vocabulary State Symbol ≤
      (1984 * (coefficient + 1) ^ 2 * vocabulary State Symbol) * (n + 1) ^ (2 * exponent) := by
  have hc := EfficientMatrix.context_polynomial_bound machine steps n coefficient exponent hsteps htime
  have he : eventSteps machine (horizonLevel steps) ≤ ObliviousMatrix.window (eventSteps machine (horizonLevel steps)) := by
    unfold ObliviousMatrix.window
    omega
  calc
    _ ≤ ObliviousMatrix.window (eventSteps machine (horizonLevel steps)) * vocabulary State Symbol :=
      Nat.mul_le_mul_right _ he
    _ ≤ (1984 * (coefficient + 1) ^ 2 * (n + 1) ^ (2 * exponent)) * vocabulary State Symbol :=
      Nat.mul_le_mul_right _ hc
    _ = _ := by ring

/-- Security for the actual ciphertext generation, with the polynomial
trace-size condition derived from source running time. -/
theorem no_readability
    {seedLengths times : ℕ → ℕ}
    (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol) (finish : State → Bool)
    (generator : NC0GeneratorFamily seedLengths
      (fun n => eventSteps machine (horizonLevel (times n)) * vocabulary State Symbol + vocabulary State Symbol))
    (secure : generator.IsPseudorandom)
    (monitor : PolynomialMonitorFamily
      (fun n => eventSteps machine (horizonLevel (times n)) * vocabulary State Symbol))
    (coefficient exponent : ℕ) (time_positive : ∀ n, 1 ≤ times n)
    (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => transcript machine blank bitSymbol (horizonLevel (times n)) finish
          (generator.generator n) input seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl State Symbol) := ⟨EfficientPhase.initialControl machine blank⟩
  exact EncryptedObliviousMatrix.no_readability
    (fun n => EfficientPhase.bitProgram machine blank bitSymbol n (horizonLevel (times n)))
    (fun control => finish control.auxiliary.state) generator secure monitor
    (1984 * (coefficient + 1) ^ 2 * vocabulary State Symbol) (2 * exponent)
    (fun n => ciphertext_polynomial_bound machine (times n) n coefficient exponent (time_positive n) (time_bound n))

def dimensionConstant (State Symbol : Type*) [Fintype State] [Fintype Symbol] (locality : ℕ) : ℕ :=
  RoutedMatrix.dimensionConstant (EncryptedMatrix.packetCount (vocabulary State Symbol))
    (EncryptedMatrix.headCount (vocabulary State Symbol) 2 locality)
    (EncryptedMatrix.opcodeCount (vocabulary State Symbol) 2 (opcodes State Symbol) locality)

def parameterConstant (State Symbol : Type*) [Fintype State] [Fintype Symbol] (locality : ℕ) : ℕ :=
  3 * EncryptedMatrix.packetCount (vocabulary State Symbol) * dimensionConstant State Symbol locality +
    4 * (3 * EncryptedMatrix.headCount (vocabulary State Symbol) 2 locality + 2) *
      dimensionConstant State Symbol locality ^ 2

omit [Fintype State] [Fintype Symbol] in
theorem context_polynomial_bound (machine : Machine State Symbol) (steps n coefficient exponent seedCoefficient : ℕ)
    (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent)
    (hseed : seedLength ≤ seedCoefficient * (n + 1) ^ (2 * exponent)) :
    seedLength + ObliviousMatrix.front (eventSteps machine (horizonLevel steps)) +
      eventSteps machine (horizonLevel steps) ≤
        (seedCoefficient + 1984 * (coefficient + 1) ^ 2) * (n + 1) ^ (2 * exponent) := by
  have hw := EfficientMatrix.context_polynomial_bound machine steps n coefficient exponent hsteps htime
  unfold ObliviousMatrix.front ObliviousMatrix.window at *
  nlinarith

theorem dimension_polynomial_bound (machine : Machine State Symbol) (steps n coefficient exponent seedCoefficient locality : ℕ)
    (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent)
    (hseed : seedLength ≤ seedCoefficient * (n + 1) ^ (2 * exponent)) :
    (RoutedMatrix.architecture (EncryptedMatrix.packetCount (vocabulary State Symbol))
      (seedLength + ObliviousMatrix.front (eventSteps machine (horizonLevel steps)) +
        eventSteps machine (horizonLevel steps))
      (EncryptedMatrix.headCount (vocabulary State Symbol) 2 locality)
      (EncryptedMatrix.opcodeCount (vocabulary State Symbol) 2 (opcodes State Symbol) locality)).hiddenWidth ≤
        (2 * dimensionConstant State Symbol locality *
          (seedCoefficient + 1984 * (coefficient + 1) ^ 2 + 1)) * (n + 1) ^ (2 * exponent) := by
  have hw := context_polynomial_bound machine steps n coefficient exponent seedCoefficient hsteps htime hseed
  have hp : 1 ≤ (n + 1) ^ (2 * exponent) := Nat.one_le_pow _ _ (by omega)
  have hw' : seedLength + ObliviousMatrix.front (eventSteps machine (horizonLevel steps)) +
      eventSteps machine (horizonLevel steps) + 1 ≤
        (seedCoefficient + 1984 * (coefficient + 1) ^ 2 + 1) * (n + 1) ^ (2 * exponent) := by nlinarith
  exact (RoutedMatrix.hidden_dimension_linear).trans (by
    simpa only [dimensionConstant, Nat.mul_assoc] using
      Nat.mul_le_mul_left (2 * dimensionConstant State Symbol locality) hw')

theorem parameter_polynomial_bound (machine : Machine State Symbol) (steps n coefficient exponent seedCoefficient locality : ℕ)
    (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent)
    (hseed : seedLength ≤ seedCoefficient * (n + 1) ^ (2 * exponent)) :
    (RoutedMatrix.architecture (EncryptedMatrix.packetCount (vocabulary State Symbol))
      (seedLength + ObliviousMatrix.front (eventSteps machine (horizonLevel steps)) +
        eventSteps machine (horizonLevel steps))
      (EncryptedMatrix.headCount (vocabulary State Symbol) 2 locality)
      (EncryptedMatrix.opcodeCount (vocabulary State Symbol) 2 (opcodes State Symbol) locality)).parameterCount ≤
        (parameterConstant State Symbol locality *
          (seedCoefficient + 1984 * (coefficient + 1) ^ 2 + 1) ^ 2) * (n + 1) ^ (4 * exponent) := by
  have hw := context_polynomial_bound machine steps n coefficient exponent seedCoefficient hsteps htime hseed
  have hp : 1 ≤ (n + 1) ^ (2 * exponent) := Nat.one_le_pow _ _ (by omega)
  have hw' : seedLength + ObliviousMatrix.front (eventSteps machine (horizonLevel steps)) +
      eventSteps machine (horizonLevel steps) + 1 ≤
        (seedCoefficient + 1984 * (coefficient + 1) ^ 2 + 1) * (n + 1) ^ (2 * exponent) := by nlinarith
  calc
    _ ≤ parameterConstant State Symbol locality *
        (seedLength + ObliviousMatrix.front (eventSteps machine (horizonLevel steps)) +
          eventSteps machine (horizonLevel steps) + 1) ^ 2 := RoutedMatrix.parameter_count_quadratic
    _ ≤ parameterConstant State Symbol locality *
        ((seedCoefficient + 1984 * (coefficient + 1) ^ 2 + 1) * (n + 1) ^ (2 * exponent)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw' 2)
    _ = _ := by
      rw [Nat.mul_pow, ← Nat.pow_mul, show 2 * exponent * 2 = 4 * exponent by omega]
      ring

end EncryptedEfficientMatrix
