import EfficientPhase
import ObliviousMatrix

/-!
# The efficient single-tape simulator as an actual numerical Transformer

This composes the complete fixed-control instruction compiler with the
shared-matrix event execution theorem. Initialization copies raw input bits
at static addresses; the input-dependent tape never enters finite control.
The event count, constant alphabet/precision, and polynomial matrix size
are properties of this same constructed model.
-/

noncomputable section
namespace EfficientMatrix
open TransformerAC0 ObliviousPhase

variable {State Symbol : Type*} [Fintype State] [Fintype Symbol]

abbrev SimulatorControl (State Symbol : Type*) :=
  ObliviousCopy.Control (LeafStep.Registers State Symbol) (HeadMarker.Cell Symbol)
abbrev SimulatorSymbol (Symbol : Type*) := HeadMarker.Cell Symbol

def events (machine : Machine State Symbol) (level : ℕ) : ℕ :=
  (EfficientPhase.instructions machine level level 0).length

omit [Fintype State] [Fintype Symbol] in
theorem events_positive (machine : Machine State Symbol) (level : ℕ) : 0 < events machine level := by
  have h := EfficientPhase.instruction_count machine level level 0
  have hp : 1 ≤ 2 ^ level := Nat.one_le_pow _ _ (by decide)
  unfold events
  nlinarith

def eventSteps (machine : Machine State Symbol) (level : ℕ) : ℕ := events machine level - 1

omit [Fintype State] [Fintype Symbol] in
theorem eventSteps_succ (machine : Machine State Symbol) (level : ℕ) :
    eventSteps machine level + 1 = events machine level := by
  have h := events_positive machine level
  unfold eventSteps
  omega

def matrixModel (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n level : ℕ) (finish : State → Bool) :
    CausalAutoregressive.Model
      (RoutedMatrix.architecture
        (ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol))
        (ObliviousMatrix.window (eventSteps machine level)) 2
        (ObliviousMatrix.opcodes (SimulatorControl State Symbol) (SimulatorSymbol Symbol)))
      (ObliviousMatrix.front (eventSteps machine level)) (eventSteps machine level) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl State Symbol) := ⟨EfficientPhase.initialControl machine blank⟩
  ObliviousMatrix.model (EfficientPhase.bitProgram machine blank bitSymbol n level) (eventSteps machine level)
    (fun control => finish control.auxiliary.state)

def symbolicPrompt (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (input : Bits n) :
    Fin (ObliviousMatrix.front (eventSteps machine level)) →
      Fin (ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol)) :=
  ObliviousMatrix.prompt (EfficientPhase.bitProgram machine blank bitSymbol n level) (eventSteps machine level) input

def inputEncoding (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (input : Bits n) := RoutedMatrix.promptInput (symbolicPrompt machine blank bitSymbol level input)

/-- End-to-end source computation by the constructed one-layer numerical
Transformer, not by the older attention/local-function record. -/
theorem matrix_output (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (finish : State → Bool) (input : Bits n) :
    (matrixModel machine blank bitSymbol n level finish).answer (inputEncoding machine blank bitSymbol level input) =
      finish (machine.run (2 ^ level)
        (EfficientPhase.sourceInitial machine (EfficientPhase.bitTape blank bitSymbol input))).state := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl State Symbol) := ⟨EfficientPhase.initialControl machine blank⟩
  change (ObliviousMatrix.model (EfficientPhase.bitProgram machine blank bitSymbol n level)
    (eventSteps machine level) (fun control => finish control.auxiliary.state)).answer
    (RoutedMatrix.promptInput (ObliviousMatrix.prompt (EfficientPhase.bitProgram machine blank bitSymbol n level)
      (eventSteps machine level) input)) = _
  rw [ObliviousMatrix.output_correct, eventSteps_succ]
  exact congrArg finish (EfficientPhase.bitProgram_correct machine blank bitSymbol level input).1

theorem padded_matrix_output (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (steps : ℕ) (finish : State → Bool) (input : Bits n)
    (terminal : ∀ symbol, machine.transition
      (machine.run steps (EfficientPhase.sourceInitial machine (EfficientPhase.bitTape blank bitSymbol input))).state symbol =
      ((machine.run steps (EfficientPhase.sourceInitial machine (EfficientPhase.bitTape blank bitSymbol input))).state,
        symbol, Direction.stay)) :
    (matrixModel machine blank bitSymbol n (horizonLevel steps) finish).answer
      (inputEncoding machine blank bitSymbol (horizonLevel steps) input) =
      finish (machine.run steps (EfficientPhase.sourceInitial machine (EfficientPhase.bitTape blank bitSymbol input))).state := by
  rw [matrix_output, EfficientPhase.terminal_run_after machine _ steps _ (horizon_covers steps) terminal]

omit [Fintype State] [Fintype Symbol] in
/-- The token count is derived from the expanded fixed-address instruction
list. It is not a complexity premise supplied to the matrix simulator. -/
theorem generated_count_bound (machine : Machine State Symbol) (steps : ℕ) (hsteps : 1 ≤ steps) :
    eventSteps machine (horizonLevel steps) + 1 ≤ 992 * steps * (Nat.log 2 steps + 1) := by
  rw [eventSteps_succ]
  exact EfficientPhase.horizon_instruction_count machine steps 0 hsteps

omit [Fintype State] [Fintype Symbol] in
theorem context_count_bound (machine : Machine State Symbol) (steps : ℕ) (hsteps : 1 ≤ steps) :
    ObliviousMatrix.window (eventSteps machine (horizonLevel steps)) ≤
      1984 * steps * (Nat.log 2 steps + 1) := by
  have he := generated_count_bound machine steps hsteps
  unfold ObliviousMatrix.window
  nlinarith

theorem vocabulary_fixed : ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol) =
    36 * Fintype.card State * Fintype.card Symbol ^ 2 + 2 * Fintype.card Symbol +
      72 * Fintype.card State * Fintype.card Symbol ^ 3 := by
  rw [ObliviousMatrix.vocabulary_card]
  simp only [SimulatorControl, SimulatorSymbol]
  rw [ObliviousCopy.control_card, LeafStep.registers_card]
  simp only [HeadMarker.Cell, Fintype.card_prod, Fintype.card_bool]
  ring

def bitLiteral (zero one : Bool) (wire : Fin n) : Autoregressive.ContextLiteral n :=
  if zero = one then .constant zero else if one then .positive wire else .negative wire

theorem eval_bitLiteral (zero one : Bool) (wire : Fin n) (input : Bits n) :
    (bitLiteral zero one wire).eval input = if input wire then one else zero := by
  cases zero <;> cases one <;> cases h : input wire <;>
    simp [bitLiteral, Autoregressive.ContextLiteral.eval, h]

def tapeLiteral (blank : Symbol) (bitSymbol : Bool → Symbol) (n : ℕ) (address : RotationProgram.Address)
    (predicate : HeadMarker.Cell Symbol → Bool) : Autoregressive.ContextLiteral n :=
  match address with
  | .inl cell =>
      if hcell : 0 ≤ cell ∧ cell < (n : ℤ) then
        bitLiteral (predicate (bitSymbol false, decide (cell = 0)))
          (predicate (bitSymbol true, decide (cell = 0))) ⟨cell.toNat, by have h := hcell.2; omega⟩
      else .constant (predicate (blank, decide (cell = 0)))
  | .inr _ => .constant (predicate (blank, false))

omit [Fintype Symbol] in
/-- Every initial-memory observation is a constant or one raw input literal,
even if the Boolean symbol encoding is noninjective. -/
theorem eval_tapeLiteral (blank : Symbol) (bitSymbol : Bool → Symbol) (input : Bits n)
    (address : RotationProgram.Address) (predicate : HeadMarker.Cell Symbol → Bool) :
    (tapeLiteral blank bitSymbol n address predicate).eval input =
      predicate (EfficientPhase.initialMemory blank (EfficientPhase.bitTape blank bitSymbol input) address) := by
  cases address with
  | inl cell =>
      unfold tapeLiteral EfficientPhase.initialMemory EfficientPhase.bitTape
      dsimp only
      split_ifs with hcell
      · rw [eval_bitLiteral]
        cases h : input ⟨cell.toNat, by have hc := hcell.2; omega⟩ <;> simp only [h, Bool.false_eq_true, if_false, if_true]
      · rfl
  | inr cell => rfl

def inputLiteral (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n level : ℕ) :
    Fin (ObliviousMatrix.front (eventSteps machine level) *
      ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol)) →
        Autoregressive.ContextLiteral n := fun wire =>
  let pt := finProdFinEquiv.symm wire
  Fin.cases (.constant (decide (pt.2 = ObliviousMatrix.tokenCode (.inl (EfficientPhase.initialControl machine blank)))))
    (fun time => tapeLiteral blank bitSymbol n
      ((EfficientPhase.bitProgram machine blank bitSymbol n level).position time.val)
      (fun value => decide (pt.2 = ObliviousMatrix.tokenCode (.inr (.inl value))))) pt.1

theorem inputEncoding_literal (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (input : Bits n) (wire : Fin (ObliviousMatrix.front (eventSteps machine level) *
      ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol))) :
    (inputLiteral machine blank bitSymbol n level wire).eval input =
      inputEncoding machine blank bitSymbol level input wire := by
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [inputLiteral, inputEncoding, RoutedMatrix.promptInput, Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun time => ?_) position
  · simp only [Fin.cases_zero, Autoregressive.ContextLiteral.eval, symbolicPrompt,
      ObliviousMatrix.prompt, EfficientPhase.bitProgram, ObliviousCopy.program]
  · simp only [Fin.cases_succ, eval_tapeLiteral, symbolicPrompt, ObliviousMatrix.prompt]
    rfl

/-- The raw-input adapter is an explicit depth-one literal circuit. It
cannot perform hidden source simulation while preparing the prompt. -/
def inputCircuit (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n level : ℕ) : Circuit n (ObliviousMatrix.front (eventSteps machine level) *
      ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol)) :=
  .bundle fun wire => (inputLiteral machine blank bitSymbol n level wire).circuit

theorem inputCircuit_correct (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (input : Bits n) : Circuit.eval (inputCircuit machine blank bitSymbol n level) input =
      inputEncoding machine blank bitSymbol level input := by
  funext wire
  simp only [inputCircuit, Circuit.eval, Autoregressive.ContextLiteral.eval_circuit]
  exact inputEncoding_literal machine blank bitSymbol level input wire

theorem inputCircuit_depth (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n level : ℕ) : Circuit.depth (inputCircuit machine blank bitSymbol n level) ≤ 1 := by
  simp only [inputCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => Autoregressive.ContextLiteral.depth_circuit_le_one _

omit [Fintype State] [Fintype Symbol] in
theorem context_polynomial_bound (machine : Machine State Symbol) (steps n coefficient exponent : ℕ)
    (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent) :
    ObliviousMatrix.window (eventSteps machine (horizonLevel steps)) ≤
      1984 * (coefficient + 1) ^ 2 * (n + 1) ^ (2 * exponent) := by
  have hcontext := context_count_bound machine steps hsteps
  have hlog := Nat.log_le_self 2 steps
  have hq : 1 ≤ (n + 1) ^ exponent := Nat.one_le_pow _ _ (by omega)
  have ht : steps ≤ (coefficient + 1) * (n + 1) ^ exponent := by nlinarith
  have hsucc : steps + 1 ≤ (coefficient + 1) * (n + 1) ^ exponent := by nlinarith
  calc
    _ ≤ 1984 * steps * (Nat.log 2 steps + 1) := hcontext
    _ ≤ 1984 * steps * (steps + 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 1984 * ((coefficient + 1) * (n + 1) ^ exponent) *
        ((coefficient + 1) * (n + 1) ^ exponent) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hsucc
    _ = _ := by rw [Nat.mul_comm 2 exponent, Nat.pow_mul]; ring

def dimensionConstant (State Symbol : Type*) [Fintype State] [Fintype Symbol] : ℕ :=
  RoutedMatrix.dimensionConstant (ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol))
    2 (ObliviousMatrix.opcodes (SimulatorControl State Symbol) (SimulatorSymbol Symbol))

theorem matrix_precision_fixed (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n level : ℕ) (finish : State → Bool) :
    (matrixModel machine blank bitSymbol n level finish).parameters.scalarBits =
      RoutedMatrix.precision (ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol))
        2 (ObliviousMatrix.opcodes (SimulatorControl State Symbol) (SimulatorSymbol Symbol)) := rfl

theorem dimension_polynomial_bound (machine : Machine State Symbol) (steps n coefficient exponent : ℕ)
    (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent) :
    (RoutedMatrix.architecture
      (ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol))
      (ObliviousMatrix.window (eventSteps machine (horizonLevel steps))) 2
      (ObliviousMatrix.opcodes (SimulatorControl State Symbol) (SimulatorSymbol Symbol))).hiddenWidth ≤
      (2 * dimensionConstant State Symbol * (1984 * (coefficient + 1) ^ 2 + 1)) * (n + 1) ^ (2 * exponent) := by
  have hw := context_polynomial_bound machine steps n coefficient exponent hsteps htime
  have hp : 1 ≤ (n + 1) ^ (2 * exponent) := Nat.one_le_pow _ _ (by omega)
  have hw' : ObliviousMatrix.window (eventSteps machine (horizonLevel steps)) + 1 ≤
      (1984 * (coefficient + 1) ^ 2 + 1) * (n + 1) ^ (2 * exponent) := by nlinarith
  exact (RoutedMatrix.hidden_dimension_linear).trans (by
    simpa only [dimensionConstant, Nat.mul_assoc] using Nat.mul_le_mul_left (2 * dimensionConstant State Symbol) hw')

def parameterConstant (State Symbol : Type*) [Fintype State] [Fintype Symbol] : ℕ :=
  3 * ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol) * dimensionConstant State Symbol +
    4 * (3 * 2 + 2) * dimensionConstant State Symbol ^ 2

theorem parameter_polynomial_bound (machine : Machine State Symbol) (steps n coefficient exponent : ℕ)
    (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent) :
    (RoutedMatrix.architecture
      (ObliviousMatrix.vocabulary (SimulatorControl State Symbol) (SimulatorSymbol Symbol))
      (ObliviousMatrix.window (eventSteps machine (horizonLevel steps))) 2
      (ObliviousMatrix.opcodes (SimulatorControl State Symbol) (SimulatorSymbol Symbol))).parameterCount ≤
      (parameterConstant State Symbol * (1984 * (coefficient + 1) ^ 2 + 1) ^ 2) * (n + 1) ^ (4 * exponent) := by
  have hw := context_polynomial_bound machine steps n coefficient exponent hsteps htime
  have hp : 1 ≤ (n + 1) ^ (2 * exponent) := Nat.one_le_pow _ _ (by omega)
  have hw' : ObliviousMatrix.window (eventSteps machine (horizonLevel steps)) + 1 ≤
      (1984 * (coefficient + 1) ^ 2 + 1) * (n + 1) ^ (2 * exponent) := by nlinarith
  calc
    _ ≤ parameterConstant State Symbol * (ObliviousMatrix.window (eventSteps machine (horizonLevel steps)) + 1) ^ 2 :=
      ObliviousMatrix.parameter_count_bound _
    _ ≤ parameterConstant State Symbol *
        ((1984 * (coefficient + 1) ^ 2 + 1) * (n + 1) ^ (2 * exponent)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw' 2)
    _ = _ := by
      rw [Nat.mul_pow, ← Nat.pow_mul, show 2 * exponent * 2 = 4 * exponent by omega]
      ring

end EfficientMatrix
