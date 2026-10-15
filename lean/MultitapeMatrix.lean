import MultitapeEfficientPhase
import ObliviousMatrix
import EfficientMatrix

/-!
# Efficient multitape computation by actual shared numerical matrices

The model executes the expanded fixed-address multitape compiler, followed
by one local read of the requested output tape cell. Its final greedy token
therefore contains that actual computed symbol. Initialization copies only
constants and raw Boolean literals; no source computation is preprocessed.
-/

noncomputable section
namespace MultitapeMatrix
open TransformerAC0 ObliviousProgram ObliviousCopy ObliviousPhase MultitapeLeaf

variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]

abbrev SimulatorControl (tapes : ℕ) (State Symbol : Type*) := Control (Registers tapes State Symbol) (HeadMarker.Cell Symbol)
abbrev SimulatorSymbol (Symbol : Type*) := HeadMarker.Cell Symbol
abbrev vocabulary (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] :=
  ObliviousMatrix.vocabulary (SimulatorControl tapes State Symbol) (SimulatorSymbol Symbol)
abbrev opcodes (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] :=
  ObliviousMatrix.opcodes (SimulatorControl tapes State Symbol) (SimulatorSymbol Symbol)

def eventSteps (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (level : ℕ) : ℕ :=
  (MultitapeEfficientPhase.instructions machine anchor level level 0).length

def readout (outputTape : Fin tapes) (cell : ℤ) : StepInstruction tapes State Symbol :=
  .read (outputTape, Sum.inl cell) (fun control symbol =>
    { control with auxiliary := { control.auxiliary with scanned := Function.update control.auxiliary.scanned outputTape symbol.1 } })

def program (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :=
  ObliviousCopy.program (MultitapeEfficientPhase.instructions machine anchor level level 0 ++ [readout outputTape cell])
    (anchor, Sum.inl 0) (MultitapeEfficientPhase.initialControl machine blank) (MultitapeEfficientPhase.initialMemory blank)

def matrixModel (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  ObliviousMatrix.model (program machine anchor blank level outputTape cell) (eventSteps machine anchor level)
    (fun control => decode (control.auxiliary.scanned outputTape))

def inputEncoding (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (tape : Fin tapes → ℤ → Symbol) :=
  RoutedMatrix.promptInput (ObliviousMatrix.prompt (program machine anchor blank level outputTape cell)
    (eventSteps machine anchor level) tape)

omit [Fintype State] [Fintype Symbol] in
theorem program_final (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (tape : Fin tapes → ℤ → Symbol) :
    (program machine anchor blank level outputTape cell).configurationAt tape (eventSteps machine anchor level + 1) =
      execute (readout outputTape cell) (run (MultitapeEfficientPhase.instructions machine anchor level level 0)
        ⟨MultitapeEfficientPhase.initialControl machine blank, MultitapeEfficientPhase.initialMemory blank tape⟩) := by
  have h := ObliviousCopy.program_complete
    (MultitapeEfficientPhase.instructions machine anchor level level 0 ++ [readout outputTape cell]) (anchor, Sum.inl 0)
    (MultitapeEfficientPhase.initialControl machine blank) (MultitapeEfficientPhase.initialMemory blank) tape
  simpa only [program, eventSteps, List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
    run_append, run_cons, run_nil] using h

/-- The requested source output tape cell is read from the actual final
simulator memory, then labeled by the actual greedy matrix token. -/
theorem output_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool) (tape : Fin tapes → ℤ → Symbol) :
    (matrixModel machine anchor blank level outputTape cell decode).answer
      (inputEncoding machine anchor blank level outputTape cell tape) =
        decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape cell) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  unfold matrixModel inputEncoding
  rw [ObliviousMatrix.output_correct, program_final]
  simp only [execute, readout, Instruction.address, Instruction.nextControl, Function.update_self]
  change decode ((run (MultitapeEfficientPhase.instructions machine anchor level level 0)
    ⟨MultitapeEfficientPhase.initialControl machine blank, MultitapeEfficientPhase.initialMemory blank tape⟩).memory
      (outputTape, Sum.inl cell)).1 = _
  rw [(MultitapeEfficientPhase.source_run_correct machine anchor level level 0 le_rfl
    (MultitapeEfficientPhase.sourceInitial machine tape) _
    (MultitapeEfficientPhase.initial_represents machine blank tape) (by simp [MultitapeEfficientPhase.sourceInitial])).2]

def bitTape (blank : Symbol) (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (input : Bits n) : Fin tapes → ℤ → Symbol :=
  fun tape cell => if h : tape = inputTape ∧ 0 ≤ cell ∧ cell < (n : ℤ) then
    bitSymbol (input ⟨cell.toNat, by omega⟩) else blank

def bitProgram (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :
    Program (Bits n) (Fin tapes × RotationProgram.Address) (SimulatorControl tapes State Symbol) (SimulatorSymbol Symbol) where
  instruction := (program machine anchor blank level outputTape cell).instruction
  initialControl := MultitapeEfficientPhase.initialControl machine blank
  initialMemory input := MultitapeEfficientPhase.initialMemory blank (bitTape blank bitSymbol inputTape input)

omit [Fintype State] [Fintype Symbol] in
theorem bitProgram_configuration (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (input : Bits n) (time : ℕ) :
    (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell).configurationAt input time =
      (program machine anchor blank level outputTape cell).configurationAt (bitTape blank bitSymbol inputTape input) time := by
  induction time with
  | zero => rfl
  | succ time ih => rw [Program.configurationAt, Program.configurationAt, ih]; rfl

def bitModel (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  ObliviousMatrix.model (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell) (eventSteps machine anchor level)
    (fun control => decode (control.auxiliary.scanned outputTape))

def bitPrompt (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (input : Bits n) :=
  ObliviousMatrix.prompt (bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell) (eventSteps machine anchor level) input

def bitInput (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (input : Bits n) :=
  RoutedMatrix.promptInput (bitPrompt machine anchor blank bitSymbol inputTape level outputTape cell input)

theorem bit_output_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (decode : Symbol → Bool) (input : Bits n) :
    (bitModel machine anchor blank bitSymbol inputTape n level outputTape cell decode).answer
      (bitInput machine anchor blank bitSymbol inputTape level outputTape cell input) =
        decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine
          (bitTape blank bitSymbol inputTape input))).tape outputTape cell) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  unfold bitModel bitInput bitPrompt
  rw [ObliviousMatrix.output_correct, bitProgram_configuration]
  have h := output_correct machine anchor blank level outputTape cell decode (bitTape blank bitSymbol inputTape input)
  simpa only [matrixModel, inputEncoding, ObliviousMatrix.output_correct] using h

def tapeLiteral (blank : Symbol) (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n : ℕ)
    (address : Fin tapes × RotationProgram.Address) (predicate : HeadMarker.Cell Symbol → Bool) : Autoregressive.ContextLiteral n :=
  match address.2 with
  | .inl cell =>
      if hcell : address.1 = inputTape ∧ 0 ≤ cell ∧ cell < (n : ℤ) then
        EfficientMatrix.bitLiteral (predicate (bitSymbol false, decide (cell = 0)))
          (predicate (bitSymbol true, decide (cell = 0))) ⟨cell.toNat, by omega⟩
      else .constant (predicate (blank, decide (cell = 0)))
  | .inr _ => .constant (predicate (blank, false))

omit [Fintype State] [Fintype Symbol] in
theorem tapeLiteral_correct (blank : Symbol) (bitSymbol : Bool → Symbol) (inputTape : Fin tapes)
    (input : Bits n) (address : Fin tapes × RotationProgram.Address) (predicate : HeadMarker.Cell Symbol → Bool) :
    (tapeLiteral blank bitSymbol inputTape n address predicate).eval input =
      predicate (MultitapeEfficientPhase.initialMemory blank (bitTape blank bitSymbol inputTape input) address) := by
  obtain ⟨tape, address⟩ := address
  cases address with
  | inl cell =>
      unfold tapeLiteral MultitapeEfficientPhase.initialMemory bitTape
      dsimp only
      split_ifs with hcell
      · rw [EfficientMatrix.eval_bitLiteral]
        cases h : input ⟨cell.toNat, by omega⟩ <;> simp only [h, Bool.false_eq_true, if_false, if_true]
      · rfl
  | inr cell => rfl

def inputLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :
    Fin (ObliviousMatrix.front (eventSteps machine anchor level) * vocabulary tapes State Symbol) → Autoregressive.ContextLiteral n :=
  fun wire =>
    let pair := finProdFinEquiv.symm wire
    Fin.cases (.constant (decide (pair.2 = ObliviousMatrix.tokenCode (.inl (MultitapeEfficientPhase.initialControl machine blank)))))
      (fun time => tapeLiteral blank bitSymbol inputTape n
        ((bitProgram machine anchor blank bitSymbol inputTape n level outputTape cell).position time.val)
        (fun value => decide (pair.2 = ObliviousMatrix.tokenCode (.inr (.inl value))))) pair.1

theorem inputLiteral_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ)
    (input : Bits n) (wire : Fin (ObliviousMatrix.front (eventSteps machine anchor level) * vocabulary tapes State Symbol)) :
    (inputLiteral machine anchor blank bitSymbol inputTape n level outputTape cell wire).eval input =
      bitInput machine anchor blank bitSymbol inputTape level outputTape cell input wire := by
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [inputLiteral, bitInput, RoutedMatrix.promptInput, Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun time => ?_) position
  · simp [bitPrompt, ObliviousMatrix.prompt, bitProgram, Autoregressive.ContextLiteral.eval]
  · simp only [Fin.cases_succ, tapeLiteral_correct, bitPrompt, ObliviousMatrix.prompt]
    rfl

def inputCircuit (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :=
  Circuit.bundle fun wire => (inputLiteral machine anchor blank bitSymbol inputTape n level outputTape cell wire).circuit

theorem inputCircuit_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (input : Bits n) :
    Circuit.eval (inputCircuit machine anchor blank bitSymbol inputTape n level outputTape cell) input =
      bitInput machine anchor blank bitSymbol inputTape level outputTape cell input := by
  funext wire
  simp only [inputCircuit, Circuit.eval, Autoregressive.ContextLiteral.eval_circuit]
  exact inputLiteral_correct machine anchor blank bitSymbol inputTape level outputTape cell input wire

theorem inputCircuit_depth (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) :
    Circuit.depth (inputCircuit machine anchor blank bitSymbol inputTape n level outputTape cell) ≤ 1 := by
  simp only [inputCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => Autoregressive.ContextLiteral.depth_circuit_le_one _

theorem precision_fixed (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape : Fin tapes) (n level : ℕ) (outputTape : Fin tapes) (cell : ℤ) (decode : Symbol → Bool) :
    (bitModel machine anchor blank bitSymbol inputTape n level outputTape cell decode).parameters.scalarBits =
      RoutedMatrix.precision (vocabulary tapes State Symbol) 2 (opcodes tapes State Symbol) := rfl

omit [Fintype State] [Fintype Symbol] in
theorem transcript_count_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (steps : ℕ) (hsteps : 1 ≤ steps) :
    eventSteps machine anchor (horizonLevel steps) ≤ (4 * (248 * tapes + 1)) * steps * (Nat.log 2 steps + 1) :=
  MultitapeEfficientPhase.horizon_instruction_count machine anchor steps 0 hsteps

omit [Fintype State] [Fintype Symbol] in
theorem event_polynomial_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (steps n coefficient exponent : ℕ) (hsteps : 1 ≤ steps) (htime : steps ≤ coefficient * (n + 1) ^ exponent) :
    eventSteps machine anchor (horizonLevel steps) ≤
      ((4 * (248 * tapes + 1)) * (coefficient + 1) ^ 2) * (n + 1) ^ (2 * exponent) := by
  have he := transcript_count_bound machine anchor steps hsteps
  have hlog := Nat.log_le_self 2 steps
  have hq : 1 ≤ (n + 1) ^ exponent := Nat.one_le_pow _ _ (by omega)
  have ht : steps ≤ (coefficient + 1) * (n + 1) ^ exponent := by nlinarith
  have hsucc : steps + 1 ≤ (coefficient + 1) * (n + 1) ^ exponent := by nlinarith
  calc
    _ ≤ (4 * (248 * tapes + 1)) * steps * (Nat.log 2 steps + 1) := he
    _ ≤ (4 * (248 * tapes + 1)) * steps * (steps + 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ (4 * (248 * tapes + 1)) * ((coefficient + 1) * (n + 1) ^ exponent) *
        ((coefficient + 1) * (n + 1) ^ exponent) := Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hsucc
    _ = _ := by rw [Nat.mul_comm 2 exponent, Nat.pow_mul]; ring

def polynomialTraceConstant (tapes coefficient exponent : ℕ) : ℕ :=
  (4 * (248 * tapes + 1)) * (coefficient + 1) * (Nat.log 2 (coefficient + 1) + 2 + exponent)

omit [Fintype State] [Fintype Symbol] in
theorem normalized_time_bound (time n coefficient exponent : ℕ) (bound : time ≤ coefficient * (n + 1) ^ exponent) :
    max 1 time ≤ (coefficient + 1) * (n + 1) ^ exponent := by
  have hp : 1 ≤ (n + 1) ^ exponent := Nat.one_le_pow _ _ (by omega)
  apply max_le <;> nlinarith

omit [Fintype State] [Fintype Symbol] in
theorem polynomial_log_time_bound (time n coefficient exponent : ℕ)
    (bound : time ≤ (coefficient + 1) * (n + 1) ^ exponent) :
    Nat.log 2 time + 1 ≤ (Nat.log 2 (coefficient + 1) + 2 + exponent) * (Nat.log 2 (n + 1) + 1) := by
  have hn : n + 1 ≤ 2 ^ (Nat.log 2 (n + 1) + 1) := (Nat.lt_pow_succ_log_self (by decide) (n + 1)).le
  have hc : coefficient + 1 ≤ 2 ^ (Nat.log 2 (coefficient + 1) + 1) :=
    (Nat.lt_pow_succ_log_self (by decide) (coefficient + 1)).le
  have hp : time ≤ 2 ^ ((Nat.log 2 (coefficient + 1) + 1) + exponent * (Nat.log 2 (n + 1) + 1)) := by
    calc
      _ ≤ (coefficient + 1) * (n + 1) ^ exponent := bound
      _ ≤ 2 ^ (Nat.log 2 (coefficient + 1) + 1) * (2 ^ (Nat.log 2 (n + 1) + 1)) ^ exponent :=
        Nat.mul_le_mul hc (Nat.pow_le_pow_left hn exponent)
      _ = _ := by rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; ring
  have hl := Nat.log_mono_right (b := 2) hp
  rw [Nat.log_pow (by decide)] at hl
  nlinarith

omit [Fintype State] [Fintype Symbol] in
/-- The sharp polynomial-time trace bound needed for power-stretch seed
allocation: it retains the original source exponent rather than doubling it. -/
theorem polynomial_log_trace_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (time n coefficient exponent : ℕ) (bound : time ≤ coefficient * (n + 1) ^ exponent) :
    eventSteps machine anchor (horizonLevel (max 1 time)) ≤
      polynomialTraceConstant tapes coefficient exponent * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
  have ht := normalized_time_bound time n coefficient exponent bound
  have hl := polynomial_log_time_bound (max 1 time) n coefficient exponent ht
  calc
    _ ≤ (4 * (248 * tapes + 1)) * max 1 time * (Nat.log 2 (max 1 time) + 1) :=
      transcript_count_bound machine anchor (max 1 time) (Nat.le_max_left _ _)
    _ ≤ (4 * (248 * tapes + 1)) * ((coefficient + 1) * (n + 1) ^ exponent) *
        ((Nat.log 2 (coefficient + 1) + 2 + exponent) * (Nat.log 2 (n + 1) + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hl
    _ = _ := by unfold polynomialTraceConstant; ring

end MultitapeMatrix
