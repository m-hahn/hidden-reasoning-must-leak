import Encryption
import LookupTransformer

/-!
# Oblivious multitape simulation by a one-layer autoregressive Transformer

This file supplies the machine-simulation component used by the encrypted-CoT
theorems.  It first gives semantics to a bounded multitape machine whose head
locations may depend on its data, and constructs an input-independent
fixed-horizon simulator with a proved configuration-by-configuration
invariant.  An oblivious access schedule fixes, independently of the input,
both the cell visited by every physical tape at every time and the most recent
earlier visit to that cell.  A step token stores the new control state and the
symbols written on all tapes.

The construction uses one causal attention head for the preceding state and
one for each tape.  A tape head attends to the schedule's most recent write,
or to the appropriate input/initial-tape cell if there is no earlier write.
The local MLP applies the machine transition and emits the next step token.
`one_layer_oblivious_simulation` proves, step by step, that this one-layer
construction produces exactly the oblivious machine trace.  Since the tape
set is fixed, the number of heads is constant as the input length and running
time vary.

The development is finite-precision in the sense relevant to the appendix:
states, tape symbols, tapes, attention values, and emitted tokens are finite
types.  Absolute positional advice contains only the input-independent access
schedule and therefore may vary nonuniformly with the input length.

The `OneLayerTransformer` below specifies attention/local-map semantics;
it is not an assembled matrix `FixedPrecisionTransformer`. The direct
input-dependent compiler stores the entire source configuration in finite
control. Its event count does not establish polynomial model size or the
binary trace overhead of the paper. `SimulationSizeAudit` proves the token
size obstruction explicitly. An efficient oblivious compiler and complete
matrix realization remain necessary for the paper's upper bounds.
-/

noncomputable section

namespace ObliviousSimulation

open TransformerAC0

/-! ## Oblivious multitape computations -/

/--
An input-independent tape-access schedule.  `prior time tape` is the latest
earlier time at which that tape visited its current cell, when such a time
exists.  The laws make the cached last-write index precise.
-/
structure AccessSchedule (Tape Position : Type*) [DecidableEq Position] where
  position : ℕ → Tape → Position
  prior : (time : ℕ) → Tape → Option (Fin time)
  prior_same : ∀ time tape previous,
    prior time tape = some previous →
      position previous tape = position time tape
  prior_latest : ∀ time tape previous,
    prior time tape = some previous →
      ∀ other, other < time → position other tape = position time tape →
        other ≤ previous
  prior_none : ∀ time tape,
    prior time tape = none →
      ∀ previous, previous < time → position previous tape ≠ position time tape

/-- One event in the compact computation trace. -/
structure StepToken (Tape State Symbol : Type*) where
  state : State
  write : Tape → Symbol

instance stepTokenInhabited {Tape State Symbol : Type*}
    [Inhabited State] [Inhabited Symbol] : Inhabited (StepToken Tape State Symbol) :=
  ⟨⟨default, fun _ => default⟩⟩

def stepTokenEquiv (Tape State Symbol : Type*) :
    (State × (Tape → Symbol)) ≃ StepToken Tape State Symbol where
  toFun value := ⟨value.1, value.2⟩
  invFun token := (token.state, token.write)
  left_inv value := by cases value; rfl
  right_inv token := by cases token; rfl

noncomputable instance stepTokenFintype
    {Tape State Symbol : Type*} [Fintype Tape] [DecidableEq Tape]
    [Fintype State] [Fintype Symbol] : Fintype (StepToken Tape State Symbol) :=
  Fintype.ofEquiv (State × (Tape → Symbol)) (stepTokenEquiv Tape State Symbol)

/--
A deterministic multitape machine whose head positions are supplied by an
oblivious schedule.  The transition sees the current finite-control state and
one symbol per tape, and returns the next state and one symbol to write per
tape.
-/
structure Machine (Input Tape Position State Symbol : Type*)
    [DecidableEq Position] where
  schedule : AccessSchedule Tape Position
  initialState : Input → State
  initialTape : Input → Tape → Position → Symbol
  transition : State → (Tape → Symbol) → StepToken Tape State Symbol

namespace Machine

variable {Input Tape Position State Symbol : Type*}
variable [DecidableEq Position]

/--
The event-sourced machine trace.  Recursive calls only inspect strictly
earlier tokens: the immediately preceding token supplies the state, and the
oblivious last-write index supplies each currently scanned symbol.
-/
def traceToken (M : Machine Input Tape Position State Symbol)
    (input : Input) (time : ℕ) : StepToken Tape State Symbol :=
  let previousState :=
    match time with
    | 0 => M.initialState input
    | previous + 1 => (M.traceToken input previous).state
  let scanned : Tape → Symbol := fun tape =>
    match M.schedule.prior time tape with
    | none => M.initialTape input tape (M.schedule.position time tape)
    | some previous => (M.traceToken input previous).write tape
  M.transition previousState scanned
termination_by time

/-- The fixed-length prefix of the infinite event trace. -/
def trace (M : Machine Input Tape Position State Symbol)
    (steps : ℕ) (input : Input) : Fin steps → StepToken Tape State Symbol :=
  fun time => M.traceToken input time

end Machine

/-! ## Constructing an oblivious simulator from input-dependent computation -/

/--
A bounded multitape machine before oblivious compilation.  Its next head
locations may depend on the current state, scanned symbols, and current head
locations.  For a fixed input length and time horizon, the finite type
`Position` is the portion of each ordinary Turing tape reachable during that
run.
-/
structure InputDependentMachine
    (Input Tape Position State Symbol : Type*) [DecidableEq Position] where
  initialState : Input → State
  initialHead : Input → Tape → Position
  initialTape : Input → Tape → Position → Symbol
  transition : State → (Tape → Position) → (Tape → Symbol) →
    State × (Tape → Symbol) × (Tape → Position)

/-- A complete configuration of a bounded multitape computation. -/
structure Configuration (Tape Position State Symbol : Type*) where
  state : State
  head : Tape → Position
  tape : Tape → Position → Symbol

def configurationEquiv (Tape Position State Symbol : Type*) :
    (State × (Tape → Position) × (Tape → Position → Symbol)) ≃
      Configuration Tape Position State Symbol where
  toFun value := ⟨value.1, value.2.1, value.2.2⟩
  invFun configuration :=
    (configuration.state, configuration.head, configuration.tape)
  left_inv value := by cases value; rfl
  right_inv configuration := by cases configuration; rfl

noncomputable instance configurationFintype
    {Tape Position State Symbol : Type*}
    [Fintype Tape] [DecidableEq Tape] [Fintype Position] [DecidableEq Position]
    [Fintype State] [Fintype Symbol] :
    Fintype (Configuration Tape Position State Symbol) :=
  Fintype.ofEquiv (State × (Tape → Position) × (Tape → Position → Symbol))
    (configurationEquiv Tape Position State Symbol)

instance configurationInhabited
    {Tape Position State Symbol : Type*}
    [Inhabited Position] [Inhabited State] [Inhabited Symbol] :
    Inhabited (Configuration Tape Position State Symbol) :=
  ⟨⟨default, fun _ => default, fun _ _ => default⟩⟩

namespace InputDependentMachine

variable {Input Tape Position State Symbol : Type*} [DecidableEq Position]

/-- Initial configuration on an input. -/
def initialConfiguration
    (M : InputDependentMachine Input Tape Position State Symbol) (input : Input) :
    Configuration Tape Position State Symbol :=
  ⟨M.initialState input, M.initialHead input, M.initialTape input⟩

/-- One ordinary, potentially input-dependent head-access step. -/
def step (M : InputDependentMachine Input Tape Position State Symbol)
    (configuration : Configuration Tape Position State Symbol) :
    Configuration Tape Position State Symbol :=
  let scanned := fun tape => configuration.tape tape (configuration.head tape)
  let action := M.transition configuration.state configuration.head scanned
  { state := action.1
    head := action.2.2
    tape := fun tape position =>
      if position = configuration.head tape then action.2.1 tape
      else configuration.tape tape position }

/-- Configuration after exactly `time` source-machine steps. -/
def configurationAt (M : InputDependentMachine Input Tape Position State Symbol)
    (input : Input) : ℕ → Configuration Tape Position State Symbol
  | 0 => M.initialConfiguration input
  | time + 1 => M.step (M.configurationAt input time)

end InputDependentMachine

/-- The immediate predecessor, used by a fixed sequential access schedule. -/
def immediatePrior : (time : ℕ) → Option (Fin time)
  | 0 => none
  | time + 1 => some ⟨time, Nat.lt_succ_self time⟩

/--
An input-independent schedule which repeatedly visits the sole physical cell.
The entire bounded source configuration is finite control in the nonuniform
fixed-horizon simulator; consequently every later event only needs the
immediately preceding event.
-/
def sequentialSchedule : AccessSchedule Unit Unit where
  position := fun _ _ => ()
  prior := fun time _ => immediatePrior time
  prior_same := by intros; rfl
  prior_latest := by
    intro time tape previous hprevious other hother _
    cases time with
    | zero => simp [immediatePrior] at hprevious
    | succ time =>
        have heq : (⟨time, Nat.lt_succ_self time⟩ : Fin (time + 1)) = previous :=
          Option.some.inj (by simpa [immediatePrior] using hprevious)
        rw [← heq]
        exact Nat.le_of_lt_succ hother
  prior_none := by
    intro time tape hnone previous hprevious
    cases time with
    | zero => omega
    | succ time => simp [immediatePrior] at hnone

/-- Simulator control: `false` is the one-step initialization phase. -/
abbrev ObliviousControl (Tape Position State Symbol : Type*) :=
  Bool × Configuration Tape Position State Symbol

/--
Compile an input-dependent bounded multitape computation into an oblivious
one-cell semantic machine. The complete configuration is stored in finite
control, whose cardinality can grow exponentially with the tape capacity.
This construction establishes semantic preservation, not the efficient
oblivious simulation needed for the paper's upper bound.
-/
def compileInputDependent
    {Input Tape Position State Symbol : Type*} [DecidableEq Position]
    (source : InputDependentMachine Input Tape Position State Symbol) :
    Machine Input Unit Unit (ObliviousControl Tape Position State Symbol) Unit where
  schedule := sequentialSchedule
  initialState := fun input => (false, source.initialConfiguration input)
  initialTape := fun _ _ _ => ()
  transition := fun control _ =>
    match control with
    | (false, configuration) => ⟨(true, configuration), fun _ => ()⟩
    | (true, configuration) => ⟨(true, source.step configuration), fun _ => ()⟩

/-- Every oblivious event contains the exact source configuration at that time. -/
theorem compileInputDependent_traceToken
    {Input Tape Position State Symbol : Type*} [DecidableEq Position]
    (source : InputDependentMachine Input Tape Position State Symbol)
    (input : Input) (time : ℕ) :
    ((compileInputDependent source).traceToken input time).state =
      (true, source.configurationAt input time) := by
  induction time with
  | zero =>
      rw [Machine.traceToken.eq_def]
      rfl
  | succ time ih =>
      rw [Machine.traceToken.eq_def]
      simp only
      rw [ih]
      rfl

/-- Trace-level semantic preservation of the oblivious compiler. -/
theorem compileInputDependent_trace
    {Input Tape Position State Symbol : Type*} [DecidableEq Position]
    (source : InputDependentMachine Input Tape Position State Symbol)
    (steps : ℕ) (input : Input) (time : Fin (steps + 1)) :
    ((compileInputDependent source).trace (steps + 1) input time).state.2 =
      source.configurationAt input time := by
  exact congrArg Prod.snd (compileInputDependent_traceToken source input time)

/-! ## A causal one-layer Transformer interface -/

/-- Initial data that an attention head may retrieve from the input region. -/
inductive InputAddress (Tape Position : Type*)
  | initialState
  | initialCell (tape : Tape) (position : Position)

/-- A causal head reads either input data or one already generated token. -/
inductive CausalSource (Address : Type*) (time : ℕ)
  | input (address : Address)
  | generated (previous : Fin time)

/-- Finite values passed from attention to the local MLP. -/
inductive AttentionValue (Tape State Symbol : Type*)
  | state (value : State)
  | symbol (value : Symbol)
  | token (value : StepToken Tape State Symbol)

instance attentionValueInhabited {Tape State Symbol : Type*}
    [Inhabited State] [Inhabited Symbol] :
    Inhabited (AttentionValue Tape State Symbol) := ⟨.state default⟩

def attentionValueEquiv (Tape State Symbol : Type*) :
    (State ⊕ Symbol ⊕ StepToken Tape State Symbol) ≃ AttentionValue Tape State Symbol where
  toFun
    | .inl state => .state state
    | .inr (.inl symbol) => .symbol symbol
    | .inr (.inr token) => .token token
  invFun
    | .state state => .inl state
    | .symbol symbol => .inr (.inl symbol)
    | .token token => .inr (.inr token)
  left_inv value := by cases value with
    | inl _ => rfl
    | inr value => cases value <;> rfl
  right_inv value := by cases value <;> rfl

noncomputable instance attentionValueFintype
    {Tape State Symbol : Type*} [Fintype Tape] [DecidableEq Tape]
    [Fintype State] [Fintype Symbol] : Fintype (AttentionValue Tape State Symbol) :=
  Fintype.ofEquiv (State ⊕ Symbol ⊕ StepToken Tape State Symbol)
    (attentionValueEquiv Tape State Symbol)

/--
Extensional semantics of a one-layer causal autoregressive Transformer.
Every output token is obtained by one simultaneous attention lookup per head,
followed by one fixed local map.  The source map is positional advice and is
therefore independent of the input and generated token values.
-/
structure OneLayerTransformer
    (Input Head Address Value Token Output : Type*) (steps : ℕ) where
  inputValue : Input → Address → Value
  tokenValue : Token → Value
  source : (time : ℕ) → Head → CausalSource Address time
  localMLP : (time : ℕ) → (Head → Value) → Token
  generated : Input → ℕ → Token
  generated_correct : ∀ input (time : Fin steps),
    generated input time = localMLP time (fun head =>
      match source time head with
      | .input address => inputValue input address
      | .generated previous => tokenValue (generated input previous))
  readout : Input → (Fin steps → Token) → Output

namespace OneLayerTransformer

variable {Input Head Address Value Token Output : Type*} {steps : ℕ}

/-- The complete generated payload before the terminal separator. -/
def trace (T : OneLayerTransformer Input Head Address Value Token Output steps)
    (input : Input) : Fin steps → Token :=
  fun time => T.generated input time

/-- The output following the generated trace. -/
def run (T : OneLayerTransformer Input Head Address Value Token Output steps)
    (input : Input) : Output :=
  T.readout input (T.trace input)

end OneLayerTransformer

/-! ## Constructing the simulator -/

variable {Input Tape Position State Symbol Output : Type*}
variable [Fintype Tape] [DecidableEq Tape] [DecidableEq Position]
variable [Inhabited State] [Inhabited Symbol]

/-- The state head is `none`; `some tape` is the head serving that tape. -/
abbrev SimulationHead (Tape : Type*) := Option Tape

/-- Input interpretation for the simulator's attention heads. -/
def machineInputValue
    (M : Machine Input Tape Position State Symbol) (input : Input) :
    InputAddress Tape Position → AttentionValue Tape State Symbol
  | .initialState => .state (M.initialState input)
  | .initialCell tape position => .symbol (M.initialTape input tape position)

/-- A generated step token is passed unchanged through attention. -/
def machineTokenValue (token : StepToken Tape State Symbol) :
    AttentionValue Tape State Symbol := .token token

/-- The immediately preceding generated position, when it exists. -/
def previousSource : (time : ℕ) →
    CausalSource (InputAddress Tape Position) time
  | 0 => .input .initialState
  | time + 1 => .generated ⟨time, Nat.lt_succ_self time⟩

/--
The input-independent attention plan.  It retrieves the previous control
state and, for every tape, the token containing the latest write to the cell
currently visited by that tape.
-/
def machineSource (M : Machine Input Tape Position State Symbol)
    (time : ℕ) : SimulationHead Tape →
      CausalSource (InputAddress Tape Position) time
  | none => previousSource time
  | some tape =>
      match M.schedule.prior time tape with
      | none => .input (.initialCell tape (M.schedule.position time tape))
      | some previous => .generated previous

/-- Extract the control state from the state head's value. -/
def stateOfAttention : AttentionValue Tape State Symbol → State
  | .state state => state
  | .token token => token.state
  | .symbol _ => default

/-- Extract the scanned symbol for `tape` from that tape head's value. -/
def symbolOfAttention (tape : Tape) : AttentionValue Tape State Symbol → Symbol
  | .symbol symbol => symbol
  | .token token => token.write tape
  | .state _ => default

/-- The fixed local transition performed after the attention lookups. -/
def machineLocalMLP (M : Machine Input Tape Position State Symbol)
    (_time : ℕ) (attended : SimulationHead Tape → AttentionValue Tape State Symbol) :
    StepToken Tape State Symbol :=
  M.transition (stateOfAttention (attended none))
    (fun tape => symbolOfAttention tape (attended (some tape)))

/-- Every bit of the simulator's finite local transition is realized by a
concrete matrix-level fixed-precision Transformer.  Thus the extensional
`localMLP` below is not carrying an unproved neural-realization premise. -/
theorem machineLocalMLP_bits_realized
    [Fintype State] [Fintype Symbol]
    (M : Machine Input Tape Position State Symbol)
    (encode : StepToken Tape State Symbol → Bits width) :
    ∀ bit : Fin width,
      ∃ model : FixedPrecisionTransformer
          (LookupTransformer.architecture
            (Fintype.card
              (SimulationHead Tape → AttentionValue Tape State Symbol))),
        ∀ (time : ℕ)
          (attended : SimulationHead Tape → AttentionValue Tape State Symbol),
          model.run (LookupTransformer.oneHot
              (Fintype.equivFin
                (SimulationHead Tape → AttentionValue Tape State Symbol) attended)) =
            encode (machineLocalMLP M time attended) bit := by
  intro bit
  obtain ⟨model, hmodel⟩ := LookupTransformer.finiteMap_bits_realized
    (SimulationHead Tape → AttentionValue Tape State Symbol)
    (StepToken Tape State Symbol) encode (machineLocalMLP M 0) bit
  refine ⟨model, ?_⟩
  intro time attended
  exact hmodel attended

/--
The one-layer simulator for an oblivious machine.  Its generated sequence is
definitionally the machine's event trace; `generated_correct` below proves
that every token is in fact obtained by the advertised causal attention and
single local transition.
-/
def compile
    (M : Machine Input Tape Position State Symbol) (steps : ℕ)
    (readout : (Fin steps → StepToken Tape State Symbol) → Output) :
    OneLayerTransformer Input (SimulationHead Tape) (InputAddress Tape Position)
      (AttentionValue Tape State Symbol) (StepToken Tape State Symbol) Output steps where
  inputValue := machineInputValue M
  tokenValue := machineTokenValue
  source := machineSource M
  localMLP := machineLocalMLP M
  generated := M.traceToken
  generated_correct := by
    intro input ⟨time, htime⟩
    rw [Machine.traceToken.eq_def]
    symm
    unfold machineLocalMLP
    cases time with
    | zero =>
        simp only
        congr 1
        funext tape
        cases hprior : M.schedule.prior 0 tape <;>
          simp [machineSource, hprior, machineInputValue, machineTokenValue,
            symbolOfAttention]
    | succ time =>
        simp only
        congr 1
        funext tape
        cases hprior : M.schedule.prior (time + 1) tape <;>
          simp [machineSource, hprior, machineInputValue, machineTokenValue,
            symbolOfAttention]
  readout := fun _ => readout

omit [Fintype Tape] [DecidableEq Tape] in
/-- The compiled Transformer emits exactly the machine trace. -/
theorem compile_trace_correct
    (M : Machine Input Tape Position State Symbol) (steps : ℕ)
    (readout : (Fin steps → StepToken Tape State Symbol) → Output)
    (input : Input) :
    (compile M steps readout).trace input = M.trace steps input := rfl

omit [Fintype Tape] [DecidableEq Tape] in
/--
Correctness of the output read after the trace, for any machine-level readout
whose correctness has been established.
-/
theorem compile_output_correct
    (M : Machine Input Tape Position State Symbol) (steps : ℕ)
    (readout : (Fin steps → StepToken Tape State Symbol) → Output)
    (target : Input → Output)
    (readout_correct : ∀ input, readout (M.trace steps input) = target input)
    (input : Input) :
    (compile M steps readout).run input = target input := by
  unfold OneLayerTransformer.run
  rw [compile_trace_correct]
  exact readout_correct input

omit [DecidableEq Tape] in
/-- The number of attention heads is one plus the fixed number of tapes. -/
theorem simulation_head_count :
    Fintype.card (SimulationHead Tape) = Fintype.card Tape + 1 := by
  simp [SimulationHead]

omit [DecidableEq Tape] in
/--
Complete oblivious-simulation theorem: one layer, exactly `steps` generated
tokens, exact output correctness, and a head count independent of the input
length and running time.
-/
theorem one_layer_oblivious_simulation
    (M : Machine Input Tape Position State Symbol) (steps : ℕ)
    (readout : (Fin steps → StepToken Tape State Symbol) → Output)
    (target : Input → Output)
    (readout_correct : ∀ input, readout (M.trace steps input) = target input) :
    ∃ T : OneLayerTransformer Input (SimulationHead Tape) (InputAddress Tape Position)
        (AttentionValue Tape State Symbol) (StepToken Tape State Symbol) Output steps,
      (∀ input, T.trace input = M.trace steps input) ∧
      (∀ input, T.run input = target input) ∧
      Fintype.card (SimulationHead Tape) = Fintype.card Tape + 1 := by
  exact ⟨compile M steps readout, compile_trace_correct M steps readout,
    compile_output_correct M steps readout target readout_correct,
    simulation_head_count⟩

/-! ## Direct simulation of input-dependent bounded machines -/

/-- Read the source configuration after the requested number of steps. -/
def inputDependentReadout
    {Tape Position State Symbol Output : Type*} {steps : ℕ}
    (finish : Configuration Tape Position State Symbol → Output)
    (trace : Fin (steps + 1) →
      StepToken Unit (ObliviousControl Tape Position State Symbol) Unit) : Output :=
  finish ((trace (Fin.last steps)).state.2)

/--
The one-layer simulator constructed directly from an input-dependent bounded
multitape machine.  The extra initial token exposes configuration zero; token
`t` then contains the configuration after exactly `t` source steps.
-/
def compileInputDependentTransformer
    {Input Tape Position State Symbol Output : Type*}
    [Fintype Tape] [DecidableEq Tape] [DecidableEq Position]
    [Inhabited Position] [Inhabited State] [Inhabited Symbol]
    (source : InputDependentMachine Input Tape Position State Symbol)
    (steps : ℕ) (finish : Configuration Tape Position State Symbol → Output) :
    OneLayerTransformer Input (SimulationHead Unit) (InputAddress Unit Unit)
      (AttentionValue Unit (ObliviousControl Tape Position State Symbol) Unit)
      (StepToken Unit (ObliviousControl Tape Position State Symbol) Unit)
      Output (steps + 1) :=
  compile (compileInputDependent source) (steps + 1)
    (inputDependentReadout finish)

/-- Every generated token exposes exactly the corresponding source configuration. -/
theorem compileInputDependentTransformer_trace
    {Input Tape Position State Symbol Output : Type*}
    [Fintype Tape] [DecidableEq Tape] [DecidableEq Position]
    [Inhabited Position] [Inhabited State] [Inhabited Symbol]
    (source : InputDependentMachine Input Tape Position State Symbol)
    (steps : ℕ) (finish : Configuration Tape Position State Symbol → Output)
    (input : Input) (time : Fin (steps + 1)) :
    (((compileInputDependentTransformer source steps finish).trace input time).state.2) =
      source.configurationAt input time := by
  exact compileInputDependent_trace source steps input time

/-- Exact task-output preservation for the constructed one-layer simulator. -/
theorem compileInputDependentTransformer_output
    {Input Tape Position State Symbol Output : Type*}
    [Fintype Tape] [DecidableEq Tape] [DecidableEq Position]
    [Inhabited Position] [Inhabited State] [Inhabited Symbol]
    (source : InputDependentMachine Input Tape Position State Symbol)
    (steps : ℕ) (finish : Configuration Tape Position State Symbol → Output)
    (target : Input → Output)
    (correct : ∀ input, finish (source.configurationAt input steps) = target input)
    (input : Input) :
    (compileInputDependentTransformer source steps finish).run input = target input := by
  change finish
    (((compileInputDependentTransformer source steps finish).trace input
      (Fin.last steps)).state.2) = target input
  rw [compileInputDependentTransformer_trace]
  exact correct input

/--
Finite-control semantic simulation of the bounded source computation.
The event count is `steps + 1` and the abstract simulator uses two heads.
Token width and finite-control cardinality are not bounded here, so this
statement does not establish the paper's binary-length or model-size theorem.
-/
theorem inputDependent_to_one_layer_oblivious_simulation
    {Input Tape Position State Symbol Output : Type*}
    [Fintype Tape] [DecidableEq Tape] [Fintype Position] [DecidableEq Position]
    [Fintype State] [Fintype Symbol]
    [Inhabited Position] [Inhabited State] [Inhabited Symbol]
    (source : InputDependentMachine Input Tape Position State Symbol)
    (steps : ℕ) (finish : Configuration Tape Position State Symbol → Output)
    (target : Input → Output)
    (correct : ∀ input, finish (source.configurationAt input steps) = target input) :
    ∃ T : OneLayerTransformer Input (SimulationHead Unit) (InputAddress Unit Unit)
        (AttentionValue Unit (ObliviousControl Tape Position State Symbol) Unit)
        (StepToken Unit (ObliviousControl Tape Position State Symbol) Unit)
        Output (steps + 1),
      (∀ input time, (T.trace input time).state.2 =
        source.configurationAt input time) ∧
      (∀ input, T.run input = target input) ∧
      Fintype.card (SimulationHead Unit) = 2 ∧
      steps + 1 ≤ (steps + 1) * (Nat.log2 (steps + 2) + 1) := by
  refine ⟨compileInputDependentTransformer source steps finish,
    compileInputDependentTransformer_trace source steps finish,
    compileInputDependentTransformer_output source steps finish target correct,
    ?_, ?_⟩
  · simp [SimulationHead]
  · calc
      steps + 1 = (steps + 1) * 1 := by omega
      _ ≤ (steps + 1) * (Nat.log2 (steps + 2) + 1) := by
        apply Nat.mul_le_mul_left
        omega

/-! ## Online encryption of the simulated trace -/

/-- A fixed-width binary representation of the finite trace-token alphabet. -/
structure BinaryCode (Token : Type*) (width : ℕ) where
  encode : Token → Bits width
  decode : Bits width → Token
  decode_encode : ∀ token, decode (encode token) = token

/-- Select one fixed-width block from a flattened bit string. -/
def bitBlock {blocks width : ℕ} (stream : Bits (blocks * width))
    (block : Fin blocks) : Bits width :=
  fun bit => stream (finProdFinEquiv (block, bit))

/-- Flatten a block-valued generated trace into the monitor's bit stream. -/
def flattenBitTrace {blocks width : ℕ} (trace : Fin blocks → Bits width) :
    Bits (blocks * width) :=
  fun index =>
    let location := finProdFinEquiv.symm index
    trace location.1 location.2

@[simp] theorem bitBlock_flattenBitTrace {blocks width : ℕ}
    (trace : Fin blocks → Bits width) (block : Fin blocks) :
    bitBlock (flattenBitTrace trace) block = trace block := by
  funext bit
  simp [bitBlock, flattenBitTrace]

/-- Flatten a fixed-length sequence of encoded tokens into one bit string. -/
def encodedTrace
    {Input Token : Type*} {steps width : ℕ}
    (plain : Input → Fin steps → Token) (code : BinaryCode Token width)
    (input : Input) : Bits (steps * width) :=
  fun index =>
    let location := finProdFinEquiv.symm index
    code.encode (plain input location.1) location.2

@[simp] theorem bitBlock_encodedTrace
    {Input Token : Type*} {steps width : ℕ}
    (plain : Input → Fin steps → Token) (code : BinaryCode Token width)
    (input : Input) (time : Fin steps) :
    bitBlock (encodedTrace plain code input) time = code.encode (plain input time) := by
  funext bit
  simp [bitBlock, encodedTrace]

/-- The exact PRG pad block assigned to one generated token. -/
def padBlock {seedLength steps width suffix locality : ℕ}
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (seed : Bits seedLength) (time : Fin steps) : Bits width :=
  bitBlock (Encryption.prefixGenerator generator.generate seed) time

/-- The visible encrypted payload, token by token. -/
def encryptedTokenTrace
    {Input Token : Type*} {seedLength steps width suffix locality : ℕ}
    (plain : Input → Fin steps → Token) (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) (time : Fin steps) : Bits width :=
  Encryption.bitXor (code.encode (plain input time)) (padBlock generator seed time)

/-- Decrypt and decode one already generated token. -/
def decryptedTokenAt
    {Input Token : Type*} {seedLength steps width suffix locality : ℕ}
    (plain : Input → Fin steps → Token) (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) (time : Fin steps) : Token :=
  code.decode (Encryption.bitXor
    (encryptedTokenTrace plain code generator input seed time)
    (padBlock generator seed time))

/-- Every previously generated ciphertext token decrypts to its plaintext. -/
@[simp] theorem decryptedTokenAt_correct
    {Input Token : Type*} {seedLength steps width suffix locality : ℕ}
    (plain : Input → Fin steps → Token) (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) (time : Fin steps) :
    decryptedTokenAt plain code generator input seed time = plain input time := by
  unfold decryptedTokenAt encryptedTokenTrace
  rw [Encryption.bitXor_right_involutive, code.decode_encode]

/--
The substantive online-encryption identity.  At autoregressive step `time`,
decrypt every causally attended prior token, apply the original one-layer
local map, and re-encrypt its result with the current PRG block.  The result
is exactly the visible ciphertext token at `time`.
-/
theorem online_decrypt_transition_reencrypt
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ}
    (T : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) (time : Fin steps) :
    encryptedTokenTrace T.trace code generator input seed time =
      Encryption.bitXor
        (code.encode (T.localMLP time (fun head =>
          match T.source time head with
          | .input address => T.inputValue input address
          | .generated previous => T.tokenValue
              (decryptedTokenAt T.trace code generator input seed
                ⟨previous, previous.isLt.trans time.isLt⟩))))
        (padBlock generator seed time) := by
  have hlocal := T.generated_correct input time
  unfold encryptedTokenTrace
  apply congrArg (fun encoded =>
    Encryption.bitXor encoded (padBlock generator seed time))
  apply congrArg code.encode
  change T.generated input (time : ℕ) = _
  rw [hlocal]
  congr 1
  funext head
  cases hsource : T.source time head with
  | input address => rfl
  | generated previous =>
      simp only
      rw [decryptedTokenAt_correct]
      rfl

/--
Number of heads sufficient for online encryption.  Besides the original
heads, each possibly generated source and the new output token may request
`width * locality` seed-coordinate lookups.  For a fixed machine, code, and
local PRG this is constant in the input length and trace length.
-/
def encryptedHeadCount (plainHeads width locality : ℕ) : ℕ :=
  plainHeads + (plainHeads + 1) * width * locality

/-- Heads of the actual encrypted simulator. -/
inductive EncryptedHead (Head : Type*) (width locality : ℕ)
  | plain (head : Head)
  | priorSeed (head : Head) (bit : Fin width) (dependency : Fin locality)
  | currentSeed (bit : Fin width) (dependency : Fin locality)
  deriving Fintype

/-- Input addresses used by the encrypted simulator. -/
inductive EncryptedAddress (Address : Type*) (seedLength : ℕ)
  | plain (address : Address)
  | seed (coordinate : Option (Fin seedLength))
  deriving Fintype

/-- Attention values used by the encrypted simulator. -/
inductive EncryptedValue (Value : Type*) (width : ℕ)
  | plain (value : Value)
  | ciphertext (value : Bits width)
  | seedBit (value : Bool)
  deriving Fintype

instance encryptedValueInhabited {Value : Type*} {width : ℕ} [Inhabited Value] :
    Inhabited (EncryptedValue Value width) := ⟨.plain default⟩

def EncryptedValue.getPlain {Value : Type*} {width : ℕ} [Inhabited Value] :
    EncryptedValue Value width → Value
  | .plain value => value
  | _ => default

def EncryptedValue.getCiphertext {Value : Type*} {width : ℕ} :
    EncryptedValue Value width → Bits width
  | .ciphertext value => value
  | _ => fun _ => false

def EncryptedValue.getSeedBit {Value : Type*} {width : ℕ} :
    EncryptedValue Value width → Bool
  | .seedBit value => value
  | _ => false

/-- Flatten a token/bit pair to its position in the PRG prefix. -/
def flatBitIndex {steps width suffix : ℕ}
    (time : Fin steps) (bit : Fin width) : Fin (steps * width + suffix) :=
  Fin.castLE (Nat.le_add_right (steps * width) suffix) (finProdFinEquiv (time, bit))

/--
Reconstruct a seed assignment from the `locality` dependency values visible to
the MLP.  Coordinates outside the selected neighborhood receive `false`.
-/
def reconstructedSeed {seedLength outputLength locality : ℕ}
    (generator : Encryption.LocalGenerator seedLength outputLength locality)
    (output : Fin outputLength) (observed : Fin locality → Bool) : Bits seedLength :=
  fun coordinate =>
    if h : ∃ dependency, generator.dependency output dependency = coordinate then
      observed (Classical.choose h)
    else false

private theorem reconstructedSeed_agrees
    {seedLength outputLength locality : ℕ}
    (generator : Encryption.LocalGenerator seedLength outputLength locality)
    (seed : Bits seedLength) (output : Fin outputLength) :
    ∀ dependency,
      reconstructedSeed generator output
          (fun j => seed (generator.dependency output j))
          (generator.dependency output dependency) =
        seed (generator.dependency output dependency) := by
  intro dependency
  unfold reconstructedSeed
  let hexists : ∃ j, generator.dependency output j =
      generator.dependency output dependency := ⟨dependency, rfl⟩
  rw [dif_pos hexists]
  apply congrArg seed
  exact Classical.choose_spec hexists

/-- Evaluating a local generator from its attended dependency bits is exact. -/
theorem localGenerator_from_dependencies
    {seedLength outputLength locality : ℕ}
    (generator : Encryption.LocalGenerator seedLength outputLength locality)
    (seed : Bits seedLength) (output : Fin outputLength) :
    generator.generate
        (reconstructedSeed generator output
          (fun dependency => seed (generator.dependency output dependency))) output =
      generator.generate seed output := by
  apply generator.locality_correct
  exact reconstructedSeed_agrees generator seed output

/-- Positional attention plan for the actual encrypted simulator. -/
def encryptedSource
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ}
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (time : ℕ) : EncryptedHead Head width locality →
      CausalSource (EncryptedAddress Address seedLength) time
  | .plain head =>
      match base.source time head with
      | .input address => .input (.plain address)
      | .generated previous => .generated previous
  | .priorSeed head bit dependency =>
      if htime : time < steps then
        match base.source time head with
        | .input _ => .input (.seed none)
        | .generated previous =>
            let previous' : Fin steps := ⟨previous, previous.isLt.trans htime⟩
            .input (.seed (some (generator.dependency
              (flatBitIndex previous' bit) dependency)))
      else .input (.seed none)
  | .currentSeed bit dependency =>
      if htime : time < steps then
        let time' : Fin steps := ⟨time, htime⟩
        .input (.seed (some (generator.dependency
          (flatBitIndex time' bit) dependency)))
      else .input (.seed none)

/-- Input interpretation for the encrypted simulator. -/
def encryptedInputValue
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width : ℕ}
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (input : Input × Bits seedLength) :
    EncryptedAddress Address seedLength → EncryptedValue Value width
  | .plain address => .plain (base.inputValue input.1 address)
  | .seed none => .seedBit false
  | .seed (some coordinate) => .seedBit (input.2 coordinate)

/-- The encrypted simulator's single local map. -/
def encryptedLocalMLP
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Inhabited Value]
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (time : ℕ)
    (attended : EncryptedHead Head width locality → EncryptedValue Value width) : Bits width :=
  if htime : time < steps then
    let current : Fin steps := ⟨time, htime⟩
    let plainAttended : Head → Value := fun head =>
      match base.source time head with
      | .input _ => (attended (.plain head)).getPlain
      | .generated previous =>
          let previous' : Fin steps := ⟨previous, previous.isLt.trans htime⟩
          let previousPad : Bits width := fun bit =>
            let output := flatBitIndex previous' bit
            generator.generate
              (reconstructedSeed generator output fun dependency =>
                (attended (.priorSeed head bit dependency)).getSeedBit) output
          base.tokenValue (code.decode (Encryption.bitXor
            (attended (.plain head)).getCiphertext previousPad))
    let nextPlain := base.localMLP time plainAttended
    let currentPad : Bits width := fun bit =>
      let output := flatBitIndex current bit
      generator.generate
        (reconstructedSeed generator output fun dependency =>
          (attended (.currentSeed bit dependency)).getSeedBit) output
    Encryption.bitXor (code.encode nextPlain) currentPad
  else fun _ => false

private theorem encryptedLocalMLP_correct
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Inhabited Value]
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) (time : Fin steps) :
    encryptedLocalMLP base code generator time (fun head =>
      match encryptedSource base generator time head with
      | .input (.plain address) => .plain (base.inputValue input address)
      | .input (.seed none) => .seedBit false
      | .input (.seed (some coordinate)) => .seedBit (seed coordinate)
      | .generated previous => .ciphertext
          (encryptedTokenTrace base.trace code generator input seed
            ⟨previous, previous.isLt.trans time.isLt⟩)) =
      encryptedTokenTrace base.trace code generator input seed time := by
  unfold encryptedLocalMLP
  rw [dif_pos time.isLt]
  unfold encryptedTokenTrace
  apply congrArg₂ Encryption.bitXor
  · apply congrArg code.encode
    change base.localMLP time _ = base.generated input time
    rw [base.generated_correct input time]
    congr 1
    funext head
    cases hsource : base.source time head with
    | input address =>
        simp [encryptedSource, hsource, EncryptedValue.getPlain]
    | generated previous =>
        simp only [hsource]
        simp [encryptedSource, hsource, time.isLt, EncryptedValue.getCiphertext,
          EncryptedValue.getSeedBit]
        have hpad :
            (fun bit =>
              generator.generate
                (reconstructedSeed generator
                  (flatBitIndex
                    (⟨previous, previous.isLt.trans time.isLt⟩ : Fin steps) bit)
                  fun dependency =>
                    seed (generator.dependency
                      (flatBitIndex
                        (⟨previous, previous.isLt.trans time.isLt⟩ : Fin steps) bit)
                      dependency))
                (flatBitIndex
                  (⟨previous, previous.isLt.trans time.isLt⟩ : Fin steps) bit)) =
              padBlock generator seed
                (⟨previous, previous.isLt.trans time.isLt⟩ : Fin steps) := by
          funext bit
          exact localGenerator_from_dependencies generator seed _
        rw [hpad, Encryption.bitXor_right_involutive, code.decode_encode]
        rfl
  · funext bit
    simpa [encryptedSource, time.isLt, EncryptedValue.getSeedBit] using
      (localGenerator_from_dependencies generator seed (flatBitIndex time bit))

/--
The actual causal one-layer encrypted Transformer.  Its ordinary heads carry
the base attention values (ciphertexts at generated positions), while the
additional heads fetch exactly the local PRG seed dependencies needed to
decrypt prior tokens and encrypt the current token inside the single local
map.
-/
def encryptedTransformer
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Inhabited Value]
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality) :
    OneLayerTransformer (Input × Bits seedLength)
      (EncryptedHead Head width locality) (EncryptedAddress Address seedLength)
      (EncryptedValue Value width) (Bits width) Output steps where
  inputValue := encryptedInputValue base
  tokenValue := .ciphertext
  source := encryptedSource base generator
  localMLP := encryptedLocalMLP base code generator
  generated := fun input time =>
    if htime : time < steps then
      encryptedTokenTrace base.trace code generator input.1 input.2 ⟨time, htime⟩
    else fun _ => false
  generated_correct := by
    intro input time
    rw [dif_pos time.isLt]
    symm
    rw [← encryptedLocalMLP_correct base code generator input.1 input.2 time]
    apply congrArg (encryptedLocalMLP base code generator time)
    funext encryptedHead
    cases encryptedHead with
    | plain head =>
        cases hsource : base.source time head with
        | input address => simp [encryptedSource, encryptedInputValue, hsource]
        | generated previous =>
            simp [encryptedSource, encryptedInputValue, hsource,
              previous.isLt.trans time.isLt]
    | priorSeed head bit dependency =>
        cases hsource : base.source time head with
        | input address =>
            simp [encryptedSource, encryptedInputValue, hsource, time.isLt]
        | generated previous =>
            simp [encryptedSource, encryptedInputValue, hsource, time.isLt]
    | currentSeed bit dependency =>
        simp [encryptedSource, encryptedInputValue, time.isLt]
  readout := fun input visible =>
    base.readout input.1 (fun time =>
      code.decode (Encryption.bitXor (visible time) (padBlock generator input.2 time)))

/-- Its generated tokens are exactly the online-encrypted base trace. -/
theorem encryptedTransformer_trace
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Inhabited Value]
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) :
    (encryptedTransformer base code generator).trace (input, seed) =
      encryptedTokenTrace base.trace code generator input seed := by
  funext time
  simp [OneLayerTransformer.trace, encryptedTransformer, time.isLt]

/-- The monitor-visible flattened implementation trace is the XOR ciphertext. -/
theorem encryptedTransformer_flat_trace
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Inhabited Value]
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) :
    flattenBitTrace ((encryptedTransformer base code generator).trace (input, seed)) =
      Encryption.encryptedTrace (encodedTrace base.trace code)
        (Encryption.prefixGenerator generator.generate) input seed := by
  funext index
  rcases hlocation : finProdFinEquiv.symm index with ⟨time, bit⟩
  have hindex : finProdFinEquiv (time, bit) = index := by
    rw [← hlocation]
    exact Equiv.apply_symm_apply finProdFinEquiv index
  rw [← hindex]
  simp [encryptedTokenTrace, padBlock, bitBlock, Encryption.encryptedTrace,
    Encryption.bitXor, Encryption.prefixGenerator, encodedTrace, flattenBitTrace,
    encryptedTransformer_trace]

/-- Decrypting the encrypted trace at readout preserves the base output. -/
theorem encryptedTransformer_output
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Inhabited Value]
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) :
    (encryptedTransformer base code generator).run (input, seed) = base.run input := by
  unfold OneLayerTransformer.run
  apply congrArg (base.readout input)
  funext time
  rw [encryptedTransformer_trace]
  simp [encryptedTokenTrace, Encryption.bitXor_right_involutive, code.decode_encode]

/-- The displayed head bound is the actual cardinality of the encrypted head type. -/
theorem encrypted_head_count
    {Head : Type*} [Fintype Head] (width locality : ℕ) :
    Fintype.card (EncryptedHead Head width locality) =
      encryptedHeadCount (Fintype.card Head) width locality := by
  let encode : EncryptedHead Head width locality →
      Head ⊕ (Head × Fin width × Fin locality) ⊕ (Fin width × Fin locality)
    | .plain head => .inl head
    | .priorSeed head bit dependency => .inr (.inl (head, bit, dependency))
    | .currentSeed bit dependency => .inr (.inr (bit, dependency))
  let decode : Head ⊕ (Head × Fin width × Fin locality) ⊕
      (Fin width × Fin locality) → EncryptedHead Head width locality
    | .inl head => .plain head
    | .inr (.inl (head, bit, dependency)) => .priorSeed head bit dependency
    | .inr (.inr (bit, dependency)) => .currentSeed bit dependency
  let equivalence : EncryptedHead Head width locality ≃
      Head ⊕ (Head × Fin width × Fin locality) ⊕ (Fin width × Fin locality) :=
    { toFun := encode
      invFun := decode
      left_inv := by intro head; cases head <;> rfl
      right_inv := by
        intro value
        rcases value with head | value
        · rfl
        · rcases value with value | value <;> rcases value with ⟨_, _, _⟩ <;> rfl }
  calc
    Fintype.card (EncryptedHead Head width locality) =
        Fintype.card (Head ⊕ (Head × Fin width × Fin locality) ⊕
          (Fin width × Fin locality)) := Fintype.card_congr equivalence
    _ = Fintype.card Head + Fintype.card Head * width * locality +
        width * locality := by simp [Nat.add_assoc, Nat.mul_assoc]
    _ = encryptedHeadCount (Fintype.card Head) width locality := by
      simp [encryptedHeadCount]
      ring


/--
A one-layer encrypted simulator: `base` supplies the causal one-layer
transition, and `implementation` is the causal encrypted Transformer itself.
The remaining fields expose its exact trace and its online transition law.
-/
structure EncryptedOneLayerTransformer
    (Input Head Address Value Token Output : Type*) [Fintype Head] [Inhabited Value]
    (steps seedLength width suffix locality : ℕ) where
  base : OneLayerTransformer Input Head Address Value Token Output steps
  code : BinaryCode Token width
  generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality
  implementation : OneLayerTransformer (Input × Bits seedLength)
    (EncryptedHead Head width locality) (EncryptedAddress Address seedLength)
    (EncryptedValue Value width) (Bits width) Output steps
  implementation_eq : implementation = encryptedTransformer base code generator
  headCount : ℕ
  headCount_eq : headCount =
    encryptedHeadCount (Fintype.card Head) width locality
  visibleTrace : Input → Bits seedLength → Fin steps → Bits width
  visible_eq : ∀ input seed time,
    visibleTrace input seed time =
      encryptedTokenTrace base.trace code generator input seed time
  online_correct : ∀ input seed time,
    visibleTrace input seed time =
      Encryption.bitXor
        (code.encode (base.localMLP time (fun head =>
          match base.source time head with
          | .input address => base.inputValue input address
          | .generated previous => base.tokenValue
              (decryptedTokenAt base.trace code generator input seed
                ⟨previous, previous.isLt.trans time.isLt⟩))))
        (padBlock generator seed time)

/-- Equip any one-layer plaintext simulator with online local-PRG encryption. -/
def encryptOneLayerTransformer
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Fintype Head] [Inhabited Value]
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality) :
    EncryptedOneLayerTransformer Input Head Address Value Token Output
      steps seedLength width suffix locality where
  base := base
  code := code
  generator := generator
  implementation := encryptedTransformer base code generator
  implementation_eq := rfl
  headCount := encryptedHeadCount (Fintype.card Head) width locality
  headCount_eq := rfl
  visibleTrace := encryptedTokenTrace base.trace code generator
  visible_eq := by intros; rfl
  online_correct := online_decrypt_transition_reencrypt base code generator

/-- The encrypted simulator retains the plaintext transformer's output. -/
theorem encryptOneLayerTransformer_output
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Fintype Head] [Inhabited Value]
    (base : OneLayerTransformer Input Head Address Value Token Output steps)
    (code : BinaryCode Token width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (input : Input) (seed : Bits seedLength) :
    (encryptOneLayerTransformer base code generator).implementation.run (input, seed) =
      base.run input :=
  encryptedTransformer_output base code generator input seed

/-- The wrapper's advertised head count is its implementation's actual head cardinality. -/
theorem EncryptedOneLayerTransformer.headCount_eq_actual
    {Input Head Address Value Token Output : Type*}
    {steps seedLength width suffix locality : ℕ} [Fintype Head] [Inhabited Value]
    (E : EncryptedOneLayerTransformer Input Head Address Value Token Output
      steps seedLength width suffix locality) :
    E.headCount = Fintype.card (EncryptedHead Head width locality) := by
  rw [E.headCount_eq, encrypted_head_count]

/-! ## End-to-end encrypted simulation theorems -/

omit [DecidableEq Tape] in
/--
General fixed-length form of “Encrypting CoTs using Few Random Bits”.  It
constructs the one-layer simulator rather than assuming a plaintext trace,
proves correct task output and the constant head bound, and supplies the
paper's no-readability conclusion for every finite input distribution and
predicate.
-/
theorem encrypting_cots_using_few_random_bits
    [Fintype Input]
    (M : Machine Input Tape Position State Symbol) (steps : ℕ)
    (readout : (Fin steps → StepToken Tape State Symbol) → Output)
    (target : Input → Output)
    (readout_correct : ∀ input, readout (M.trace steps input) = target input)
    {seedLength width suffix locality : ℕ}
    (code : BinaryCode (StepToken Tape State Symbol) width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (D : Encryption.FiniteDistribution Input)
    (fullMonitors : Encryption.MonitorClass (steps * width + suffix))
    (traceMonitors : Encryption.MonitorClass (steps * width)) (ε : ℝ)
    (secure : Encryption.SecureAgainst generator.generate fullMonitors ε)
    (prefixClosed : Encryption.PrefixClosed fullMonitors traceMonitors)
    (xorClosed : Encryption.XorClosed traceMonitors)
    (monitor : Encryption.Monitor (steps * width))
    (hmonitor : monitor ∈ traceMonitors) (predicate : Input → Bool) :
    ∃ E : EncryptedOneLayerTransformer Input (SimulationHead Tape)
        (InputAddress Tape Position) (AttentionValue Tape State Symbol)
        (StepToken Tape State Symbol) Output steps seedLength width suffix locality,
      (∀ input seed, E.implementation.run (input, seed) = target input) ∧
      Fintype.card (EncryptedHead (SimulationHead Tape) width locality) =
        encryptedHeadCount (Fintype.card Tape + 1) width locality ∧
      Encryption.predictionSuccess D
          (fun input seed => flattenBitTrace
            (E.implementation.trace (input, seed)))
          monitor predicate ≤ D.bestConstantSuccess predicate + ε := by
  let base := compile M steps readout
  let encrypted := encryptOneLayerTransformer base code generator
  refine ⟨encrypted, ?_, ?_, ?_⟩
  · intro input seed
    rw [encryptOneLayerTransformer_output]
    exact compile_output_correct M steps readout target readout_correct input
  · rw [encrypted_head_count, simulation_head_count (Tape := Tape)]
  · rw [show (fun input seed => flattenBitTrace
          (encrypted.implementation.trace (input, seed))) =
        Encryption.encryptedTrace (encodedTrace base.trace code)
          (Encryption.prefixGenerator generator.generate) by
      funext input seed
      exact encryptedTransformer_flat_trace base code generator input seed]
    exact Encryption.encrypted_trace_no_readability_of_local_generator D
      (encodedTrace base.trace code) generator fullMonitors traceMonitors ε secure
      prefixClosed xorClosed monitor hmonitor predicate

omit [DecidableEq Tape] in
/--
End-to-end finite form of “Transformers can Encrypt Reasoning”.  In addition
to constructing the one-layer online-encrypted simulator, it proves both sides
of the leakage/readability separation: the information footprint loses at
most `seedLength` bits, while every admissible monitor's prediction advantage
is at most the PRG advantage.
-/
theorem transformers_can_encrypt_reasoning
    [Fintype Input]
    (M : Machine Input Tape Position State Symbol) (steps : ℕ)
    (readout : (Fin steps → StepToken Tape State Symbol) → Output)
    (target : Input → Output)
    (readout_correct : ∀ input, readout (M.trace steps input) = target input)
    {seedLength width suffix locality : ℕ}
    (code : BinaryCode (StepToken Tape State Symbol) width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (D : Encryption.FiniteDistribution Input)
    (fullMonitors : Encryption.MonitorClass (steps * width + suffix))
    (traceMonitors : Encryption.MonitorClass (steps * width))
    (ε footprintLower : ℝ)
    (secure : Encryption.SecureAgainst generator.generate fullMonitors ε)
    (prefixClosed : Encryption.PrefixClosed fullMonitors traceMonitors)
    (xorClosed : Encryption.XorClosed traceMonitors)
    (profile : Encryption.PrivateRandomnessProfile seedLength)
    (fixedSeedFootprint : ∀ seed,
      footprintLower ≤ profile.fixedSeedInformation seed)
    (monitor : Encryption.Monitor (steps * width))
    (hmonitor : monitor ∈ traceMonitors) (predicate : Input → Bool) :
    ∃ E : EncryptedOneLayerTransformer Input (SimulationHead Tape)
        (InputAddress Tape Position) (AttentionValue Tape State Symbol)
        (StepToken Tape State Symbol) Output steps seedLength width suffix locality,
      (∀ input seed, E.implementation.run (input, seed) = target input) ∧
      Fintype.card (EncryptedHead (SimulationHead Tape) width locality) =
        encryptedHeadCount (Fintype.card Tape + 1) width locality ∧
      footprintLower - seedLength ≤ profile.traceMutualInformation ∧
      Encryption.predictionSuccess D
          (fun input seed => flattenBitTrace
            (E.implementation.trace (input, seed)))
          monitor predicate ≤ D.bestConstantSuccess predicate + ε := by
  let base := compile M steps readout
  let encrypted := encryptOneLayerTransformer base code generator
  refine ⟨encrypted, ?_, ?_, ?_, ?_⟩
  · intro input seed
    rw [encryptOneLayerTransformer_output]
    exact compile_output_correct M steps readout target readout_correct input
  · rw [encrypted_head_count, simulation_head_count (Tape := Tape)]
  · exact Encryption.randomness_cannot_erase_footprint
      profile footprintLower fixedSeedFootprint
  · rw [show (fun input seed => flattenBitTrace
          (encrypted.implementation.trace (input, seed))) =
        Encryption.encryptedTrace (encodedTrace base.trace code)
          (Encryption.prefixGenerator generator.generate) by
      funext input seed
      exact encryptedTransformer_flat_trace base code generator input seed]
    exact Encryption.encrypted_trace_no_readability_of_local_generator D
      (encodedTrace base.trace code) generator fullMonitors traceMonitors ε secure
      prefixClosed xorClosed monitor hmonitor predicate

/-! ## Exact length and context-window accounting -/

/-- A concrete representative of the standard `O(T log T)` overhead. -/
def obliviousTimeBound (time : ℕ) : ℕ :=
  time * (Nat.log2 (time + 1) + 1)

/-- Explicit constant-factor form of the cited `O(T log T)` overhead. -/
def scaledObliviousTimeBound (constant time : ℕ) : ℕ :=
  constant * obliviousTimeBound time

/-- Every oblivious `time`-step run fits the displayed `time log time` bound. -/
theorem time_le_obliviousTimeBound (time : ℕ) : time ≤ obliviousTimeBound time := by
  unfold obliviousTimeBound
  calc
    time = time * 1 := by omega
    _ ≤ time * (Nat.log2 (time + 1) + 1) := by
      apply Nat.mul_le_mul_left
      omega

/-- Context length including two separators, input, trace, and output. -/
def contextLength (inputLength traceLength outputLength : ℕ) : ℕ :=
  inputLength + traceLength + outputLength + 2

/-- Substituting the oblivious-simulation time bound into the context size. -/
theorem contextLength_le_oblivious_bound
    {inputLength steps outputLength time : ℕ}
    (steps_le : steps ≤ obliviousTimeBound time) :
    contextLength inputLength steps outputLength ≤
      inputLength + obliviousTimeBound time + outputLength + 2 := by
  unfold contextLength
  omega

/-- Context accounting with an explicit constant in the `O(T log T)` bound. -/
theorem contextLength_le_scaled_oblivious_bound
    {inputLength steps outputLength constant time : ℕ}
    (steps_le : steps ≤ scaledObliviousTimeBound constant time) :
    contextLength inputLength steps outputLength ≤
      inputLength + scaledObliviousTimeBound constant time + outputLength + 2 := by
  unfold contextLength
  omega

/-- Unconditional context bound for the constructed oblivious-machine trace. -/
theorem compiled_contextLength_le
    (inputLength steps outputLength : ℕ) :
    contextLength inputLength steps outputLength ≤
      inputLength + obliviousTimeBound steps + outputLength + 2 :=
  contextLength_le_oblivious_bound (time_le_obliviousTimeBound steps)

/-- The generated CoT itself has the claimed `O(T log T)` representative. -/
theorem traceLength_le_oblivious_bound
    {steps time : ℕ} (steps_le : steps ≤ obliviousTimeBound time) :
    steps ≤ time * (Nat.log2 (time + 1) + 1) := by
  exact steps_le

omit [DecidableEq Tape] in
/--
Bound propagation for an already-oblivious machine.  This generic lemma is
separate from `inputDependent_to_one_layer_oblivious_simulation`, which
constructs its simulator and proves its bound without such a hypothesis.
-/
theorem one_layer_oblivious_simulation_with_overhead
    (M : Machine Input Tape Position State Symbol) (steps : ℕ)
    (readout : (Fin steps → StepToken Tape State Symbol) → Output)
    (target : Input → Output)
    (readout_correct : ∀ input, readout (M.trace steps input) = target input)
    (inputLength outputLength originalTime constant : ℕ)
    (steps_le : steps ≤ scaledObliviousTimeBound constant originalTime) :
    ∃ T : OneLayerTransformer Input (SimulationHead Tape) (InputAddress Tape Position)
        (AttentionValue Tape State Symbol) (StepToken Tape State Symbol) Output steps,
      (∀ input, T.trace input = M.trace steps input) ∧
      (∀ input, T.run input = target input) ∧
      Fintype.card (SimulationHead Tape) = Fintype.card Tape + 1 ∧
      steps ≤ constant * originalTime * (Nat.log2 (originalTime + 1) + 1) ∧
      contextLength inputLength steps outputLength ≤
        inputLength + constant * originalTime *
          (Nat.log2 (originalTime + 1) + 1) + outputLength + 2 := by
  refine ⟨compile M steps readout, compile_trace_correct M steps readout,
    compile_output_correct M steps readout target readout_correct,
    simulation_head_count, ?_, ?_⟩
  · simpa [scaledObliviousTimeBound, obliviousTimeBound, Nat.mul_assoc] using steps_le
  · simpa [scaledObliviousTimeBound, obliviousTimeBound, Nat.mul_assoc] using
      (contextLength_le_scaled_oblivious_bound
        (inputLength := inputLength) (outputLength := outputLength) steps_le)

omit [DecidableEq Tape] in
/--
The encrypted implementation has the same bounded trace length and context
window.  Encryption changes the token alphabet and adds a constant number of
heads, but introduces no autoregressive steps.
-/
theorem encrypted_oblivious_simulation_with_overhead
    (M : Machine Input Tape Position State Symbol) (steps : ℕ)
    (readout : (Fin steps → StepToken Tape State Symbol) → Output)
    (target : Input → Output)
    (readout_correct : ∀ input, readout (M.trace steps input) = target input)
    {seedLength width suffix locality : ℕ}
    (code : BinaryCode (StepToken Tape State Symbol) width)
    (generator : Encryption.LocalGenerator seedLength (steps * width + suffix) locality)
    (inputLength outputLength originalTime constant : ℕ)
    (steps_le : steps ≤ scaledObliviousTimeBound constant originalTime) :
    ∃ E : EncryptedOneLayerTransformer Input (SimulationHead Tape)
        (InputAddress Tape Position) (AttentionValue Tape State Symbol)
        (StepToken Tape State Symbol) Output steps seedLength width suffix locality,
      (∀ input seed, E.implementation.run (input, seed) = target input) ∧
      (∀ input seed, flattenBitTrace (E.implementation.trace (input, seed)) =
        Encryption.encryptedTrace (encodedTrace E.base.trace E.code)
          (Encryption.prefixGenerator E.generator.generate) input seed) ∧
      Fintype.card (EncryptedHead (SimulationHead Tape) width locality) =
        encryptedHeadCount (Fintype.card Tape + 1) width locality ∧
      steps ≤ constant * originalTime * (Nat.log2 (originalTime + 1) + 1) ∧
      contextLength inputLength steps outputLength ≤
        inputLength + constant * originalTime *
          (Nat.log2 (originalTime + 1) + 1) + outputLength + 2 := by
  let base := compile M steps readout
  let encrypted := encryptOneLayerTransformer base code generator
  refine ⟨encrypted, ?_, ?_, ?_, ?_, ?_⟩
  · intro input seed
    rw [encryptOneLayerTransformer_output]
    exact compile_output_correct M steps readout target readout_correct input
  · intro input seed
    exact encryptedTransformer_flat_trace base code generator input seed
  · rw [encrypted_head_count, simulation_head_count (Tape := Tape)]
  · simpa [scaledObliviousTimeBound, obliviousTimeBound, Nat.mul_assoc] using steps_le
  · simpa [scaledObliviousTimeBound, obliviousTimeBound, Nat.mul_assoc] using
      (contextLength_le_scaled_oblivious_bound
        (inputLength := inputLength) (outputLength := outputLength) steps_le)

/--
Encrypted finite-control semantic simulation of the bounded source machine.
The displayed bounds count abstract events; binary length is
`(steps + 1) * width`, and `width` need not be a constant. Thus this result
does not establish the paper's efficient matrix Transformer construction.
-/
theorem inputDependent_to_encrypted_oblivious_simulation
    {Input Tape Position State Symbol Output : Type*}
    [Fintype Tape] [DecidableEq Tape] [Fintype Position] [DecidableEq Position]
    [Fintype State] [Fintype Symbol]
    [Inhabited Position] [Inhabited State] [Inhabited Symbol]
    (source : InputDependentMachine Input Tape Position State Symbol)
    (steps : ℕ) (finish : Configuration Tape Position State Symbol → Output)
    (target : Input → Output)
    (correct : ∀ input, finish (source.configurationAt input steps) = target input)
    {seedLength width suffix locality : ℕ}
    (code : BinaryCode
      (StepToken Unit (ObliviousControl Tape Position State Symbol) Unit) width)
    (generator : Encryption.LocalGenerator
      seedLength ((steps + 1) * width + suffix) locality)
    (inputLength outputLength : ℕ) :
    ∃ E : EncryptedOneLayerTransformer Input (SimulationHead Unit)
        (InputAddress Unit Unit)
        (AttentionValue Unit (ObliviousControl Tape Position State Symbol) Unit)
        (StepToken Unit (ObliviousControl Tape Position State Symbol) Unit)
        Output (steps + 1) seedLength width suffix locality,
      (∀ input seed, E.implementation.run (input, seed) = target input) ∧
      (∀ input seed, flattenBitTrace (E.implementation.trace (input, seed)) =
        Encryption.encryptedTrace (encodedTrace E.base.trace E.code)
          (Encryption.prefixGenerator E.generator.generate) input seed) ∧
      Fintype.card (EncryptedHead (SimulationHead Unit) width locality) =
        encryptedHeadCount 2 width locality ∧
      steps + 1 ≤ (steps + 1) * (Nat.log2 (steps + 2) + 1) ∧
      contextLength inputLength (steps + 1) outputLength ≤
        inputLength + obliviousTimeBound (steps + 1) + outputLength + 2 := by
  let base := compileInputDependentTransformer source steps finish
  let encrypted := encryptOneLayerTransformer base code generator
  refine ⟨encrypted, ?_, ?_, ?_, ?_, ?_⟩
  · intro input seed
    rw [encryptOneLayerTransformer_output]
    exact compileInputDependentTransformer_output source steps finish target correct input
  · intro input seed
    exact encryptedTransformer_flat_trace base code generator input seed
  · rw [encrypted_head_count]
    simp [SimulationHead]
  · calc
      steps + 1 = (steps + 1) * 1 := by omega
      _ ≤ (steps + 1) * (Nat.log2 (steps + 2) + 1) := by
        apply Nat.mul_le_mul_left
        omega
  · exact compiled_contextLength_le inputLength (steps + 1) outputLength

/--
Interface-level leakage/readability theorem for the finite-control shortcut.
It uses an abstract information profile and monitor-class closure fields.
`ConcreteReasoning` and `PolynomialEncryption` give concrete replacements
for those information/security interfaces. This shortcut still does not
establish efficient matrix realization or binary/runtime overhead.
-/
theorem inputDependent_transformers_can_encrypt_reasoning
    {Input Tape Position State Symbol Output : Type*}
    [Fintype Input] [Fintype Tape] [DecidableEq Tape]
    [Fintype Position] [DecidableEq Position] [Fintype State] [Fintype Symbol]
    [Inhabited Position] [Inhabited State] [Inhabited Symbol]
    (source : InputDependentMachine Input Tape Position State Symbol)
    (steps : ℕ) (finish : Configuration Tape Position State Symbol → Output)
    (target : Input → Output)
    (correct : ∀ input, finish (source.configurationAt input steps) = target input)
    {seedLength width suffix locality : ℕ}
    (code : BinaryCode
      (StepToken Unit (ObliviousControl Tape Position State Symbol) Unit) width)
    (generator : Encryption.LocalGenerator
      seedLength ((steps + 1) * width + suffix) locality)
    (D : Encryption.FiniteDistribution Input)
    (fullMonitors : Encryption.MonitorClass ((steps + 1) * width + suffix))
    (traceMonitors : Encryption.MonitorClass ((steps + 1) * width))
    (ε footprintLower : ℝ)
    (secure : Encryption.SecureAgainst generator.generate fullMonitors ε)
    (prefixClosed : Encryption.PrefixClosed fullMonitors traceMonitors)
    (xorClosed : Encryption.XorClosed traceMonitors)
    (profile : Encryption.PrivateRandomnessProfile seedLength)
    (fixedSeedFootprint : ∀ seed,
      footprintLower ≤ profile.fixedSeedInformation seed)
    (monitor : Encryption.Monitor ((steps + 1) * width))
    (hmonitor : monitor ∈ traceMonitors) (predicate : Input → Bool)
    (inputLength outputLength : ℕ) :
    ∃ E : EncryptedOneLayerTransformer Input (SimulationHead Unit)
        (InputAddress Unit Unit)
        (AttentionValue Unit (ObliviousControl Tape Position State Symbol) Unit)
        (StepToken Unit (ObliviousControl Tape Position State Symbol) Unit)
        Output (steps + 1) seedLength width suffix locality,
      (∀ input seed, E.implementation.run (input, seed) = target input) ∧
      Fintype.card (EncryptedHead (SimulationHead Unit) width locality) =
        encryptedHeadCount 2 width locality ∧
      footprintLower - seedLength ≤ profile.traceMutualInformation ∧
      Encryption.predictionSuccess D
          (fun input seed => flattenBitTrace
            (E.implementation.trace (input, seed)))
          monitor predicate ≤ D.bestConstantSuccess predicate + ε ∧
      steps + 1 ≤ (steps + 1) * (Nat.log2 (steps + 2) + 1) ∧
      contextLength inputLength (steps + 1) outputLength ≤
        inputLength + obliviousTimeBound (steps + 1) + outputLength + 2 := by
  have hreadout : ∀ input,
      inputDependentReadout finish
          ((compileInputDependent source).trace (steps + 1) input) = target input := by
    intro input
    unfold inputDependentReadout
    rw [compileInputDependent_trace]
    exact correct input
  obtain ⟨E, houtput, hheads, hfootprint, hsecurity⟩ :=
    transformers_can_encrypt_reasoning
      (M := compileInputDependent source) (steps := steps + 1)
      (readout := inputDependentReadout finish) target hreadout code generator D
      fullMonitors traceMonitors ε footprintLower secure prefixClosed xorClosed
      profile fixedSeedFootprint monitor hmonitor predicate
  refine ⟨E, houtput, ?_, hfootprint, hsecurity, ?_, ?_⟩
  · simpa using hheads
  · calc
      steps + 1 = (steps + 1) * 1 := by omega
      _ ≤ (steps + 1) * (Nat.log2 (steps + 2) + 1) := by
        apply Nat.mul_le_mul_left
        omega
  · exact compiled_contextLength_le inputLength (steps + 1) outputLength

end ObliviousSimulation
