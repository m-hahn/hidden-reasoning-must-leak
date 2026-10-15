import ObliviousSimulation

/-!
# Oblivious programs with fixed finite control

An instruction sequence fixes every memory address independently of the
input. Reads, writes, and local transitions operate on a fixed finite control
type and a fixed finite cell alphabet. Unlike the finite-configuration
shortcut, the control contains no whole-tape configuration. This is the
event-level backend for the efficient oblivious simulation construction.
-/

noncomputable section

namespace ObliviousProgram

open TransformerAC0 ObliviousSimulation

/-- A fixed-address finite-control instruction. -/
inductive Instruction (Address Control Symbol : Type*)
  | read (address : Address) (update : Control → Symbol → Control)
  | write (address : Address) (value : Control → Symbol)
  | modify (address : Address) (update : Control → Symbol → Symbol)
  | local (address : Address) (update : Control → Control)

namespace Instruction

variable {Address Control Symbol : Type*}

def address : Instruction Address Control Symbol → Address
  | .read address _ => address
  | .write address _ => address
  | .modify address _ => address
  | .local address _ => address

def nextControl : Instruction Address Control Symbol → Control → Symbol → Control
  | .read _ update, control, symbol => update control symbol
  | .write _ _, control, _ => control
  | .modify _ _, control, _ => control
  | .local _ update, control, _ => update control

def nextSymbol : Instruction Address Control Symbol → Control → Symbol → Symbol
  | .read _ _, _, symbol => symbol
  | .write _ value, control, _ => value control
  | .modify _ update, control, symbol => update control symbol
  | .local _ _, _, symbol => symbol

end Instruction

variable {Address Control Symbol : Type*}

/-- The last visit before `time` to an address. Its construction uses only
the address sequence and therefore supplies an actual oblivious schedule. -/
def lastBefore [DecidableEq Address] (position : ℕ → Address) :
    (time : ℕ) → Address → Option (Fin time)
  | 0, _ => none
  | time + 1, address =>
      if position time = address then some ⟨time, Nat.lt_succ_self time⟩
      else (lastBefore position time address).map Fin.castSucc

theorem lastBefore_some [DecidableEq Address] (position : ℕ → Address)
    (time : ℕ) (address : Address) (previous : Fin time)
    (hprevious : lastBefore position time address = some previous) :
    position previous = address ∧
      ∀ other, other < time → position other = address → other ≤ previous := by
  induction time generalizing address with
  | zero => exact Fin.elim0 previous
  | succ time ih =>
      by_cases hhead : position time = address
      · have hequal : (⟨time, Nat.lt_succ_self time⟩ : Fin (time + 1)) = previous :=
          Option.some.inj (by simpa [lastBefore, hhead] using hprevious)
        rw [← hequal]
        exact ⟨hhead, fun other hother _ => Nat.le_of_lt_succ hother⟩
      · cases hrec : lastBefore position time address with
        | none => simp [lastBefore, hhead, hrec] at hprevious
        | some before =>
            have hequal : before.castSucc = previous :=
              Option.some.inj (by simpa [lastBefore, hhead, hrec] using hprevious)
            rw [← hequal]
            have hbefore := ih address before hrec
            refine ⟨hbefore.1, ?_⟩
            intro other hother haddress
            have hlt : other < time := by
              by_contra hnot
              have heq : other = time := by omega
              subst other
              exact hhead haddress
            exact hbefore.2 other hlt haddress

theorem lastBefore_none [DecidableEq Address] (position : ℕ → Address)
    (time : ℕ) (address : Address) (hnone : lastBefore position time address = none) :
    ∀ previous, previous < time → position previous ≠ address := by
  induction time generalizing address with
  | zero => intros; omega
  | succ time ih =>
      have hhead : position time ≠ address := by
        intro heq
        simp [lastBefore, heq] at hnone
      have hrec : lastBefore position time address = none := by
        cases heq : lastBefore position time address <;> simp_all [lastBefore]
      intro previous hprevious hposition
      by_cases heq : previous = time
      · subst previous
        exact hhead hposition
      · exact ih address hrec previous (by omega) hposition

def schedule [DecidableEq Address] (position : ℕ → Address) : AccessSchedule Unit Address where
  position := fun time _ => position time
  prior := fun time _ => lastBefore position time (position time)
  prior_same := by
    intro time _ previous hprevious
    exact (lastBefore_some position time (position time) previous hprevious).1
  prior_latest := by
    intro time _ previous hprevious
    exact (lastBefore_some position time (position time) previous hprevious).2
  prior_none := by
    intro time _ hnone
    exact lastBefore_none position time (position time) hnone

structure Configuration (Address Control Symbol : Type*) where
  control : Control
  memory : Address → Symbol

def execute [DecidableEq Address]
    (instruction : Instruction Address Control Symbol)
    (configuration : Configuration Address Control Symbol) : Configuration Address Control Symbol :=
  let scanned := configuration.memory instruction.address
  { control := instruction.nextControl configuration.control scanned
    memory := fun address => if address = instruction.address then
      instruction.nextSymbol configuration.control scanned else configuration.memory address }

/-- The sequence of instructions and the initial finite control are fixed.
Only initial cell contents depend on the input. -/
structure Program (Input Address Control Symbol : Type*) where
  instruction : ℕ → Instruction Address Control Symbol
  initialControl : Control
  initialMemory : Input → Address → Symbol

namespace Program

variable {Input Address Control Symbol : Type*} [DecidableEq Address]

def configurationAt (program : Program Input Address Control Symbol) (input : Input) :
    ℕ → Configuration Address Control Symbol
  | 0 => ⟨program.initialControl, program.initialMemory input⟩
  | time + 1 => execute (program.instruction time) (program.configurationAt input time)

def position (program : Program Input Address Control Symbol) (time : ℕ) : Address :=
  (program.instruction time).address

/-- A token records the new control and the symbol retained/written at the
visited cell, both from constant finite alphabets. -/
def traceToken (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) :
    StepToken Unit Control Symbol :=
  let before := program.configurationAt input time
  let instruction := program.instruction time
  let scanned := before.memory instruction.address
  ⟨instruction.nextControl before.control scanned,
    fun _ => instruction.nextSymbol before.control scanned⟩

theorem traceToken_control (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) :
    (program.traceToken input time).state = (program.configurationAt input (time + 1)).control := rfl

theorem traceToken_write (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) :
    (program.traceToken input time).write () =
      (program.configurationAt input (time + 1)).memory (program.position time) := by
  simp [traceToken, configurationAt, execute, position]

/-- Memory at an unvisited address retains its initial contents. -/
theorem memory_initial_of_unvisited
    (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) (address : Address)
    (unvisited : ∀ previous, previous < time → program.position previous ≠ address) :
    (program.configurationAt input time).memory address = program.initialMemory input address := by
  induction time with
  | zero => rfl
  | succ time ih =>
      have hhead : address ≠ program.position time := (unvisited time (by omega)).symm
      simp only [configurationAt, execute, position] at hhead ⊢
      rw [if_neg hhead]
      exact ih (fun previous hprevious => unvisited previous (by omega))

/-- Between visits to an address its memory content does not change. -/
theorem memory_unchanged_between
    (program : Program Input Address Control Symbol) (input : Input) (first last : ℕ) (address : Address)
    (hle : first ≤ last)
    (unvisited : ∀ time, first ≤ time → time < last → program.position time ≠ address) :
    (program.configurationAt input last).memory address =
      (program.configurationAt input first).memory address := by
  induction last with
  | zero =>
      have heq : first = 0 := by omega
      subst first
      rfl
  | succ last ih =>
      by_cases heq : first = last + 1
      · subst first; rfl
      · have hfirst : first ≤ last := by omega
        have hhead : address ≠ program.position last := (unvisited last hfirst (by omega)).symm
        simp only [configurationAt, execute, position] at hhead ⊢
        rw [if_neg hhead]
        exact ih hfirst (fun time htime hlast => unvisited time htime (by omega))

/-- The last-write lookup equals the actual current memory value. -/
theorem scanned_eq_last_write (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) :
    (program.configurationAt input time).memory (program.position time) =
      match lastBefore program.position time (program.position time) with
      | none => program.initialMemory input (program.position time)
      | some previous => (program.traceToken input previous).write () := by
  cases hprior : lastBefore program.position time (program.position time) with
  | none =>
      exact program.memory_initial_of_unvisited input time _
        (lastBefore_none program.position time _ hprior)
  | some previous =>
      have hlast := lastBefore_some program.position time _ previous hprior
      have hunchanged := program.memory_unchanged_between input (previous.val + 1) time
        (program.position time) (by omega) (by
          intro other hafter hbefore haddress
          have hle := hlast.2 other hbefore haddress
          omega)
      rw [hunchanged, ← hlast.1, ← traceToken_write]

variable [Inhabited Control] [Inhabited Symbol]

def inputValue (program : Program Input Address Control Symbol) (input : Input) :
    InputAddress Unit Address → AttentionValue Unit Control Symbol
  | .initialState => .state program.initialControl
  | .initialCell _ address => .symbol (program.initialMemory input address)

def source (program : Program Input Address Control Symbol) (time : ℕ) :
    SimulationHead Unit → CausalSource (InputAddress Unit Address) time
  | none => previousSource time
  | some _ =>
      match lastBefore program.position time (program.position time) with
      | none => .input (.initialCell () (program.position time))
      | some previous => .generated previous

def localMLP (program : Program Input Address Control Symbol) (time : ℕ)
    (attended : SimulationHead Unit → AttentionValue Unit Control Symbol) : StepToken Unit Control Symbol :=
  let control := stateOfAttention (attended none)
  let scanned := symbolOfAttention () (attended (some ()))
  ⟨(program.instruction time).nextControl control scanned,
    fun _ => (program.instruction time).nextSymbol control scanned⟩

def attended (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) :
    SimulationHead Unit → AttentionValue Unit Control Symbol :=
  fun head => match program.source time head with
  | .input address => program.inputValue input address
  | .generated previous => .token (program.traceToken input previous)

theorem attended_state (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) :
    stateOfAttention (program.attended input time none) =
      (program.configurationAt input time).control := by
  cases time with
  | zero => rfl
  | succ time =>
      simp [attended, source, previousSource, stateOfAttention, traceToken_control]

theorem attended_symbol (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) :
    symbolOfAttention () (program.attended input time (some ())) =
      (program.configurationAt input time).memory (program.position time) := by
  rw [scanned_eq_last_write]
  cases hprior : lastBefore program.position time (program.position time) <;>
    simp [attended, source, hprior, inputValue, symbolOfAttention]

theorem generated_correct (program : Program Input Address Control Symbol) (input : Input) (time : ℕ) :
    program.traceToken input time = program.localMLP time (program.attended input time) := by
  unfold localMLP
  rw [attended_state, attended_symbol]
  rfl

/-- The private output is a finite function of the final control, rather than
an arbitrary function of the complete trace. -/
def readout (program : Program Input Address Control Symbol) (finish : Control → Output) :
    (steps : ℕ) → (Fin steps → StepToken Unit Control Symbol) → Output
  | 0, _ => finish program.initialControl
  | steps + 1, trace => finish (trace (Fin.last steps)).state

/-- Two causal heads suffice: one retrieves the preceding finite control,
and one retrieves the last write to the currently accessed cell. -/
def compile (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Output) :
    OneLayerTransformer Input (SimulationHead Unit) (InputAddress Unit Address)
      (AttentionValue Unit Control Symbol) (StepToken Unit Control Symbol) Output steps where
  inputValue := program.inputValue
  tokenValue := .token
  source := program.source
  localMLP := program.localMLP
  generated := program.traceToken
  generated_correct := fun input time => by
    apply Eq.trans (program.generated_correct input time)
    congr 1
    funext head
    unfold attended
    cases program.source time head <;> rfl
  readout := fun _ => program.readout finish steps

theorem compile_output (program : Program Input Address Control Symbol) (steps : ℕ)
    (finish : Control → Output) (input : Input) :
    (program.compile steps finish).run input =
      finish (program.configurationAt input steps).control := by
  cases steps with
  | zero => rfl
  | succ steps =>
      change finish (program.traceToken input steps).state = _
      rw [traceToken_control]

omit [Inhabited Control] [Inhabited Symbol] in
/-- The whole generated token alphabet is bounded independently of the
number of memory cells and the number of executed instructions. -/
theorem token_alphabet_card [Fintype Control] [Fintype Symbol] :
    Fintype.card (StepToken Unit Control Symbol) = Fintype.card Control * Fintype.card Symbol := by
  rw [← Fintype.card_congr (stepTokenEquiv Unit Control Symbol)]
  simp

theorem head_count : Fintype.card (SimulationHead Unit) = 2 := by simp [SimulationHead]

end Program

private theorem card_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
      omega

/-- A lossless token encoding with a width determined only by the fixed
finite control and cell alphabets. No input-length-dependent configuration
alphabet occurs in this construction. -/
def constantWidthCode (Control Symbol : Type*) [Fintype Control] [Fintype Symbol]
    [Inhabited Control] [Inhabited Symbol] :
    BinaryCode (StepToken Unit Control Symbol) (Fintype.card Control * Fintype.card Symbol) := by
  classical
  let width := Fintype.card Control * Fintype.card Symbol
  have hcard : Fintype.card (StepToken Unit Control Symbol) ≤ Fintype.card (Bits width) := by
    rw [Program.token_alphabet_card]
    simpa [Bits, width] using card_le_two_pow width
  let encode := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  exact { encode := encode
          decode := Function.invFun encode
          decode_encode := Function.leftInverse_invFun encode.injective }

end ObliviousProgram
