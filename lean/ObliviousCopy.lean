import ObliviousProgram

/-!
# Fixed-address conditional copying

Every copied cell takes precisely two finite-control instructions: a read
into one held symbol, then a conditional write. The branch never changes
either address. Source/destination disjointness gives exact snapshot-copy
semantics for a whole scan, with arbitrary scan order. The control alphabet
contains one symbol and fixed auxiliary data, never a tape configuration.
-/

noncomputable section

namespace ObliviousCopy

open ObliviousProgram

structure Control (Aux Symbol : Type*) where
  auxiliary : Aux
  flag : Bool
  held : Symbol
  deriving Fintype

variable {Address Label Aux Symbol : Type*} [DecidableEq Address]

def run (instructions : List (Instruction Address C S)) (configuration : Configuration Address C S) :
    Configuration Address C S :=
  instructions.foldl (fun before instruction => execute instruction before) configuration

@[simp] theorem run_nil (configuration : Configuration Address C S) : run [] configuration = configuration := rfl

@[simp] theorem run_cons (instruction : Instruction Address C S)
    (instructions : List (Instruction Address C S)) (configuration : Configuration Address C S) :
    run (instruction :: instructions) configuration = run instructions (execute instruction configuration) := rfl

theorem run_append (first second : List (Instruction Address C S))
    (configuration : Configuration Address C S) :
    run (first ++ second) configuration = run second (run first configuration) := by
  exact List.foldl_append

/-- A finite instruction list is a genuine oblivious program; any execution
past the list is padded by a fixed-address no-op. -/
def program (instructions : List (Instruction Address C S)) (paddingAddress : Address)
    (initialControl : C) (initialMemory : Input → Address → S) : Program Input Address C S where
  instruction := fun time => if htime : time < instructions.length then instructions[time]
    else .local paddingAddress id
  initialControl := initialControl
  initialMemory := initialMemory

theorem program_prefix (instructions : List (Instruction Address C S)) (paddingAddress : Address)
    (initialControl : C) (initialMemory : Input → Address → S) (input : Input) (time : ℕ)
    (htime : time ≤ instructions.length) :
    ((program instructions paddingAddress initialControl initialMemory).configurationAt input time) =
      run (instructions.take time) ⟨initialControl, initialMemory input⟩ := by
  induction time with
  | zero => rfl
  | succ time ih =>
      have hlt : time < instructions.length := by omega
      rw [Program.configurationAt, ih (by omega), List.take_succ_eq_append_getElem hlt, run_append]
      simp only [program, dif_pos hlt, run_cons, run_nil]

theorem program_complete (instructions : List (Instruction Address C S)) (paddingAddress : Address)
    (initialControl : C) (initialMemory : Input → Address → S) (input : Input) :
    ((program instructions paddingAddress initialControl initialMemory).configurationAt input instructions.length) =
      run instructions ⟨initialControl, initialMemory input⟩ := by
  simpa using program_prefix instructions paddingAddress initialControl initialMemory input instructions.length le_rfl

def cell (source destination : Address) (enabled : Bool → Bool) :
    List (Instruction Address (Control Aux Symbol) Symbol) :=
  [.read source (fun control symbol => { control with held := symbol }),
    .modify destination (fun control symbol => if enabled control.flag then control.held else symbol)]

theorem run_cell (source destination : Address) (enabled : Bool → Bool)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) :
    run (cell source destination enabled) configuration =
      { control := { configuration.control with held := configuration.memory source }
        memory := fun address => if address = destination ∧ enabled configuration.control.flag = true then
          configuration.memory source else configuration.memory address } := by
  apply congrArg₂ (@Configuration.mk Address (Control Aux Symbol) Symbol)
  · rfl
  · funext address
    simp only [run, cell, List.foldl_cons, List.foldl_nil, execute,
      Instruction.address, Instruction.nextControl, Instruction.nextSymbol]
    by_cases hdest : address = destination
    · subst address
      cases hflag : enabled configuration.control.flag <;> simp [hflag]
      intro heq
      rw [heq]
    · simp [hdest]
      intro heq
      rw [heq]

def scan (source destination : Label → Address) (enabled : Bool → Bool) (labels : List Label) :
    List (Instruction Address (Control Aux Symbol) Symbol) :=
  labels.flatMap fun label => cell (source label) (destination label) enabled

theorem scan_length (source destination : Label → Address) (enabled : Bool → Bool) (labels : List Label) :
    (scan (Aux := Aux) (Symbol := Symbol) source destination enabled labels).length = 2 * labels.length := by
  induction labels with
  | nil => simp [scan]
  | cons label labels ih => simp [scan, cell] at ih ⊢; omega

theorem scan_control (source destination : Label → Address) (enabled : Bool → Bool) (labels : List Label)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) :
    (run (scan source destination enabled labels) configuration).control.auxiliary = configuration.control.auxiliary ∧
      (run (scan source destination enabled labels) configuration).control.flag = configuration.control.flag := by
  induction labels generalizing configuration with
  | nil => simp [scan]
  | cons label labels ih =>
      simp only [scan, List.flatMap_cons, run_append, run_cell]
      exact ih _

theorem scan_other (source destination : Label → Address) (enabled : Bool → Bool) (labels : List Label)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) (address : Address)
    (other : ∀ label ∈ labels, address ≠ destination label) :
    (run (scan source destination enabled labels) configuration).memory address = configuration.memory address := by
  induction labels generalizing configuration with
  | nil => rfl
  | cons label labels ih =>
      have hhead : address ≠ destination label := other label (by simp)
      have htail : ∀ label ∈ labels, address ≠ destination label := fun label h => other label (by simp [h])
      change (run (cell (source label) (destination label) enabled ++ scan source destination enabled labels)
        configuration).memory address = _
      rw [run_append]
      rw [ih _ htail, run_cell]
      simp [hhead]

theorem scan_source (source destination : Label → Address) (enabled : Bool → Bool) (labels : List Label)
    (disjoint : ∀ i j, source i ≠ destination j)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) (label : Label) :
    (run (scan source destination enabled labels) configuration).memory (source label) =
      configuration.memory (source label) :=
  scan_other source destination enabled labels configuration (source label) (fun other _ => disjoint label other)

/-- Every enabled destination receives its original source value. Disabled
destinations and unlisted destinations retain their original contents. -/
theorem scan_destination [DecidableEq Label]
    (source destination : Label → Address) (enabled : Bool → Bool) (labels : List Label)
    (injective : Function.Injective destination) (disjoint : ∀ i j, source i ≠ destination j)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) (label : Label) :
    (run (scan source destination enabled labels) configuration).memory (destination label) =
      if enabled configuration.control.flag = true ∧ label ∈ labels then
        configuration.memory (source label) else configuration.memory (destination label) := by
  induction labels generalizing configuration with
  | nil => simp [scan]
  | cons head labels ih =>
      change (run (cell (source head) (destination head) enabled ++ scan source destination enabled labels)
        configuration).memory (destination label) = _
      rw [run_append]
      rw [ih]
      rw [run_cell]
      dsimp only
      have hsource : source label ≠ destination head := disjoint label head
      have hdest : destination label = destination head ↔ label = head := injective.eq_iff
      simp only [hsource, false_and, if_false, hdest, List.mem_cons]
      by_cases henable : enabled configuration.control.flag = true
      · simp only [henable, true_and]
        by_cases hlabel : label = head
        · subst label; simp
        · simp [hlabel]
      · simp [henable]

theorem control_card [Fintype Aux] [Fintype Symbol] :
    Fintype.card (Control Aux Symbol) = 2 * Fintype.card Aux * Fintype.card Symbol := by
  let equivalence : Control Aux Symbol ≃ Aux × Bool × Symbol :=
    { toFun := fun control => (control.auxiliary, control.flag, control.held)
      invFun := fun triple => ⟨triple.1, triple.2.1, triple.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr equivalence]
  simp
  ring

end ObliviousCopy
