import MultitapeTuring
import LeafStep

/-!
# A genuinely local multitape leaf instruction program

Three fixed marker reads per tape collect the scanned symbols in fixed-size
registers. Only after all reads does one shared finite-control transition
run. Five fixed writes per tape then update the symbols and head markers.
The memory and arbitrary head coordinates are never stored in control.
-/

noncomputable section
namespace MultitapeLeaf
open ObliviousProgram ObliviousCopy RotationProgram ObliviousPhase

variable {tapes : ℕ} {State Symbol : Type*}

structure Registers (tapes : ℕ) (State Symbol : Type*) where
  state : State
  headIndex : Fin tapes → Fin 3
  scanned : Fin tapes → Symbol
  write : Fin tapes → Symbol
  direction : Fin tapes → Direction

def registersEquiv : Registers tapes State Symbol ≃
    State × (Fin tapes → Fin 3) × (Fin tapes → Symbol) × (Fin tapes → Symbol) × (Fin tapes → Direction) where
  toFun registers := (registers.state, registers.headIndex, registers.scanned, registers.write, registers.direction)
  invFun value := ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance registersFintype [Fintype State] [Fintype Symbol] : Fintype (Registers tapes State Symbol) :=
  Fintype.ofEquiv _ registersEquiv.symm

@[ext] theorem Registers.ext {first second : Registers tapes State Symbol}
    (state : first.state = second.state) (headIndex : first.headIndex = second.headIndex)
    (scanned : first.scanned = second.scanned) (write : first.write = second.write)
    (direction : first.direction = second.direction) : first = second := by
  cases first
  cases second
  simp_all

abbrev SimulatorConfiguration (tapes : ℕ) (State Symbol : Type*) :=
  ObliviousProgram.Configuration (Fin tapes × Address)
    (Control (Registers tapes State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)

abbrev StepInstruction (tapes : ℕ) (State Symbol : Type*) :=
  Instruction (Fin tapes × Address) (Control (Registers tapes State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)

def setScanned (registers : Registers tapes State Symbol) (tape : Fin tapes) (index : Fin 3) (symbol : Symbol) :
    Registers tapes State Symbol :=
  { registers with
    headIndex := Function.update registers.headIndex tape index
    scanned := Function.update registers.scanned tape symbol }

def readHead (tape : Fin tapes) (index : Fin 3) : StepInstruction tapes State Symbol :=
  .read (tape, Sum.inl (LeafStep.headPosition index)) (fun control cell =>
    if cell.2 then { control with auxiliary := setScanned control.auxiliary tape index cell.1 } else control)

def readTape (tape : Fin tapes) : List (StepInstruction tapes State Symbol) :=
  [readHead tape 0, readHead tape 1, readHead tape 2]

def readList (indices : List (Fin tapes)) : List (StepInstruction tapes State Symbol) := indices.flatMap readTape
def readTapes : List (StepInstruction tapes State Symbol) := readList (List.finRange tapes)

def collect (registers : Registers tapes State Symbol) (indices : List (Fin tapes))
    (headIndices : Fin tapes → Fin 3) (symbols : Fin tapes → Symbol) : Registers tapes State Symbol :=
  { registers with
    headIndex := fun tape => if tape ∈ indices then headIndices tape else registers.headIndex tape
    scanned := fun tape => if tape ∈ indices then symbols tape else registers.scanned tape }

def Represents (source : MultitapeTuring.Configuration tapes State Symbol)
    (simulator : SimulatorConfiguration tapes State Symbol) : Prop :=
  simulator.control.auxiliary.state = source.state ∧
    ∀ tape cell, simulator.memory (tape, Sum.inl cell) = (source.tape tape cell, decide (cell = source.head tape))

theorem execute_readHead (tape : Fin tapes) (index : Fin 3)
    (configuration : SimulatorConfiguration tapes State Symbol) :
    execute (readHead tape index) configuration =
      { configuration with control := if (configuration.memory (tape, Sum.inl (LeafStep.headPosition index))).2 then
          { configuration.control with auxiliary := (setScanned configuration.control.auxiliary tape index
            (configuration.memory (tape, Sum.inl (LeafStep.headPosition index))).1) } else configuration.control } := by
  apply congrArg₂ (@ObliviousProgram.Configuration.mk (Fin tapes × Address)
    (Control (Registers tapes State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol))
  · rfl
  · funext address
    simp only [execute, readHead, Instruction.address, Instruction.nextSymbol]
    split_ifs with heq
    · rw [heq]
    · rfl

theorem readTape_correct (tape : Fin tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol)
    (configuration : SimulatorConfiguration tapes State Symbol)
    (memory : ∀ tape cell, configuration.memory (tape, Sum.inl cell) =
      (source.tape tape cell, decide (cell = source.head tape)))
    (index : Fin 3) (head : source.head tape = LeafStep.headPosition index) :
    run (readTape tape) configuration =
      { configuration with control := { configuration.control with auxiliary :=
          (setScanned configuration.control.auxiliary tape index (source.tape tape (source.head tape))) } } := by
  unfold readTape
  rw [run_cons, execute_readHead, run_cons, execute_readHead, run_cons, execute_readHead, run_nil]
  fin_cases index <;> simp [memory, head, LeafStep.headPosition]

theorem collect_cons (registers : Registers tapes State Symbol) (tape : Fin tapes) (indices : List (Fin tapes))
    (headIndices : Fin tapes → Fin 3) (symbols : Fin tapes → Symbol) :
    collect (setScanned registers tape (headIndices tape) (symbols tape)) indices headIndices symbols =
      collect registers (tape :: indices) headIndices symbols := by
  apply Registers.ext
  · rfl
  · funext other
    by_cases heq : other = tape <;> by_cases hmem : other ∈ indices <;> simp [collect, setScanned, heq, hmem]
  · funext other
    by_cases heq : other = tape <;> by_cases hmem : other ∈ indices <;> simp [collect, setScanned, heq, hmem]
  · rfl
  · rfl

theorem readList_correct (indices : List (Fin tapes))
    (source : MultitapeTuring.Configuration tapes State Symbol)
    (configuration : SimulatorConfiguration tapes State Symbol)
    (memory : ∀ tape cell, configuration.memory (tape, Sum.inl cell) =
      (source.tape tape cell, decide (cell = source.head tape)))
    (headIndices : Fin tapes → Fin 3) (heads : ∀ tape, source.head tape = LeafStep.headPosition (headIndices tape)) :
    run (readList indices) configuration =
      { configuration with control := { configuration.control with auxiliary :=
          (collect configuration.control.auxiliary indices headIndices (MultitapeTuring.Machine.scanned source)) } } := by
  induction indices generalizing configuration with
  | nil => simp [readList, collect]
  | cons tape rest ih =>
      simp only [readList, List.flatMap_cons, run_append]
      rw [readTape_correct tape source configuration memory (headIndices tape) (heads tape)]
      rw [← readList, ih]
      · exact congrArg (fun registers : Registers tapes State Symbol =>
          { configuration with control := { configuration.control with auxiliary := registers } })
          (collect_cons configuration.control.auxiliary tape rest headIndices (MultitapeTuring.Machine.scanned source))
      · exact memory

theorem readTapes_correct
    (source : MultitapeTuring.Configuration tapes State Symbol)
    (configuration : SimulatorConfiguration tapes State Symbol)
    (memory : ∀ tape cell, configuration.memory (tape, Sum.inl cell) =
      (source.tape tape cell, decide (cell = source.head tape)))
    (headIndices : Fin tapes → Fin 3) (heads : ∀ tape, source.head tape = LeafStep.headPosition (headIndices tape)) :
    run readTapes configuration =
      { configuration with control := { configuration.control with auxiliary :=
          { configuration.control.auxiliary with
            headIndex := headIndices
            scanned := MultitapeTuring.Machine.scanned source } } } := by
  rw [readTapes, readList_correct _ source configuration memory headIndices heads]
  simp [collect]

def applyTransition (machine : MultitapeTuring.Machine tapes State Symbol) (registers : Registers tapes State Symbol) :
    Registers tapes State Symbol :=
  let action := machine.transition registers.state registers.scanned
  { registers with state := action.1, write := action.2.1, direction := action.2.2 }

def compute (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) : StepInstruction tapes State Symbol :=
  .local (anchor, Sum.inr 0) (fun control => { control with auxiliary := applyTransition machine control.auxiliary })

theorem execute_compute (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (configuration : SimulatorConfiguration tapes State Symbol) :
    execute (compute machine anchor) configuration =
      { configuration with control := { configuration.control with auxiliary := applyTransition machine configuration.control.auxiliary } } := by
  apply congrArg₂ (@ObliviousProgram.Configuration.mk (Fin tapes × Address)
    (Control (Registers tapes State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol))
  · rfl
  · funext address
    simp only [execute, compute, Instruction.address, Instruction.nextSymbol]
    split_ifs with heq
    · rw [heq]
    · rfl

def writeCell (tape : Fin tapes) (cell : ℤ) : StepInstruction tapes State Symbol :=
  .modify (tape, Sum.inl cell) (fun control old =>
    (if cell = LeafStep.headPosition (control.auxiliary.headIndex tape) then control.auxiliary.write tape else old.1,
      decide (cell = LeafStep.headPosition (control.auxiliary.headIndex tape) +
        (control.auxiliary.direction tape).displacement)))

def writeTape (tape : Fin tapes) : List (StepInstruction tapes State Symbol) :=
  [writeCell tape (-2), writeCell tape (-1), writeCell tape 0, writeCell tape 1, writeCell tape 2]

def writeList (indices : List (Fin tapes)) : List (StepInstruction tapes State Symbol) := indices.flatMap writeTape
def writeTapes : List (StepInstruction tapes State Symbol) := writeList (List.finRange tapes)

def instructions (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) :
    List (StepInstruction tapes State Symbol) := readTapes ++ [compute machine anchor] ++ writeTapes

theorem instruction_count (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) :
    (instructions machine anchor).length = 8 * tapes + 1 := by
  simp [instructions, readTapes, readList, writeTapes, writeList, List.length_flatMap, readTape, writeTape,
    List.length_finRange]
  omega

theorem execute_writeCell (tape : Fin tapes) (cell : ℤ)
    (configuration : SimulatorConfiguration tapes State Symbol) :
    execute (writeCell tape cell) configuration =
      { configuration with memory := fun address => if address = (tape, Sum.inl cell) then
        (if cell = LeafStep.headPosition (configuration.control.auxiliary.headIndex tape) then configuration.control.auxiliary.write tape
            else (configuration.memory address).1,
          decide (cell = LeafStep.headPosition (configuration.control.auxiliary.headIndex tape) +
            (configuration.control.auxiliary.direction tape).displacement)) else configuration.memory address } := by
  apply congrArg₂ (@ObliviousProgram.Configuration.mk (Fin tapes × Address)
    (Control (Registers tapes State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol))
  · rfl
  · funext address
    simp only [execute, writeCell, Instruction.address, Instruction.nextSymbol]
    by_cases heq : address = (tape, Sum.inl cell)
    · simp only [if_pos heq]
      rw [heq]
    · simp only [if_neg heq]

theorem writeTape_control (tape : Fin tapes) (configuration : SimulatorConfiguration tapes State Symbol) :
    (run (writeTape tape) configuration).control = configuration.control := by
  simp only [writeTape, run_cons, execute_writeCell, run_nil]

def updatedCell (registers : Registers tapes State Symbol) (tape : Fin tapes) (cell : ℤ)
    (old : HeadMarker.Cell Symbol) : HeadMarker.Cell Symbol :=
  if -2 ≤ cell ∧ cell ≤ 2 then
    (if cell = LeafStep.headPosition (registers.headIndex tape) then registers.write tape else old.1,
      decide (cell = LeafStep.headPosition (registers.headIndex tape) + (registers.direction tape).displacement))
  else old

theorem updatedCell_idempotent (registers : Registers tapes State Symbol) (tape : Fin tapes) (cell : ℤ)
    (old : HeadMarker.Cell Symbol) :
    updatedCell registers tape cell (updatedCell registers tape cell old) = updatedCell registers tape cell old := by
  unfold updatedCell
  split_ifs <;> rfl

theorem writeTape_memory (tape : Fin tapes) (configuration : SimulatorConfiguration tapes State Symbol) (cell : ℤ) :
    (run (writeTape tape) configuration).memory (tape, Sum.inl cell) =
      updatedCell configuration.control.auxiliary tape cell (configuration.memory (tape, Sum.inl cell)) := by
  by_cases hcell : -2 ≤ cell ∧ cell ≤ 2
  · have hcases : cell = -2 ∨ cell = -1 ∨ cell = 0 ∨ cell = 1 ∨ cell = 2 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
      simp [writeTape, run_cons, execute_writeCell, updatedCell]
  · have hn2 : cell ≠ -2 := by omega
    have hn1 : cell ≠ -1 := by omega
    have hz : cell ≠ 0 := by omega
    have hp1 : cell ≠ 1 := by omega
    have hp2 : cell ≠ 2 := by omega
    simp [writeTape, run_cons, execute_writeCell, updatedCell, hcell, hn2, hn1, hz, hp1, hp2]

theorem writeTape_other (tape other : Fin tapes) (different : other ≠ tape)
    (configuration : SimulatorConfiguration tapes State Symbol) (address : Address) :
    (run (writeTape tape) configuration).memory (other, address) = configuration.memory (other, address) := by
  simp [writeTape, run_cons, execute_writeCell, different]

theorem writeTape_buffer (tape other : Fin tapes)
    (configuration : SimulatorConfiguration tapes State Symbol) (cell : ℤ) :
    (run (writeTape tape) configuration).memory (other, Sum.inr cell) = configuration.memory (other, Sum.inr cell) := by
  simp [writeTape, run_cons, execute_writeCell]

theorem writeList_control (indices : List (Fin tapes)) (configuration : SimulatorConfiguration tapes State Symbol) :
    (run (writeList indices) configuration).control = configuration.control := by
  induction indices generalizing configuration with
  | nil => rfl
  | cons tape rest ih =>
      simp only [writeList, List.flatMap_cons, run_append]
      rw [← writeList, ih, writeTape_control]

theorem writeList_memory (indices : List (Fin tapes)) (configuration : SimulatorConfiguration tapes State Symbol)
    (tape : Fin tapes) (cell : ℤ) :
    (run (writeList indices) configuration).memory (tape, Sum.inl cell) =
      if tape ∈ indices then updatedCell configuration.control.auxiliary tape cell (configuration.memory (tape, Sum.inl cell))
      else configuration.memory (tape, Sum.inl cell) := by
  induction indices generalizing configuration with
  | nil => simp [writeList]
  | cons other rest ih =>
      simp only [writeList, List.flatMap_cons, run_append]
      rw [← writeList, ih, writeTape_control]
      by_cases heq : tape = other
      · subst other
        rw [writeTape_memory]
        by_cases hmem : tape ∈ rest <;> simp [hmem, updatedCell_idempotent]
      · rw [writeTape_other other tape heq]
        simp [heq]

theorem writeTapes_control (configuration : SimulatorConfiguration tapes State Symbol) :
    (run writeTapes configuration).control = configuration.control := writeList_control _ _

theorem writeTapes_memory (configuration : SimulatorConfiguration tapes State Symbol) (tape : Fin tapes) (cell : ℤ) :
    (run writeTapes configuration).memory (tape, Sum.inl cell) =
      updatedCell configuration.control.auxiliary tape cell (configuration.memory (tape, Sum.inl cell)) := by
  rw [writeTapes, writeList_memory]
  simp

theorem writeList_buffer (indices : List (Fin tapes)) (configuration : SimulatorConfiguration tapes State Symbol)
    (tape : Fin tapes) (cell : ℤ) :
    (run (writeList indices) configuration).memory (tape, Sum.inr cell) = configuration.memory (tape, Sum.inr cell) := by
  induction indices generalizing configuration with
  | nil => rfl
  | cons other rest ih =>
      simp only [writeList, List.flatMap_cons, run_append]
      rw [← writeList, ih, writeTape_buffer]

/-- All source tapes and the shared control are updated by the actual
`8 K + 1` fixed-address instructions. The only location premise is the
leaf's numerical head bound, not a simulation certificate. -/
theorem step_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol) (configuration : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source configuration) (headBounds : ∀ tape, |source.head tape| ≤ 1) :
    Represents (machine.step source) (run (instructions machine anchor) configuration) := by
  let headIndices : Fin tapes → Fin 3 := fun tape =>
    RotationProgram.index 1 (source.head tape) (abs_le.mp (headBounds tape))
  have hheads : ∀ tape, source.head tape = LeafStep.headPosition (headIndices tape) := by
    intro tape
    exact (position_index 1 (source.head tape) (abs_le.mp (headBounds tape))).symm
  unfold instructions
  rw [run_append, run_append, readTapes_correct source configuration representation.2 headIndices hheads,
    run_cons, execute_compute, run_nil]
  constructor
  · rw [writeTapes_control]
    simp only [applyTransition, representation.1, MultitapeTuring.Machine.step]
  · intro tape cell
    rw [writeTapes_memory]
    dsimp only [applyTransition]
    rw [representation.1, representation.2]
    simp only [updatedCell, ← hheads]
    let direction := (machine.transition source.state (MultitapeTuring.Machine.scanned source)).2.2 tape
    have hnewHead : |source.head tape + direction.displacement| ≤ 2 := by
      have h := abs_add (source.head tape) direction.displacement
      have hd := direction.abs_displacement_le_one
      have hh := headBounds tape
      omega
    by_cases hin : -2 ≤ cell ∧ cell ≤ 2
    · simp [hin, MultitapeTuring.Machine.step, Function.update_apply, direction]
    · have hold : cell ≠ source.head tape := by have h := abs_le.mp (headBounds tape); omega
      have hnew : cell ≠ source.head tape + direction.displacement := by have h := abs_le.mp hnewHead; omega
      simp [hin, hold, hnew, MultitapeTuring.Machine.step, Function.update_apply, direction]

theorem registers_card [Fintype State] [Fintype Symbol] :
    Fintype.card (Registers tapes State Symbol) = Fintype.card State * 9 ^ tapes * Fintype.card Symbol ^ (2 * tapes) := by
  rw [Fintype.card_congr registersEquiv]
  have hdirection : Fintype.card Direction = 3 := by decide
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hdirection]
  rw [show 9 = 3 * 3 by decide, mul_pow, show 2 * tapes = tapes + tapes by omega, pow_add]
  ring

theorem readTape_memory (tape : Fin tapes) (configuration : SimulatorConfiguration tapes State Symbol) :
    (run (readTape tape) configuration).memory = configuration.memory := by
  simp only [readTape, run_cons, execute_readHead, run_nil]

theorem readList_memory (indices : List (Fin tapes)) (configuration : SimulatorConfiguration tapes State Symbol) :
    (run (readList indices) configuration).memory = configuration.memory := by
  induction indices generalizing configuration with
  | nil => rfl
  | cons tape rest ih =>
      simp only [readList, List.flatMap_cons, run_append]
      rw [← readList, ih, readTape_memory]

theorem instructions_buffer (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (configuration : SimulatorConfiguration tapes State Symbol) (tape : Fin tapes) (cell : ℤ) :
    (run (instructions machine anchor) configuration).memory (tape, Sum.inr cell) =
      configuration.memory (tape, Sum.inr cell) := by
  unfold instructions
  rw [run_append, run_append]
  rw [writeTapes, writeList_buffer, run_cons, execute_compute, run_nil]
  exact congrFun (readList_memory _ configuration) (tape, Sum.inr cell)

end MultitapeLeaf
