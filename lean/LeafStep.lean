import PhaseStack

/-!
# A constant-size leaf source-step program

At a leaf phase the simulated head is within `[-1,1]`. Three fixed-address
reads find the unique marker and apply the source transition. Five fixed
cell updates write the new symbol and new marker. Only a three-valued local
head index, one symbol, one direction and the source state are registers;
the unbounded tape remains memory.
-/

noncomputable section

namespace LeafStep

open ObliviousProgram ObliviousCopy RotationProgram ObliviousPhase

variable {State Symbol : Type*}

structure Registers (State Symbol : Type*) where
  state : State
  headIndex : Fin 3
  write : Symbol
  direction : Direction
  deriving Fintype

abbrev SimulatorConfiguration (State Symbol : Type*) :=
  ObliviousProgram.Configuration Address (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)

def headPosition (index : Fin 3) : ℤ := (index.val : ℤ) - 1

def selected (machine : Machine State Symbol) (state : State) (symbol : Symbol) (index : Fin 3) :
    Registers State Symbol :=
  let action := machine.transition state symbol
  ⟨action.1, index, action.2.1, action.2.2⟩

def readHead (machine : Machine State Symbol) (index : Fin 3) :
    Instruction Address (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol) :=
  .read (Sum.inl (headPosition index)) (fun control cell =>
    if cell.2 then { control with auxiliary := selected machine control.auxiliary.state cell.1 index }
      else control)

def readHeads (machine : Machine State Symbol) :
    List (Instruction Address (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  [readHead machine 0, readHead machine 1, readHead machine 2]

def writeCell (cell : ℤ) :
    Instruction Address (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol) :=
  .modify (Sum.inl cell) (fun control old =>
    (if cell = headPosition control.auxiliary.headIndex then control.auxiliary.write else old.1,
      decide (cell = headPosition control.auxiliary.headIndex + control.auxiliary.direction.displacement)))

def writeCells :
    List (Instruction Address (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  [writeCell (-2), writeCell (-1), writeCell 0, writeCell 1, writeCell 2]

def instructions (machine : Machine State Symbol) :
    List (Instruction Address (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  readHeads machine ++ writeCells

theorem instruction_count (machine : Machine State Symbol) : (instructions machine).length = 8 := rfl

def Represents (source : ObliviousPhase.Configuration State Symbol) (simulator : SimulatorConfiguration State Symbol) : Prop :=
  simulator.control.auxiliary.state = source.state ∧
    ∀ cell, simulator.memory (Sum.inl cell) = (source.tape cell, decide (cell = source.head))

theorem execute_readHead (machine : Machine State Symbol) (index : Fin 3)
    (configuration : SimulatorConfiguration State Symbol) :
    execute (readHead machine index) configuration =
      { configuration with control := if (configuration.memory (Sum.inl (headPosition index))).2 then
          { configuration.control with auxiliary := (selected machine configuration.control.auxiliary.state
            (configuration.memory (Sum.inl (headPosition index))).1 index) } else configuration.control } := by
  apply congrArg₂ (@ObliviousProgram.Configuration.mk Address
    (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol))
  · rfl
  · funext address
    simp only [execute, readHead, Instruction.address, Instruction.nextSymbol]
    split_ifs with heq
    · rw [heq]
    · rfl

theorem readHeads_correct (machine : Machine State Symbol) (source : ObliviousPhase.Configuration State Symbol)
    (configuration : SimulatorConfiguration State Symbol) (representation : Represents source configuration)
    (index : Fin 3) (head : source.head = headPosition index) :
    run (readHeads machine) configuration =
      { configuration with control := { configuration.control with auxiliary :=
          (selected machine source.state (source.tape source.head) index) } } := by
  unfold readHeads
  rw [run_cons, execute_readHead, run_cons, execute_readHead, run_cons, execute_readHead, run_nil]
  fin_cases index <;>
    simp [representation.2, head, headPosition, representation.1, selected]

theorem execute_writeCell (cell : ℤ) (configuration : SimulatorConfiguration State Symbol) :
    execute (writeCell cell) configuration =
      { configuration with memory := fun address => if address = Sum.inl cell then
        (if cell = headPosition configuration.control.auxiliary.headIndex then configuration.control.auxiliary.write
            else (configuration.memory address).1,
          decide (cell = headPosition configuration.control.auxiliary.headIndex +
            configuration.control.auxiliary.direction.displacement)) else configuration.memory address } := by
  apply congrArg₂ (@ObliviousProgram.Configuration.mk Address
    (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol))
  · rfl
  · funext address
    simp only [execute, writeCell, Instruction.address, Instruction.nextSymbol]
    by_cases heq : address = Sum.inl cell
    · simp only [if_pos heq]
      rw [heq]
    · simp only [if_neg heq]

theorem writeCells_control (configuration : SimulatorConfiguration State Symbol) :
    (run writeCells configuration).control = configuration.control := by
  simp only [writeCells, run_cons, execute_writeCell, run_nil]

theorem writeCells_memory (configuration : SimulatorConfiguration State Symbol) (cell : ℤ) :
    (run writeCells configuration).memory (Sum.inl cell) =
      if -2 ≤ cell ∧ cell ≤ 2 then
        (if cell = headPosition configuration.control.auxiliary.headIndex then configuration.control.auxiliary.write
            else (configuration.memory (Sum.inl cell)).1,
          decide (cell = headPosition configuration.control.auxiliary.headIndex +
            configuration.control.auxiliary.direction.displacement))
      else configuration.memory (Sum.inl cell) := by
  by_cases hcell : -2 ≤ cell ∧ cell ≤ 2
  · have hcases : cell = -2 ∨ cell = -1 ∨ cell = 0 ∨ cell = 1 ∨ cell = 2 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
      simp [writeCells, run_cons, execute_writeCell]
  · have hn2 : cell ≠ -2 := by omega
    have hn1 : cell ≠ -1 := by omega
    have hz : cell ≠ 0 := by omega
    have hp1 : cell ≠ 1 := by omega
    have hp2 : cell ≠ 2 := by omega
    simp [writeCells, run_cons, execute_writeCell, hcell, hn2, hn1, hz, hp1, hp2]

theorem writeCells_buffer (configuration : SimulatorConfiguration State Symbol) (cell : ℤ) :
    (run writeCells configuration).memory (Sum.inr cell) = configuration.memory (Sum.inr cell) := by
  simp [writeCells, run_cons, execute_writeCell]

/-- The actual eight-instruction leaf program preserves representation of
one complete source step, including the source state and every tape cell. -/
theorem step_correct (machine : Machine State Symbol) (source : ObliviousPhase.Configuration State Symbol)
    (configuration : SimulatorConfiguration State Symbol) (representation : Represents source configuration)
    (headBound : |source.head| ≤ 1) :
    Represents (machine.step source) (run (instructions machine) configuration) := by
  have hhead : TapeRotation.inside 1 source.head := abs_le.mp headBound
  let headIndex : Fin 3 := RotationProgram.index 1 source.head hhead
  have hposition : source.head = headPosition headIndex := (position_index 1 source.head hhead).symm
  unfold instructions
  rw [run_append, readHeads_correct machine source configuration representation headIndex hposition]
  constructor
  · rw [writeCells_control]
    dsimp only [selected, Machine.step]
  · intro cell
    rw [writeCells_memory]
    dsimp only [selected]
    rw [← hposition, representation.2]
    let direction := (machine.transition source.state (source.tape source.head)).2.2
    have hnewHead : |source.head + direction.displacement| ≤ 2 := by
      have h := abs_add source.head direction.displacement
      have hd := direction.abs_displacement_le_one
      omega
    change (if -2 ≤ cell ∧ cell ≤ 2 then
      (if cell = source.head then (machine.transition source.state (source.tape source.head)).2.1
        else source.tape cell, decide (cell = source.head + direction.displacement))
      else (source.tape cell, decide (cell = source.head))) = _
    by_cases hin : -2 ≤ cell ∧ cell ≤ 2
    · simp [hin, Machine.step, Function.update_apply, direction]
    · have hold : cell ≠ source.head := by have h := abs_le.mp headBound; omega
      have hnew : cell ≠ source.head + direction.displacement := by have h := abs_le.mp hnewHead; omega
      simp [hin, hold, hnew, Machine.step, Function.update_apply, direction]

theorem registers_card [Fintype State] [Fintype Symbol] :
    Fintype.card (Registers State Symbol) = 9 * Fintype.card State * Fintype.card Symbol := by
  let equivalence : Registers State Symbol ≃ State × Fin 3 × Symbol × Direction :=
    { toFun := fun registers => (registers.state, registers.headIndex, registers.write, registers.direction)
      invFun := fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hdirection : Fintype.card Direction = 3 := by decide
  rw [Fintype.card_congr equivalence]
  simp only [Fintype.card_prod, Fintype.card_fin, hdirection]
  ring

/-- A fully assembled source-step token alphabet remains constant when the
simulated tape capacity and time horizon grow. -/
theorem token_alphabet_card [Fintype State] [Fintype Symbol] :
    Fintype.card (ObliviousSimulation.StepToken Unit
      (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) =
      72 * Fintype.card State * Fintype.card Symbol ^ 3 := by
  rw [ObliviousProgram.Program.token_alphabet_card, ObliviousCopy.control_card, registers_card]
  simp only [HeadMarker.Cell, Fintype.card_prod, Fintype.card_bool]
  ring

end LeafStep
