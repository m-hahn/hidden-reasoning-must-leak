import PhaseStack

/-!
# Exact lifting of fixed-address programs to multiple tapes

Each lifted instruction retains the original fixed finite control and cell
alphabet, changing only its address to a tape/address pair. Execution on
the selected tape is exactly the original program; every other tape's
memory is untouched. Instruction count is unchanged. These are the actual
instruction-level adapters for the efficient multitape extension.
-/

noncomputable section
namespace TapeProgram
open ObliviousProgram ObliviousCopy

variable {Tape Address Control Symbol : Type*} [DecidableEq Tape] [DecidableEq Address]

def liftInstruction (tape : Tape) : Instruction Address Control Symbol → Instruction (Tape × Address) Control Symbol
  | .read address update => .read (tape, address) update
  | .write address value => .write (tape, address) value
  | .modify address update => .modify (tape, address) update
  | .local address update => .local (tape, address) update

omit [DecidableEq Tape] [DecidableEq Address] in
@[simp] theorem lifted_address (tape : Tape) (instruction : Instruction Address Control Symbol) :
    (liftInstruction tape instruction).address = (tape, instruction.address) := by cases instruction <;> rfl

omit [DecidableEq Tape] [DecidableEq Address] in
@[simp] theorem lifted_control (tape : Tape) (instruction : Instruction Address Control Symbol)
    (control : Control) (symbol : Symbol) :
    (liftInstruction tape instruction).nextControl control symbol = instruction.nextControl control symbol := by
  cases instruction <;> rfl

omit [DecidableEq Tape] [DecidableEq Address] in
@[simp] theorem lifted_symbol (tape : Tape) (instruction : Instruction Address Control Symbol)
    (control : Control) (symbol : Symbol) :
    (liftInstruction tape instruction).nextSymbol control symbol = instruction.nextSymbol control symbol := by
  cases instruction <;> rfl

def project (tape : Tape) (configuration : Configuration (Tape × Address) Control Symbol) :
    Configuration Address Control Symbol := ⟨configuration.control, fun address => configuration.memory (tape, address)⟩

theorem execute_project (tape : Tape) (instruction : Instruction Address Control Symbol)
    (configuration : Configuration (Tape × Address) Control Symbol) :
    project tape (execute (liftInstruction tape instruction) configuration) = execute instruction (project tape configuration) := by
  apply congrArg₂ (@Configuration.mk Address Control Symbol)
  · simp [project, execute]
  · funext address
    simp [project, execute]

theorem execute_other (tape other : Tape) (different : other ≠ tape)
    (instruction : Instruction Address Control Symbol) (configuration : Configuration (Tape × Address) Control Symbol)
    (address : Address) :
    (execute (liftInstruction tape instruction) configuration).memory (other, address) = configuration.memory (other, address) := by
  simp [execute, different]

def lift (tape : Tape) (instructions : List (Instruction Address Control Symbol)) :
    List (Instruction (Tape × Address) Control Symbol) := instructions.map (liftInstruction tape)

omit [DecidableEq Tape] [DecidableEq Address] in
@[simp] theorem lift_length (tape : Tape) (instructions : List (Instruction Address Control Symbol)) :
    (lift tape instructions).length = instructions.length := by simp [lift]

theorem run_project (tape : Tape) (instructions : List (Instruction Address Control Symbol))
    (configuration : Configuration (Tape × Address) Control Symbol) :
    project tape (run (lift tape instructions) configuration) = run instructions (project tape configuration) := by
  induction instructions generalizing configuration with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [lift, List.map_cons, run_cons]
      rw [← lift, ih, execute_project]

theorem run_other (tape other : Tape) (different : other ≠ tape)
    (instructions : List (Instruction Address Control Symbol))
    (configuration : Configuration (Tape × Address) Control Symbol) (address : Address) :
    (run (lift tape instructions) configuration).memory (other, address) = configuration.memory (other, address) := by
  induction instructions generalizing configuration with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [lift, List.map_cons, run_cons]
      rw [← lift, ih, execute_other tape other different]

end TapeProgram

namespace MultitapeCompression
open ObliviousProgram ObliviousCopy ObliviousPhase RotationProgram

variable {tapes : ℕ} {State Symbol : Type*}

abbrev SimulatorConfiguration (tapes : ℕ) (State Symbol : Type*) :=
  ObliviousProgram.Configuration (Fin tapes × Address) (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)

def compress (tape : Fin tapes) (half : ℕ) :
    List (Instruction (Fin tapes × Address) (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  TapeProgram.lift tape (CompressedTape.compress half)

theorem compress_length (tape : Fin tapes) (half : ℕ) :
    (compress (State := State) (Symbol := Symbol) tape half).length = 112 * half + 8 := by
  rw [compress, TapeProgram.lift_length, CompressedTape.compress_length]

/-- The compression is still the actual marker/rotation instruction list.
Only the selected tape changes; the unbounded tapes are never control. -/
theorem compress_represents (tape : Fin tapes) (half : ℕ)
    (source : ObliviousPhase.Configuration State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : CompressedTape.Represents source (TapeProgram.project tape simulator))
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    CompressedTape.Represents (source.permute (compressionPermutation half source.head))
      (TapeProgram.project tape (run (compress tape half) simulator)) := by
  rw [compress, TapeProgram.run_project]
  exact CompressedTape.compress_represents half source _ representation headBound

theorem compress_other (tape other : Fin tapes) (different : other ≠ tape) (half : ℕ)
    (simulator : SimulatorConfiguration tapes State Symbol) (address : Address) :
    (run (compress tape half) simulator).memory (other, address) = simulator.memory (other, address) :=
  TapeProgram.run_other tape other different _ simulator address

def compressSaved (tape : Fin tapes) (half : ℕ) (slot : ℤ) :
    List (Instruction (Fin tapes × Address) (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  TapeProgram.lift tape (PhaseStack.compressSaved half slot)

def expand (tape : Fin tapes) (half : ℕ) (slot : ℤ) :
    List (Instruction (Fin tapes × Address) (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  TapeProgram.lift tape (PhaseStack.expand half slot)

theorem compressSaved_length (tape : Fin tapes) (half : ℕ) (slot : ℤ) :
    (compressSaved (State := State) (Symbol := Symbol) tape half slot).length = 112 * half + 9 := by
  rw [compressSaved, TapeProgram.lift_length, PhaseStack.compressSaved_length]

theorem expand_length (tape : Fin tapes) (half : ℕ) (slot : ℤ) :
    (expand (State := State) (Symbol := Symbol) tape half slot).length = 96 * half + 7 := by
  rw [expand, TapeProgram.lift_length, PhaseStack.expand_length]

theorem compressSaved_represents (tape : Fin tapes) (half : ℕ) (slot : ℤ)
    (source : ObliviousPhase.Configuration State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : CompressedTape.Represents source (TapeProgram.project tape simulator))
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    CompressedTape.Represents (source.permute (compressionPermutation half source.head))
      (TapeProgram.project tape (run (compressSaved tape half slot) simulator)) := by
  rw [compressSaved, TapeProgram.run_project]
  exact PhaseStack.compressSaved_represents half slot source _ representation headBound

theorem compressSaved_choice (tape : Fin tapes) (half : ℕ) (slot : ℤ)
    (source : ObliviousPhase.Configuration State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : CompressedTape.Represents source (TapeProgram.project tape simulator))
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    ((run (compressSaved tape half slot) simulator).memory (tape, Sum.inr slot)).2 = decide (source.head < 0) := by
  have h := PhaseStack.compressSaved_choice half slot source (TapeProgram.project tape simulator) representation headBound
  rw [← TapeProgram.run_project] at h
  exact h

theorem expand_represents (tape : Fin tapes) (half : ℕ) (slot originalHead : ℤ)
    (source : ObliviousPhase.Configuration State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : CompressedTape.Represents source (TapeProgram.project tape simulator))
    (choice : (simulator.memory (tape, Sum.inr slot)).2 = decide (originalHead < 0)) :
    CompressedTape.Represents (source.permute (compressionPermutation half originalHead).symm)
      (TapeProgram.project tape (run (expand tape half slot) simulator)) := by
  rw [expand, TapeProgram.run_project]
  exact PhaseStack.expand_represents half slot originalHead source _ representation choice

theorem compressSaved_other (tape other : Fin tapes) (different : other ≠ tape) (half : ℕ) (slot : ℤ)
    (simulator : SimulatorConfiguration tapes State Symbol) (address : Address) :
    (run (compressSaved tape half slot) simulator).memory (other, address) = simulator.memory (other, address) :=
  TapeProgram.run_other tape other different _ simulator address

theorem expand_other (tape other : Fin tapes) (different : other ≠ tape) (half : ℕ) (slot : ℤ)
    (simulator : SimulatorConfiguration tapes State Symbol) (address : Address) :
    (run (expand tape half slot) simulator).memory (other, address) = simulator.memory (other, address) :=
  TapeProgram.run_other tape other different _ simulator address

end MultitapeCompression
