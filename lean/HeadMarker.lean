import RotationProgram

/-!
# Obtaining compression choices from a finite head marker

The simulated head is marked in the cell alphabet. A fixed scan detects
whether that marker lies on the negative side of the window. No integer head
coordinate is stored in the simulator's control and no address depends on the
observed marker. The scan preserves every cell and all auxiliary control.
-/

noncomputable section

namespace HeadMarker

open ObliviousProgram ObliviousCopy RotationProgram ObliviousPhase

variable {Aux Symbol : Type*}

abbrev Cell (Symbol : Type*) := Symbol × Bool

def read (radius : ℕ) (index : Fin (2 * radius + 1)) :
    Instruction Address (Control Aux (Cell Symbol)) (Cell Symbol) :=
  .read (Sum.inl (position radius index)) (fun control cell =>
    { control with flag := control.flag || (decide (position radius index < 0) && cell.2) })

def scan (radius : ℕ) : List (Instruction Address (Control Aux (Cell Symbol)) (Cell Symbol)) :=
  (cells radius).map (read radius)

theorem run_read (radius : ℕ) (index : Fin (2 * radius + 1))
    (configuration : Configuration Address (Control Aux (Cell Symbol)) (Cell Symbol)) :
    execute (read radius index) configuration =
      { configuration with control := { configuration.control with flag := configuration.control.flag ||
        (decide (position radius index < 0) && (configuration.memory (Sum.inl (position radius index))).2) } } := by
  apply congrArg₂ (@Configuration.mk Address (Control Aux (Cell Symbol)) (Cell Symbol))
  · rfl
  · funext address
    simp only [execute, read, Instruction.address, Instruction.nextSymbol]
    split_ifs with heq
    · rw [heq]
    · rfl

theorem run_list (radius : ℕ) (indices : List (Fin (2 * radius + 1)))
    (configuration : Configuration Address (Control Aux (Cell Symbol)) (Cell Symbol)) :
    run (indices.map (read radius)) configuration =
      { configuration with control := { configuration.control with flag := (configuration.control.flag ||
        indices.any (fun i => decide (position radius i < 0) && (configuration.memory (Sum.inl (position radius i))).2)) } } := by
  induction indices generalizing configuration with
  | nil => simp [run]
  | cons index indices ih =>
      rw [List.map_cons, run_cons, run_read, ih]
      simp only [List.any_cons]
      cases configuration.control.flag <;>
        cases decide (position radius index < 0) && (configuration.memory (Sum.inl (position radius index))).2 <;>
        cases indices.any (fun i => decide (position radius i < 0) && (configuration.memory (Sum.inl (position radius i))).2) <;>
        rfl

def detect (radius : ℕ) : List (Instruction Address (Control Aux (Cell Symbol)) (Cell Symbol)) :=
  .local (Sum.inl 0) (fun control => { control with flag := false }) :: scan radius

theorem clear_memory (configuration : Configuration Address (Control Aux (Cell Symbol)) (Cell Symbol)) :
    execute (.local (Sum.inl 0) (fun control => { control with flag := false })) configuration =
      { configuration with control := { configuration.control with flag := false } } := by
  apply congrArg₂ (@Configuration.mk Address (Control Aux (Cell Symbol)) (Cell Symbol))
  · rfl
  · funext address
    simp only [execute, Instruction.address, Instruction.nextSymbol]
    split_ifs with heq
    · rw [heq]
    · rfl

theorem detect_length (radius : ℕ) :
    (detect (Aux := Aux) (Symbol := Symbol) radius).length = 2 * radius + 2 := by
  simp [detect, scan, cells]

/-- A valid unique head marker supplies the actual compression flag. The
entire scan and reset have addresses fixed before seeing the input. -/
theorem detect_correct (radius : ℕ) (head : ℤ)
    (configuration : Configuration Address (Control Aux (Cell Symbol)) (Cell Symbol))
    (hhead : TapeRotation.inside radius head)
    (marker : ∀ cell, (configuration.memory (Sum.inl cell)).2 = decide (cell = head)) :
    run (detect radius) configuration =
      { configuration with control := { configuration.control with flag := decide (head < 0) } } := by
  unfold detect scan
  rw [run_cons, clear_memory, run_list]
  simp only [Bool.false_or]
  have hflag : (cells radius).any
      (fun i => decide (position radius i < 0) && (configuration.memory (Sum.inl (position radius i))).2) =
      decide (head < 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, marker]
    constructor
    · rintro ⟨i, _, hnegative, heq⟩
      simpa [heq] using hnegative
    · intro hnegative
      exact ⟨index radius head hhead, mem_cells _ _, by simpa [position_index] using hnegative,
        position_index radius head hhead⟩
  rw [hflag]

/-- Cell contents and fixed auxiliary source state survive head detection
unchanged. The only change is the Boolean choice flag. -/
theorem detect_preserves (radius : ℕ)
    (configuration : Configuration Address (Control Aux (Cell Symbol)) (Cell Symbol)) :
    (run (detect radius) configuration).memory = configuration.memory ∧
      (run (detect radius) configuration).control.auxiliary = configuration.control.auxiliary := by
  unfold detect scan
  rw [run_cons, clear_memory, run_list]
  exact ⟨rfl, rfl⟩

end HeadMarker
