import ObliviousCopy
import TapeRotation

/-!
# Fixed-address implementation of finite tape rotation

A complete scan copies the window into a buffer. Both shift directions then
execute, with fixed addresses in both scans; only their write enables depend
on the finite control flag. The final main tape is the chosen permutation of
the original tape, with every outside cell unchanged. The instruction count
is exactly linear in the window length.
-/

noncomputable section

namespace RotationProgram

open ObliviousProgram ObliviousCopy ObliviousPhase

variable {Aux Symbol : Type*}

abbrev Address := Sum ℤ ℤ

def position (radius : ℕ) (index : Fin (2 * radius + 1)) : ℤ := (index.val : ℤ) - radius

theorem position_injective (radius : ℕ) : Function.Injective (position radius) := by
  intro first second heq
  apply Fin.ext
  unfold position at heq
  omega

theorem position_inside (radius : ℕ) (index : Fin (2 * radius + 1)) :
    TapeRotation.inside radius (position radius index) := by
  have h := index.isLt
  unfold TapeRotation.inside position
  omega

def index (radius : ℕ) (cell : ℤ) (hcell : TapeRotation.inside radius cell) : Fin (2 * radius + 1) :=
  ⟨(cell + radius).toNat, by have h := hcell.1; have h' := hcell.2; omega⟩

theorem position_index (radius : ℕ) (cell : ℤ) (hcell : TapeRotation.inside radius cell) :
    position radius (index radius cell hcell) = cell := by
  unfold position index
  dsimp only
  have h := hcell.1
  omega

def cells (radius : ℕ) : List (Fin (2 * radius + 1)) := List.ofFn id

@[simp] theorem mem_cells (radius : ℕ) (cell : Fin (2 * radius + 1)) : cell ∈ cells radius := by
  classical
  simp only [cells, List.mem_ofFn]
  exact ⟨cell, rfl⟩

def copyBuffer (radius : ℕ) : List (Instruction Address (Control Aux Symbol) Symbol) :=
  scan (fun i => Sum.inl (position radius i)) (fun i => Sum.inr (position radius i))
    (fun _ => true) (cells radius)

def shiftScan (radius : ℕ) (shift : ℤ) (enabled : Bool → Bool) :
    List (Instruction Address (Control Aux Symbol) Symbol) :=
  scan (fun i => Sum.inr ((TapeRotation.permutation radius shift).symm (position radius i)))
    (fun i => Sum.inl (position radius i)) enabled (cells radius)

/-- The instruction sequence, including both address scans, is independent
of the control flag and of the input tape. -/
def rotate (radius : ℕ) (shift : ℤ) : List (Instruction Address (Control Aux Symbol) Symbol) :=
  copyBuffer radius ++ shiftScan radius shift id ++ shiftScan radius (-shift) Bool.not

theorem copyBuffer_length (radius : ℕ) :
    (copyBuffer (Aux := Aux) (Symbol := Symbol) radius).length = 2 * (2 * radius + 1) := by
  rw [copyBuffer, scan_length]
  simp [cells]

theorem shiftScan_length (radius : ℕ) (shift : ℤ) (enabled : Bool → Bool) :
    (shiftScan (Aux := Aux) (Symbol := Symbol) radius shift enabled).length = 2 * (2 * radius + 1) := by
  rw [shiftScan, scan_length]
  simp [cells]

/-- Six fixed-address instructions per cell: one buffer copy and two
conditionally enabled, unconditional-address shift scans. -/
theorem rotate_length (radius : ℕ) (shift : ℤ) :
    (rotate (Aux := Aux) (Symbol := Symbol) radius shift).length = 6 * (2 * radius + 1) := by
  simp only [rotate, List.length_append, copyBuffer_length, shiftScan_length]
  ring

theorem copyBuffer_control (radius : ℕ) (configuration : Configuration Address (Control Aux Symbol) Symbol) :
    (run (copyBuffer radius) configuration).control.auxiliary = configuration.control.auxiliary ∧
      (run (copyBuffer radius) configuration).control.flag = configuration.control.flag := by
  exact scan_control _ _ _ _ _

theorem shiftScan_control (radius : ℕ) (shift : ℤ) (enabled : Bool → Bool)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) :
    (run (shiftScan radius shift enabled) configuration).control.auxiliary = configuration.control.auxiliary ∧
      (run (shiftScan radius shift enabled) configuration).control.flag = configuration.control.flag := by
  exact scan_control _ _ _ _ _

theorem copyBuffer_main (radius : ℕ) (configuration : Configuration Address (Control Aux Symbol) Symbol)
    (cell : ℤ) : (run (copyBuffer radius) configuration).memory (Sum.inl cell) =
      configuration.memory (Sum.inl cell) := by
  exact scan_other _ _ _ _ _ _ (by intros; simp)

theorem copyBuffer_buffer (radius : ℕ) (configuration : Configuration Address (Control Aux Symbol) Symbol)
    (cell : ℤ) (hcell : TapeRotation.inside radius cell) :
    (run (copyBuffer radius) configuration).memory (Sum.inr cell) = configuration.memory (Sum.inl cell) := by
  have h := scan_destination (fun i => Sum.inl (position radius i))
    (fun i => Sum.inr (position radius i)) (fun _ => true) (cells radius)
    (by intro i j heq; exact position_injective radius (Sum.inr.inj heq))
    (by intros; simp) configuration (index radius cell hcell)
  simpa only [copyBuffer, position_index, mem_cells, and_self, if_true] using h

theorem copyBuffer_buffer_outside (radius : ℕ)
    (configuration : Configuration Address (Control Aux Symbol) Symbol)
    (cell : ℤ) (hcell : ¬ TapeRotation.inside radius cell) :
    (run (copyBuffer radius) configuration).memory (Sum.inr cell) =
      configuration.memory (Sum.inr cell) := by
  apply scan_other
  intro i _ heq
  apply hcell
  have hposition : cell = position radius i := Sum.inr.inj heq
  rw [hposition]
  exact position_inside radius i

theorem shiftScan_buffer (radius : ℕ) (shift : ℤ) (enabled : Bool → Bool)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) (cell : ℤ) :
    (run (shiftScan radius shift enabled) configuration).memory (Sum.inr cell) =
      configuration.memory (Sum.inr cell) := by
  exact scan_other _ _ _ _ _ _ (by intros; simp)

theorem shiftScan_inside (radius : ℕ) (shift : ℤ) (enabled : Bool → Bool)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) (cell : ℤ)
    (hcell : TapeRotation.inside radius cell) :
    (run (shiftScan radius shift enabled) configuration).memory (Sum.inl cell) =
      if enabled configuration.control.flag then
        configuration.memory (Sum.inr ((TapeRotation.permutation radius shift).symm cell))
      else configuration.memory (Sum.inl cell) := by
  have h := scan_destination
    (fun i => Sum.inr ((TapeRotation.permutation radius shift).symm (position radius i)))
    (fun i => Sum.inl (position radius i)) enabled (cells radius)
    (by intro i j heq; exact position_injective radius (Sum.inl.inj heq))
    (by intros; simp) configuration (index radius cell hcell)
  simpa only [shiftScan, position_index, mem_cells, and_true] using h

theorem shiftScan_outside (radius : ℕ) (shift : ℤ) (enabled : Bool → Bool)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) (cell : ℤ)
    (hcell : ¬ TapeRotation.inside radius cell) :
    (run (shiftScan radius shift enabled) configuration).memory (Sum.inl cell) =
      configuration.memory (Sum.inl cell) := by
  apply scan_other
  intro i _ heq
  apply hcell
  have hposition : cell = position radius i := Sum.inl.inj heq
  rw [hposition]
  exact position_inside radius i

theorem inverse_inside (radius : ℕ) (shift cell : ℤ) (hcell : TapeRotation.inside radius cell) :
    TapeRotation.inside radius ((TapeRotation.permutation radius shift).symm cell) :=
  TapeRotation.move_inside radius (-shift) cell hcell

theorem rotate_control (radius : ℕ) (shift : ℤ)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) :
    (run (rotate radius shift) configuration).control.auxiliary = configuration.control.auxiliary ∧
      (run (rotate radius shift) configuration).control.flag = configuration.control.flag := by
  unfold rotate
  rw [run_append, run_append]
  constructor
  · rw [(shiftScan_control _ _ _ _).1, (shiftScan_control _ _ _ _).1, (copyBuffer_control _ _).1]
  · rw [(shiftScan_control _ _ _ _).2, (shiftScan_control _ _ _ _).2, (copyBuffer_control _ _).2]

/-- Flag-stack cells can live beyond the largest buffer window. They are
preserved by every nested rotation, including both conditional scans. -/
theorem rotate_buffer_outside (radius : ℕ) (shift : ℤ)
    (configuration : Configuration Address (Control Aux Symbol) Symbol)
    (cell : ℤ) (hcell : ¬ TapeRotation.inside radius cell) :
    (run (rotate radius shift) configuration).memory (Sum.inr cell) =
      configuration.memory (Sum.inr cell) := by
  unfold rotate
  rw [run_append, run_append, shiftScan_buffer, shiftScan_buffer,
    copyBuffer_buffer_outside _ _ cell hcell]

/-- Exact full main-tape rotation. The symbol type and auxiliary finite
control type are independent of the window radius and the execution length. -/
theorem rotate_main (radius : ℕ) (shift : ℤ)
    (configuration : Configuration Address (Control Aux Symbol) Symbol) (cell : ℤ) :
    (run (rotate radius shift) configuration).memory (Sum.inl cell) =
      configuration.memory (Sum.inl ((TapeRotation.permutation radius
        (if configuration.control.flag then shift else -shift)).symm cell)) := by
  unfold rotate
  rw [run_append, run_append]
  by_cases hcell : TapeRotation.inside radius cell
  · rw [shiftScan_inside _ _ _ _ cell hcell, (shiftScan_control _ _ _ _).2,
      (copyBuffer_control _ _).2]
    cases hflag : configuration.control.flag
    · simp only [Bool.not_false, if_true, hflag, Bool.false_eq_true, if_false]
      rw [shiftScan_buffer, copyBuffer_buffer _ _ _ (inverse_inside radius (-shift) cell hcell)]
    · simp only [Bool.not_true, if_false, hflag, if_true]
      rw [shiftScan_inside _ _ _ _ cell hcell, (copyBuffer_control _ _).2]
      simp only [hflag, id_eq, if_true]
      exact copyBuffer_buffer radius configuration _ (inverse_inside radius shift cell hcell)
  · rw [shiftScan_outside _ _ _ _ cell hcell, shiftScan_outside _ _ _ _ cell hcell, copyBuffer_main]
    change configuration.memory (Sum.inl cell) =
      configuration.memory (Sum.inl (TapeRotation.move radius _ cell))
    rw [TapeRotation.move_outside radius _ cell hcell]

end RotationProgram
