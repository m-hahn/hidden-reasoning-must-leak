import CompressedTape

/-!
# Saved compression choices in tape memory

Choice bits are stored in buffer cells outside the rotation window. Saving
and loading are fixed-address instructions. Compression computes the bit by
head-marker detection; expansion loads that earlier bit and performs the
inverse permutation, without inspecting the current head position.
-/

noncomputable section

namespace PhaseStack

open ObliviousProgram ObliviousCopy RotationProgram ObliviousPhase CompressedTape

variable {State Symbol : Type*}

def save (slot : ℤ) :
    Instruction Address (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol) :=
  .modify (Sum.inr slot) (fun control cell => (cell.1, control.flag))

def load (slot : ℤ) :
    Instruction Address (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol) :=
  .read (Sum.inr slot) (fun control cell => { control with flag := cell.2 })

theorem save_memory (slot : ℤ) (configuration : SimulatorConfiguration State Symbol) :
    execute (save slot) configuration =
      { configuration with memory := fun address => if address = Sum.inr slot then
        ((configuration.memory address).1, configuration.control.flag) else configuration.memory address } := by
  apply congrArg₂ (@ObliviousProgram.Configuration.mk Address (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol))
  · rfl
  · funext address
    simp only [execute, save, Instruction.address, Instruction.nextSymbol]
    split_ifs with heq
    · rw [heq]
    · rfl

theorem load_memory (slot : ℤ) (configuration : SimulatorConfiguration State Symbol) :
    execute (load slot) configuration =
      { configuration with control := { configuration.control with flag := (configuration.memory (Sum.inr slot)).2 } } := by
  apply congrArg₂ (@ObliviousProgram.Configuration.mk Address (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol))
  · rfl
  · funext address
    simp only [execute, load, Instruction.address, Instruction.nextSymbol]
    split_ifs with heq
    · rw [heq]
    · rfl

theorem save_represents (slot : ℤ) (source : ObliviousPhase.Configuration State Symbol)
    (configuration : SimulatorConfiguration State Symbol) (representation : Represents source configuration) :
    Represents source (execute (save slot) configuration) := by
  rw [save_memory]
  exact ⟨representation.1, fun position => by simpa using representation.2 position⟩

theorem load_represents (slot : ℤ) (source : ObliviousPhase.Configuration State Symbol)
    (configuration : SimulatorConfiguration State Symbol) (representation : Represents source configuration) :
    Represents source (execute (load slot) configuration) := by
  rw [load_memory]
  exact representation

theorem compress_flag (half : ℕ) (source : ObliviousPhase.Configuration State Symbol)
    (configuration : SimulatorConfiguration State Symbol) (representation : Represents source configuration)
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    (run (compress half) configuration).control.flag = decide (source.head < 0) := by
  have hhead : TapeRotation.inside (8 * half) source.head :=
    TapeRotation.inside_of_abs_le _ _ (by simp only [Nat.cast_mul, Nat.cast_ofNat]; omega)
  have hmarker : ∀ cell, (configuration.memory (Sum.inl cell)).2 = decide (cell = source.head) := by
    intro cell
    rw [representation.2 cell]
  unfold compress
  rw [run_append, (rotate_control _ _ _).2,
    HeadMarker.detect_correct (8 * half) source.head configuration hhead hmarker]

def compressSaved (half : ℕ) (slot : ℤ) :
    List (Instruction Address (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  compress half ++ [save slot]

theorem compressSaved_length (half : ℕ) (slot : ℤ) :
    (compressSaved (State := State) (Symbol := Symbol) half slot).length = 112 * half + 9 := by
  simp [compressSaved, compress_length]

theorem compressSaved_represents (half : ℕ) (slot : ℤ) (source : ObliviousPhase.Configuration State Symbol)
    (configuration : SimulatorConfiguration State Symbol) (representation : Represents source configuration)
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    Represents (source.permute (compressionPermutation half source.head))
      (run (compressSaved half slot) configuration) := by
  unfold compressSaved
  rw [run_append, run_cons, run_nil]
  exact save_represents slot _ _ (compress_represents half source configuration representation headBound)

theorem compressSaved_choice (half : ℕ) (slot : ℤ) (source : ObliviousPhase.Configuration State Symbol)
    (configuration : SimulatorConfiguration State Symbol) (representation : Represents source configuration)
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    ((run (compressSaved half slot) configuration).memory (Sum.inr slot)).2 = decide (source.head < 0) := by
  unfold compressSaved
  rw [run_append, run_cons, run_nil, save_memory]
  simp only [ite_true]
  exact compress_flag half source configuration representation headBound

/-- Unrelated saved choices outside a phase's window survive the complete
compression, including the head scan and both buffer-based shift scans. -/
theorem compress_preserves_slot (half : ℕ) (slot : ℤ)
    (configuration : SimulatorConfiguration State Symbol) (outside : ¬ TapeRotation.inside (8 * half) slot) :
    (run (compress half) configuration).memory (Sum.inr slot) = configuration.memory (Sum.inr slot) := by
  unfold compress
  rw [run_append, rotate_buffer_outside _ _ _ slot outside]
  exact congrFun (HeadMarker.detect_preserves _ _).1 (Sum.inr slot)

def expand (half : ℕ) (slot : ℤ) :
    List (Instruction Address (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  load slot :: rotate (8 * half) (-(half : ℤ))

theorem expand_length (half : ℕ) (slot : ℤ) :
    (expand (State := State) (Symbol := Symbol) half slot).length = 96 * half + 7 := by
  simp only [expand, List.length_cons, rotate_length]
  ring

/-- The loaded earlier choice determines the inverse rotation. No clearance
or sign hypothesis on the *current* head is needed to transport its tape. -/
theorem expand_represents (half : ℕ) (slot originalHead : ℤ)
    (source : ObliviousPhase.Configuration State Symbol) (configuration : SimulatorConfiguration State Symbol)
    (representation : Represents source configuration)
    (choice : (configuration.memory (Sum.inr slot)).2 = decide (originalHead < 0)) :
    Represents (source.permute (compressionPermutation half originalHead).symm)
      (run (expand half slot) configuration) := by
  unfold expand
  rw [run_cons, load_memory]
  have hshift : (if decide (originalHead < 0) then -(half : ℤ) else -(-(half : ℤ))) =
      -(compressionShift half originalHead) := by
    by_cases hnegative : originalHead < 0 <;> simp [compressionShift, hnegative]
  constructor
  · rw [(rotate_control _ _ _).1]
    exact representation.1
  · intro cell
    rw [rotate_main]
    dsimp only
    rw [choice, hshift, representation.2]
    simp only [compressionPermutation, TapeRotation.permutation_symm, ObliviousPhase.Configuration.permute]
    congr 1
    rw [← TapeRotation.permutation_symm (8 * half) (-compressionShift half originalHead)]
    simp only [Equiv.symm_apply_eq]

/-- Stack positions are outside every buffer window at or below the fixed
top-level phase. Their integer coordinates are schedule data, not control. -/
def stackSlot (topLevel slot : ℕ) : ℤ := (8 * 2 ^ topLevel : ℕ) + 1 + slot

theorem stackSlot_injective (topLevel : ℕ) : Function.Injective (stackSlot topLevel) := by
  intro first second heq
  unfold stackSlot at heq
  omega

theorem stackSlot_outside (topLevel level slot : ℕ) (hlevel : level ≤ topLevel) :
    ¬ TapeRotation.inside (8 * 2 ^ level) (stackSlot topLevel slot) := by
  have hpow : 2 ^ level ≤ 2 ^ topLevel := Nat.pow_le_pow_right (by decide) hlevel
  unfold TapeRotation.inside stackSlot
  omega

end PhaseStack
