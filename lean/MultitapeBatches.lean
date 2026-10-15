import MultitapeLeaf
import MultitapePhase
import TapeProgram

/-!
# Expanded multitape compression batches

Every tape executes the previously proved marker/rotation/stack instruction
lists at fixed addresses. A prefix processes each tape exactly once. The
proof transports the whole source configuration, and checks that saved
choices remain on their own tapes for inverse expansion.
-/

noncomputable section
namespace MultitapeBatches
open ObliviousProgram ObliviousCopy ObliviousPhase RotationProgram MultitapeLeaf

variable {tapes : ℕ} {State Symbol : Type*}

def onePermutation (tape : Fin tapes) (permutation : Equiv.Perm ℤ) : Fin tapes → Equiv.Perm ℤ :=
  fun other => if other = tape then permutation else Equiv.refl ℤ

def partialSource (permutations : Fin tapes → Equiv.Perm ℤ) (count : ℕ)
    (source : MultitapeTuring.Configuration tapes State Symbol) : MultitapeTuring.Configuration tapes State Symbol :=
  source.permute (fun tape => if tape.val < count then permutations tape else Equiv.refl ℤ)

@[simp] theorem partialSource_zero (permutations : Fin tapes → Equiv.Perm ℤ)
    (source : MultitapeTuring.Configuration tapes State Symbol) : partialSource permutations 0 source = source := by
  apply MultitapeTuring.Configuration.ext <;> simp [partialSource, MultitapeTuring.Configuration.permute]

@[simp] theorem partialSource_full (permutations : Fin tapes → Equiv.Perm ℤ)
    (source : MultitapeTuring.Configuration tapes State Symbol) :
    partialSource permutations tapes source = source.permute permutations := by
  apply MultitapeTuring.Configuration.ext <;> simp [partialSource, MultitapeTuring.Configuration.permute]

theorem partialSource_unvisited_head (permutations : Fin tapes → Equiv.Perm ℤ)
    (count : ℕ) (source : MultitapeTuring.Configuration tapes State Symbol)
    (tape : Fin tapes) (unvisited : count ≤ tape.val) :
    (partialSource permutations count source).head tape = source.head tape := by
  simp [partialSource, MultitapeTuring.Configuration.permute, show ¬tape.val < count by omega]

theorem partialSource_next (permutations : Fin tapes → Equiv.Perm ℤ) (count : ℕ) (hcount : count < tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol) :
    partialSource permutations (count + 1) source =
      (partialSource permutations count source).permute (onePermutation ⟨count, hcount⟩ (permutations ⟨count, hcount⟩)) := by
  apply MultitapeTuring.Configuration.ext
  · rfl
  · funext tape
    by_cases heq : tape = ⟨count, hcount⟩
    · subst tape
      simp [partialSource, onePermutation, MultitapeTuring.Configuration.permute]
    · have hval : tape.val ≠ count := by intro h; apply heq; exact Fin.ext h
      have hiff : tape.val < count + 1 ↔ tape.val < count := by omega
      simp [partialSource, onePermutation, MultitapeTuring.Configuration.permute, heq, hiff]
  · funext tape cell
    by_cases heq : tape = ⟨count, hcount⟩
    · subst tape
      simp [partialSource, onePermutation, MultitapeTuring.Configuration.permute]
    · have hval : tape.val ≠ count := by intro h; apply heq; exact Fin.ext h
      have hiff : tape.val < count + 1 ↔ tape.val < count := by omega
      simp [partialSource, onePermutation, MultitapeTuring.Configuration.permute, heq, hiff]

def prefixPrograms (operation : Fin tapes → List (StepInstruction tapes State Symbol)) :
    (count : ℕ) → count ≤ tapes → List (StepInstruction tapes State Symbol)
  | 0, _ => []
  | count + 1, bounded => prefixPrograms operation count (by omega) ++ operation ⟨count, by omega⟩

theorem prefixPrograms_other (operation : Fin tapes → List (StepInstruction tapes State Symbol))
    (count : ℕ) (bounded : count ≤ tapes)
    (other : ∀ selected other, selected ≠ other → ∀ simulator address,
      (run (operation selected) simulator).memory (other, address) = simulator.memory (other, address))
    (tape : Fin tapes) (unvisited : count ≤ tape.val)
    (simulator : SimulatorConfiguration tapes State Symbol) (address : Address) :
    (run (prefixPrograms operation count bounded) simulator).memory (tape, address) = simulator.memory (tape, address) := by
  induction count generalizing simulator with
  | zero => rfl
  | succ count ih =>
      rw [prefixPrograms, run_append, other _ tape (by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega)]
      exact ih (by omega) (by omega) simulator

theorem prefixPrograms_cell (operation : Fin tapes → List (StepInstruction tapes State Symbol))
    (count : ℕ) (bounded : count ≤ tapes) (address : Fin tapes × Address)
    (preserves : ∀ tape simulator, (run (operation tape) simulator).memory address = simulator.memory address)
    (simulator : SimulatorConfiguration tapes State Symbol) :
    (run (prefixPrograms operation count bounded) simulator).memory address = simulator.memory address := by
  induction count generalizing simulator with
  | zero => rfl
  | succ count ih => rw [prefixPrograms, run_append, preserves]; exact ih (by omega) simulator

def sourceView (source : MultitapeTuring.Configuration tapes State Symbol)
    (simulator : SimulatorConfiguration tapes State Symbol) (tape : Fin tapes) :
    ObliviousPhase.Configuration (Registers tapes State Symbol) Symbol :=
  ⟨simulator.control.auxiliary, source.head tape, source.tape tape⟩

theorem sourceView_represents (source : MultitapeTuring.Configuration tapes State Symbol)
    (simulator : SimulatorConfiguration tapes State Symbol) (representation : Represents source simulator) (tape : Fin tapes) :
    CompressedTape.Represents (sourceView source simulator tape) (TapeProgram.project tape simulator) :=
  ⟨rfl, representation.2 tape⟩

theorem compression_one (half : ℕ) (slot : ℤ) (tape : Fin tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator) (headBound : |source.head tape| ≤ 2 * (half : ℤ)) :
    Represents (source.permute (onePermutation tape (compressionPermutation half (source.head tape))))
      (run (MultitapeCompression.compressSaved tape half slot) simulator) := by
  have h := MultitapeCompression.compressSaved_represents tape half slot (sourceView source simulator tape)
    simulator (sourceView_represents source simulator representation tape) headBound
  constructor
  · exact (congrArg Registers.state h.1).trans representation.1
  · intro other cell
    by_cases heq : other = tape
    · subst other
      simpa [sourceView, onePermutation, MultitapeTuring.Configuration.permute, ObliviousPhase.Configuration.permute]
        using h.2 cell
    · rw [MultitapeCompression.compressSaved_other tape other heq]
      simpa [onePermutation, MultitapeTuring.Configuration.permute, heq] using representation.2 other cell

theorem compression_one_choice (half : ℕ) (slot : ℤ) (tape : Fin tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator) (headBound : |source.head tape| ≤ 2 * (half : ℤ)) :
    ((run (MultitapeCompression.compressSaved tape half slot) simulator).memory (tape, Sum.inr slot)).2 =
      decide (source.head tape < 0) :=
  MultitapeCompression.compressSaved_choice tape half slot (sourceView source simulator tape)
    simulator (sourceView_represents source simulator representation tape) headBound

theorem expansion_one (half : ℕ) (slot originalHead : ℤ) (tape : Fin tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator)
    (choice : (simulator.memory (tape, Sum.inr slot)).2 = decide (originalHead < 0)) :
    Represents (source.permute (onePermutation tape (compressionPermutation half originalHead).symm))
      (run (MultitapeCompression.expand tape half slot) simulator) := by
  have h := MultitapeCompression.expand_represents tape half slot originalHead (sourceView source simulator tape)
    simulator (sourceView_represents source simulator representation tape) choice
  constructor
  · exact (congrArg Registers.state h.1).trans representation.1
  · intro other cell
    by_cases heq : other = tape
    · subst other
      simpa [sourceView, onePermutation, MultitapeTuring.Configuration.permute, ObliviousPhase.Configuration.permute]
        using h.2 cell
    · rw [MultitapeCompression.expand_other tape other heq]
      simpa [onePermutation, MultitapeTuring.Configuration.permute, heq] using representation.2 other cell

def compressPrefix (half : ℕ) (slot : ℤ) (count : ℕ) (bounded : count ≤ tapes) :
    List (StepInstruction tapes State Symbol) := prefixPrograms (fun tape => MultitapeCompression.compressSaved tape half slot) count bounded

def expandPrefix (half : ℕ) (slot : ℤ) (count : ℕ) (bounded : count ≤ tapes) :
    List (StepInstruction tapes State Symbol) := prefixPrograms (fun tape => MultitapeCompression.expand tape half slot) count bounded

theorem compressPrefix_represents (half : ℕ) (slot : ℤ) (count : ℕ) (bounded : count ≤ tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator) (headBounds : ∀ tape, |source.head tape| ≤ 2 * (half : ℤ)) :
    Represents (partialSource (MultitapeTuring.compressionPermutations half source.head) count source)
      (run (compressPrefix half slot count bounded) simulator) := by
  induction count with
  | zero => simpa [compressPrefix, prefixPrograms] using representation
  | succ count ih =>
      have hi := ih (by omega)
      have hhead := partialSource_unvisited_head (MultitapeTuring.compressionPermutations half source.head)
        count source ⟨count, by omega⟩ le_rfl
      rw [partialSource_next _ count (by omega), compressPrefix, prefixPrograms, run_append]
      rw [show (MultitapeTuring.compressionPermutations half source.head) ⟨count, by omega⟩ =
        compressionPermutation half ((partialSource (MultitapeTuring.compressionPermutations half source.head) count source).head ⟨count, by omega⟩) by rw [hhead]; rfl]
      exact compression_one half slot _ _ _ hi (by rw [hhead]; exact headBounds _)

theorem expandPrefix_represents (half : ℕ) (slot : ℤ) (heads : Fin tapes → ℤ) (count : ℕ) (bounded : count ≤ tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator)
    (choices : ∀ tape, (simulator.memory (tape, Sum.inr slot)).2 = decide (heads tape < 0)) :
    Represents (partialSource (fun tape => (compressionPermutation half (heads tape)).symm) count source)
      (run (expandPrefix half slot count bounded) simulator) := by
  induction count with
  | zero => simpa [expandPrefix, prefixPrograms] using representation
  | succ count ih =>
      rw [partialSource_next _ count (by omega), expandPrefix, prefixPrograms, run_append]
      apply expansion_one half slot (heads ⟨count, by omega⟩) _ _ _ (ih (by omega))
      have hmemory := prefixPrograms_other (fun tape => MultitapeCompression.expand tape half slot) count (by omega)
        (fun selected other hne simulator address => MultitapeCompression.expand_other selected other hne.symm half slot simulator address)
        ⟨count, by omega⟩ le_rfl simulator (Sum.inr slot)
      exact (congrArg Prod.snd hmemory).trans (choices _)

theorem compressPrefix_choice (half : ℕ) (slot : ℤ) (count : ℕ) (bounded : count ≤ tapes)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator) (headBounds : ∀ tape, |source.head tape| ≤ 2 * (half : ℤ))
    (tape : Fin tapes) (processed : tape.val < count) :
    ((run (compressPrefix half slot count bounded) simulator).memory (tape, Sum.inr slot)).2 = decide (source.head tape < 0) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [compressPrefix, prefixPrograms, run_append]
      by_cases heq : tape = ⟨count, by omega⟩
      · rw [heq]
        have hhead := partialSource_unvisited_head (MultitapeTuring.compressionPermutations half source.head)
          count source ⟨count, by omega⟩ le_rfl
        have h := compression_one_choice half slot ⟨count, by omega⟩
          (partialSource (MultitapeTuring.compressionPermutations half source.head) count source)
          (run (compressPrefix half slot count (by omega)) simulator)
          (compressPrefix_represents half slot count (by omega) source simulator representation headBounds)
          (by rw [hhead]; exact headBounds _)
        simpa only [hhead] using h
      · rw [MultitapeCompression.compressSaved_other _ tape heq]
        have hval : tape.val ≠ count := by intro h; apply heq; exact Fin.ext h
        exact ih (by omega) (by omega)

def compressAll (half : ℕ) (slot : ℤ) : List (StepInstruction tapes State Symbol) := compressPrefix half slot tapes le_rfl
def expandAll (half : ℕ) (slot : ℤ) : List (StepInstruction tapes State Symbol) := expandPrefix half slot tapes le_rfl

theorem compression_correct (half : ℕ) (slot : ℤ)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator) (headBounds : ∀ tape, |source.head tape| ≤ 2 * (half : ℤ)) :
    Represents (source.permute (MultitapeTuring.compressionPermutations half source.head))
      (run (compressAll half slot) simulator) := by
  simpa only [partialSource_full] using compressPrefix_represents half slot tapes le_rfl source simulator representation headBounds

theorem compression_choices (half : ℕ) (slot : ℤ)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator) (headBounds : ∀ tape, |source.head tape| ≤ 2 * (half : ℤ)) :
    ∀ tape, ((run (compressAll half slot) simulator).memory (tape, Sum.inr slot)).2 = decide (source.head tape < 0) :=
  fun tape => compressPrefix_choice half slot tapes le_rfl source simulator representation headBounds tape tape.isLt

theorem expansion_correct (half : ℕ) (slot : ℤ) (heads : Fin tapes → ℤ)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator)
    (choices : ∀ tape, (simulator.memory (tape, Sum.inr slot)).2 = decide (heads tape < 0)) :
    Represents (source.permute (fun tape => (MultitapeTuring.compressionPermutations half heads tape).symm))
      (run (expandAll half slot) simulator) := by
  simpa only [partialSource_full] using expandPrefix_represents half slot heads tapes le_rfl source simulator representation choices

theorem compression_one_preserves_slot (half : ℕ) (saved other : ℤ) (selected tape : Fin tapes)
    (simulator : SimulatorConfiguration tapes State Symbol)
    (outside : ¬ TapeRotation.inside (8 * half) other) (different : other ≠ saved) :
    (run (MultitapeCompression.compressSaved selected half saved) simulator).memory (tape, Sum.inr other) =
      simulator.memory (tape, Sum.inr other) := by
  by_cases heq : tape = selected
  · subst selected
    have hproject := TapeProgram.run_project tape (PhaseStack.compressSaved half saved) simulator
    have hlocal : (run (PhaseStack.compressSaved half saved) (TapeProgram.project tape simulator)).memory (Sum.inr other) =
        (TapeProgram.project tape simulator).memory (Sum.inr other) := by
      unfold PhaseStack.compressSaved
      rw [run_append, run_cons, run_nil, PhaseStack.save_memory]
      simp only [Sum.inr.injEq, different, if_false]
      exact PhaseStack.compress_preserves_slot half other _ outside
    exact (congrArg (fun configuration => configuration.memory (Sum.inr other)) hproject).trans hlocal
  · exact MultitapeCompression.compressSaved_other selected tape heq half saved simulator _

theorem expansion_one_preserves_slot (half : ℕ) (saved other : ℤ) (selected tape : Fin tapes)
    (simulator : SimulatorConfiguration tapes State Symbol) (outside : ¬ TapeRotation.inside (8 * half) other) :
    (run (MultitapeCompression.expand selected half saved) simulator).memory (tape, Sum.inr other) =
      simulator.memory (tape, Sum.inr other) := by
  by_cases heq : tape = selected
  · subst selected
    have hproject := TapeProgram.run_project tape (PhaseStack.expand half saved) simulator
    have hlocal : (run (PhaseStack.expand half saved) (TapeProgram.project tape simulator)).memory (Sum.inr other) =
        (TapeProgram.project tape simulator).memory (Sum.inr other) := by
      unfold PhaseStack.expand
      rw [run_cons, PhaseStack.load_memory, rotate_buffer_outside _ _ _ other outside]
    exact (congrArg (fun configuration => configuration.memory (Sum.inr other)) hproject).trans hlocal
  · exact MultitapeCompression.expand_other selected tape heq half saved simulator _

theorem compression_preserves_slot (half : ℕ) (saved other : ℤ) (tape : Fin tapes)
    (simulator : SimulatorConfiguration tapes State Symbol)
    (outside : ¬ TapeRotation.inside (8 * half) other) (different : other ≠ saved) :
    (run (compressAll half saved) simulator).memory (tape, Sum.inr other) = simulator.memory (tape, Sum.inr other) :=
  prefixPrograms_cell _ tapes le_rfl _
    (fun selected simulator => compression_one_preserves_slot half saved other selected tape simulator outside different) simulator

theorem expansion_preserves_slot (half : ℕ) (saved other : ℤ) (tape : Fin tapes)
    (simulator : SimulatorConfiguration tapes State Symbol) (outside : ¬ TapeRotation.inside (8 * half) other) :
    (run (expandAll half saved) simulator).memory (tape, Sum.inr other) = simulator.memory (tape, Sum.inr other) :=
  prefixPrograms_cell _ tapes le_rfl _
    (fun selected simulator => expansion_one_preserves_slot half saved other selected tape simulator outside) simulator

theorem prefixPrograms_length (operation : Fin tapes → List (StepInstruction tapes State Symbol))
    (size : ℕ) (sizes : ∀ tape, (operation tape).length = size) (count : ℕ) (bounded : count ≤ tapes) :
    (prefixPrograms operation count bounded).length = count * size := by
  induction count with
  | zero => simp [prefixPrograms]
  | succ count ih => rw [prefixPrograms, List.length_append, sizes, ih]; ring

theorem compressAll_length (half : ℕ) (slot : ℤ) :
    (compressAll (tapes := tapes) (State := State) (Symbol := Symbol) half slot).length = tapes * (112 * half + 9) :=
  prefixPrograms_length _ _ (fun tape => MultitapeCompression.compressSaved_length tape half slot) _ _

theorem expandAll_length (half : ℕ) (slot : ℤ) :
    (expandAll (tapes := tapes) (State := State) (Symbol := Symbol) half slot).length = tapes * (96 * half + 7) :=
  prefixPrograms_length _ _ (fun tape => MultitapeCompression.expand_length tape half slot) _ _

end MultitapeBatches
