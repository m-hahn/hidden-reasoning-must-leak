import HeadMarker
import PhaseSemantics

/-!
# Fixed-control compression of a marked source tape

The source state remains fixed-size auxiliary control. Tape symbols and the
unique source head marker remain cell memory. The compression choice is
computed by a fixed head-marker scan, then both fixed-address shift scans
execute. Representation preservation is proved from the actual instructions;
no head-coordinate oracle or whole-tape control symbol is used.
-/

noncomputable section

namespace CompressedTape

open ObliviousProgram ObliviousCopy RotationProgram ObliviousPhase

variable {State Symbol : Type*}

abbrev SimulatorConfiguration (State Symbol : Type*) :=
  ObliviousProgram.Configuration Address (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)

def Represents (source : ObliviousPhase.Configuration State Symbol)
    (simulator : SimulatorConfiguration State Symbol) : Prop :=
  simulator.control.auxiliary = source.state ∧
    ∀ position, simulator.memory (Sum.inl position) = (source.tape position, decide (position = source.head))

def compress (half : ℕ) :
    List (Instruction Address (Control State (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)) :=
  HeadMarker.detect (8 * half) ++ RotationProgram.rotate (8 * half) (half : ℤ)

theorem compress_length (half : ℕ) :
    (compress (State := State) (Symbol := Symbol) half).length = 112 * half + 8 := by
  simp only [compress, List.length_append, HeadMarker.detect_length, RotationProgram.rotate_length]
  ring

theorem compress_length_le (half : ℕ) (hhalf : 1 ≤ half) :
    (compress (State := State) (Symbol := Symbol) half).length ≤ 120 * half := by
  rw [compress_length]
  omega

theorem compress_represents (half : ℕ) (source : ObliviousPhase.Configuration State Symbol)
    (simulator : SimulatorConfiguration State Symbol) (representation : Represents source simulator)
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    Represents (source.permute (compressionPermutation half source.head)) (run (compress half) simulator) := by
  have hhead : TapeRotation.inside (8 * half) source.head :=
    TapeRotation.inside_of_abs_le _ _ (by simp only [Nat.cast_mul, Nat.cast_ofNat]; omega)
  have hmarker : ∀ cell, (simulator.memory (Sum.inl cell)).2 = decide (cell = source.head) := by
    intro cell
    rw [representation.2 cell]
  have hdetect := HeadMarker.detect_correct (8 * half) source.head simulator hhead hmarker
  have hshift : (if decide (source.head < 0) then (half : ℤ) else -(half : ℤ)) =
      compressionShift half source.head := by simp [compressionShift]
  unfold compress
  rw [run_append, hdetect]
  constructor
  · rw [(RotationProgram.rotate_control _ _ _).1]
    exact representation.1
  · intro cell
    rw [RotationProgram.rotate_main]
    dsimp only
    rw [hshift, representation.2]
    simp only [Configuration.permute, compressionPermutation]
    congr 1
    simp only [Equiv.symm_apply_eq]

theorem compress_head_bound (half : ℕ) (source : ObliviousPhase.Configuration State Symbol)
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    |(source.permute (compressionPermutation half source.head)).head| ≤ (half : ℤ) :=
  compressed_head_bound half source headBound

end CompressedTape
