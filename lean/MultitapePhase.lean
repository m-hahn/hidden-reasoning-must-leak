import MultitapeTuring
import PhaseSemantics

/-!
# Recursive compression semantics for genuine multitape machines

Each tape has its own compression choice. Joint finite-window rotations
commute with the shared finite-control source transition under the proved
unit-motion bounds. This is full configuration semantics; instruction
expansion and its runtime are separate obligations.
-/

noncomputable section
namespace MultitapeTuring
open ObliviousPhase
variable {tapes : ℕ} {State Symbol : Type*}

def compressionPermutations (half : ℕ) (heads : Fin tapes → ℤ) : Fin tapes → Equiv.Perm ℤ :=
  fun tape => compressionPermutation half (heads tape)

theorem compressed_head_bound (half : ℕ) (configuration : MultitapeTuring.Configuration tapes State Symbol)
    (hheads : ∀ tape, |configuration.head tape| ≤ 2 * (half : ℤ)) :
    ∀ tape, |(configuration.permute (compressionPermutations half configuration.head)).head tape| ≤ (half : ℤ) := by
  intro tape
  have hshift := shifted_head_bound half (configuration.head tape) (hheads tape)
  have hin := TapeRotation.inside_of_abs_le (8 * half) (configuration.head tape) (by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    have h := hheads tape
    omega)
  have hout := TapeRotation.inside_of_abs_le (8 * half)
    (configuration.head tape + compressionShift half (configuration.head tape)) (by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      omega)
  simpa only [Configuration.permute, compressionPermutations, compressionPermutation,
    TapeRotation.move_eq_translation (8 * half) _ _ hin hout] using hshift

namespace Machine

theorem head_bound_run (machine : MultitapeTuring.Machine tapes State Symbol)
    (configuration : MultitapeTuring.Configuration tapes State Symbol) (steps : ℕ) (tape : Fin tapes) :
    |(machine.run steps configuration).head tape| ≤ |configuration.head tape| + (steps : ℤ) := by
  calc
    _ = |configuration.head tape + ((machine.run steps configuration).head tape - configuration.head tape)| := by
      congr 1
      ring
    _ ≤ |configuration.head tape| + |(machine.run steps configuration).head tape - configuration.head tape| := abs_add _ _
    _ ≤ _ := add_le_add_left (machine.head_distance_le configuration steps tape) _

def phaseExecution (machine : MultitapeTuring.Machine tapes State Symbol) :
    ℕ → MultitapeTuring.Configuration tapes State Symbol → MultitapeTuring.Configuration tapes State Symbol
  | 0, configuration => machine.step configuration
  | level + 1, configuration =>
      let firstPermutations := compressionPermutations (2 ^ level) configuration.head
      let first := machine.phaseExecution level (configuration.permute firstPermutations)
      let secondPermutations := compressionPermutations (2 ^ level) first.head
      let second := machine.phaseExecution level (first.permute secondPermutations)
      (second.permute (fun tape => (secondPermutations tape).symm)).permute
        (fun tape => (firstPermutations tape).symm)

set_option maxHeartbeats 800000 in
theorem phaseExecution_correct (machine : MultitapeTuring.Machine tapes State Symbol) (level : ℕ)
    (configuration : MultitapeTuring.Configuration tapes State Symbol)
    (hheads : ∀ tape, |configuration.head tape| ≤ (2 ^ level : ℕ)) :
    machine.phaseExecution level configuration = machine.run (2 ^ level) configuration := by
  induction level generalizing configuration with
  | zero => simp [phaseExecution, run]
  | succ level ih =>
      let half : ℕ := 2 ^ level
      let firstPermutations := compressionPermutations half configuration.head
      let compressed := configuration.permute firstPermutations
      let first := machine.phaseExecution level compressed
      let secondPermutations := compressionPermutations half first.head
      have hhalf : 0 ≤ (half : ℤ) := Int.natCast_nonneg half
      have hfull : ∀ tape, |configuration.head tape| ≤ 2 * (half : ℤ) := by
        intro tape
        simpa [half, pow_succ, mul_comm] using hheads tape
      have hcompressed : ∀ tape, |compressed.head tape| ≤ (half : ℤ) := compressed_head_bound half configuration hfull
      have hfirst : first = machine.run half compressed := ih compressed hcompressed
      have hfirstHeads : ∀ tape, |first.head tape| ≤ 2 * (half : ℤ) := by
        intro tape
        rw [hfirst]
        have h := machine.head_bound_run compressed half tape
        have hb := hcompressed tape
        omega
      have hsecondHeads : ∀ tape, |(first.permute secondPermutations).head tape| ≤ (half : ℤ) :=
        compressed_head_bound half first hfirstHeads
      have hsecond := ih (first.permute secondPermutations) hsecondHeads
      have hsecondCommute :
          machine.run half (first.permute secondPermutations) =
            (machine.run half first).permute secondPermutations := by
        apply machine.run_rotate first (8 * half) half (fun tape => compressionShift half (first.head tape))
        intro tape
        rw [abs_compressionShift]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        have hh := hfirstHeads tape
        omega
      have hfirstCommute :
          machine.run (half + half) compressed =
            (machine.run (half + half) configuration).permute firstPermutations := by
        apply machine.run_rotate configuration (8 * half) (half + half)
          (fun tape => compressionShift half (configuration.head tape))
        intro tape
        rw [abs_compressionShift]
        simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
        have hh := hfull tape
        omega
      change ((machine.phaseExecution level (first.permute secondPermutations)).permute
        (fun tape => (secondPermutations tape).symm)).permute (fun tape => (firstPermutations tape).symm) = _
      rw [hsecond, hsecondCommute, Configuration.permute_inverse, hfirst,
        ← machine.run_add, hfirstCommute, Configuration.permute_inverse]
      congr 1
      simp [half, pow_succ]
      ring

end Machine
end MultitapeTuring
