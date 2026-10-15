import TapeRotation

/-!
# Correctness of recursive oblivious compression phases

The two compression choices depend only on the simulated head sign. Each
choice is a finite-window permutation, and expansion undoes the two choices
in reverse order. This file proves that the complete recursive phase equals
`2^level` source steps, including the complete tape configuration. The
separate fixed-address implementation of each rotation is still needed to
turn the semantic phase into an efficient finite-control program.
-/

noncomputable section

namespace ObliviousPhase

variable {State Symbol : Type*}

def compressionShift (half : ℕ) (head : ℤ) : ℤ :=
  if head < 0 then (half : ℤ) else -(half : ℤ)

theorem abs_compressionShift (half : ℕ) (head : ℤ) :
    |compressionShift half head| = (half : ℤ) := by
  unfold compressionShift
  split_ifs <;> simp

theorem shifted_head_bound (half : ℕ) (head : ℤ) (hhead : |head| ≤ 2 * (half : ℤ)) :
    |head + compressionShift half head| ≤ (half : ℤ) := by
  rw [abs_le] at hhead ⊢
  unfold compressionShift
  split_ifs <;> omega

def compressionPermutation (half : ℕ) (head : ℤ) : Equiv.Perm ℤ :=
  TapeRotation.permutation (8 * half) (compressionShift half head)

theorem compressed_head_bound (half : ℕ) (configuration : Configuration State Symbol)
    (hhead : |configuration.head| ≤ 2 * (half : ℤ)) :
    |(configuration.permute (compressionPermutation half configuration.head)).head| ≤ (half : ℤ) := by
  have hshift := shifted_head_bound half configuration.head hhead
  have hin := TapeRotation.inside_of_abs_le (8 * half) configuration.head (by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    omega)
  have hout := TapeRotation.inside_of_abs_le (8 * half)
    (configuration.head + compressionShift half configuration.head) (by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      omega)
  simpa only [Configuration.permute, compressionPermutation,
    TapeRotation.move_eq_translation (8 * half) _ _ hin hout] using hshift

namespace Machine

variable {State Symbol : Type*}

theorem head_bound_run (machine : Machine State Symbol) (configuration : Configuration State Symbol)
    (steps : ℕ) : |(machine.run steps configuration).head| ≤ |configuration.head| + (steps : ℤ) := by
  calc
    _ = |configuration.head + ((machine.run steps configuration).head - configuration.head)| := by
      congr 1
      ring
    _ ≤ |configuration.head| + |(machine.run steps configuration).head - configuration.head| := abs_add _ _
    _ ≤ _ := add_le_add_left (machine.head_distance_le configuration steps) _

/-- Source semantics of the Pippenger--Fischer recursive phase. No entire
configuration is stored in a finite-control symbol: permutations act on the
tape memory and the two shift choices are explicitly undone. -/
def phaseExecution (machine : Machine State Symbol) :
    ℕ → Configuration State Symbol → Configuration State Symbol
  | 0, configuration => machine.step configuration
  | level + 1, configuration =>
      let firstPermutation := compressionPermutation (2 ^ level) configuration.head
      let first := machine.phaseExecution level (configuration.permute firstPermutation)
      let secondPermutation := compressionPermutation (2 ^ level) first.head
      let second := machine.phaseExecution level (first.permute secondPermutation)
      (second.permute secondPermutation.symm).permute firstPermutation.symm

set_option maxHeartbeats 800000 in
/-- A complete phase preserves the actual state, head, and infinite tape,
and simulates exactly `2^level` source transitions. -/
theorem phaseExecution_correct (machine : Machine State Symbol) (level : ℕ)
    (configuration : Configuration State Symbol) (hhead : |configuration.head| ≤ (2 ^ level : ℕ)) :
    machine.phaseExecution level configuration = machine.run (2 ^ level) configuration := by
  induction level generalizing configuration with
  | zero => simp [phaseExecution, run]
  | succ level ih =>
      let half : ℕ := 2 ^ level
      let firstPermutation := compressionPermutation half configuration.head
      let compressed := configuration.permute firstPermutation
      let first := machine.phaseExecution level compressed
      let secondPermutation := compressionPermutation half first.head
      have hhalf : 0 ≤ (half : ℤ) := Int.natCast_nonneg half
      have hfull : |configuration.head| ≤ 2 * (half : ℤ) := by
        simpa [half, pow_succ, mul_comm] using hhead
      have hcompressed : |compressed.head| ≤ (half : ℤ) := compressed_head_bound half configuration hfull
      have hfirst : first = machine.run half compressed := ih compressed hcompressed
      have hfirstHead : |first.head| ≤ 2 * (half : ℤ) := by
        rw [hfirst]
        have h := machine.head_bound_run compressed half
        omega
      have hsecondHead : |(first.permute secondPermutation).head| ≤ (half : ℤ) :=
        compressed_head_bound half first hfirstHead
      have hsecond := ih (first.permute secondPermutation) hsecondHead
      have hsecondCommute :
          machine.run half (first.permute secondPermutation) =
            (machine.run half first).permute secondPermutation := by
        apply machine.run_rotate first (8 * half) half (compressionShift half first.head)
        rw [abs_compressionShift]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        omega
      have hfirstCommute :
          machine.run (half + half) compressed =
            (machine.run (half + half) configuration).permute firstPermutation := by
        apply machine.run_rotate configuration (8 * half) (half + half)
          (compressionShift half configuration.head)
        rw [abs_compressionShift]
        simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
        omega
      change ((machine.phaseExecution level (first.permute secondPermutation)).permute
        secondPermutation.symm).permute firstPermutation.symm = _
      rw [hsecond, hsecondCommute, Configuration.permute_inverse, hfirst,
        ← machine.run_add, hfirstCommute, Configuration.permute_inverse]
      congr 1
      simp [half, pow_succ]
      ring

end Machine

def horizonLevel (steps : ℕ) : ℕ := Nat.log 2 steps + 1

theorem horizon_covers (steps : ℕ) : steps ≤ 2 ^ horizonLevel steps :=
  (Nat.lt_pow_succ_log_self (by decide) steps).le

theorem horizon_at_most_twice (steps : ℕ) (hsteps : 1 ≤ steps) :
    2 ^ horizonLevel steps ≤ 2 * steps := by
  have h := Nat.pow_log_le_self 2 (by omega : steps ≠ 0)
  unfold horizonLevel
  rw [pow_succ]
  omega

/-- Explicit near-linear bound on the proved cell-linear *phase weights*.
The implementation must still charge each primitive's actual instructions
against these weights before this is a simulation-runtime theorem. -/
theorem horizon_linear_work_bound (steps : ℕ) (hsteps : 1 ≤ steps) :
    totalLinearWork (phase (horizonLevel steps)) ≤ 10 * steps * (Nat.log 2 steps + 1) := by
  rw [totalLinearWork_phase]
  have hpower := horizon_at_most_twice steps hsteps
  have hlevel : 4 * horizonLevel steps + 1 ≤ 5 * (Nat.log 2 steps + 1) := by
    unfold horizonLevel
    omega
  calc
    _ ≤ (5 * (Nat.log 2 steps + 1)) * (2 * steps) := Nat.mul_le_mul hlevel hpower
    _ = _ := by ring

end ObliviousPhase
