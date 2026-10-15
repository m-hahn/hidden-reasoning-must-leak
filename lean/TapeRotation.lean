import ObliviousPhase

/-!
# Finite-window tape rotations

Compression is an actual permutation of a finite tape interval, with the
outside tape unchanged. Its inverse is the opposite rotation. On a source
run that stays away from the wrap boundary it commutes with every transition,
including tape writes. These facts are the semantic core of an oblivious
compression/expansion phase, not a runtime claim for an unexpanded primitive.
-/

noncomputable section

namespace ObliviousPhase

namespace TapeRotation

def inside (radius : ℕ) (position : ℤ) : Prop :=
  -(radius : ℤ) ≤ position ∧ position ≤ radius

instance (radius : ℕ) (position : ℤ) : Decidable (inside radius position) :=
  inferInstanceAs (Decidable (_ ∧ _))

def move (radius : ℕ) (shift position : ℤ) : ℤ :=
  if inside radius position then
    (position + radius + shift) % (2 * (radius : ℤ) + 1) - radius
  else position

theorem move_inside (radius : ℕ) (shift position : ℤ) (hposition : inside radius position) :
    inside radius (move radius shift position) := by
  rw [move, if_pos hposition]
  have hmod : 0 ≤ (position + radius + shift) % (2 * (radius : ℤ) + 1) :=
    Int.emod_nonneg _ (by omega)
  have hlt : (position + radius + shift) % (2 * (radius : ℤ) + 1) < 2 * (radius : ℤ) + 1 :=
    Int.emod_lt_of_pos _ (by omega)
  unfold inside
  omega

theorem move_outside (radius : ℕ) (shift position : ℤ) (hposition : ¬ inside radius position) :
    move radius shift position = position := by simp [move, hposition]

theorem move_inverse (radius : ℕ) (shift position : ℤ) :
    move radius (-shift) (move radius shift position) = position := by
  by_cases hposition : inside radius position
  · have hout := move_inside radius shift position hposition
    rw [move, if_pos hout, move, if_pos hposition]
    have hreduce :
        (((position + radius + shift) % (2 * (radius : ℤ) + 1) - radius) + radius + -shift) %
          (2 * (radius : ℤ) + 1) = (position + radius) % (2 * (radius : ℤ) + 1) := by
      have hcancel :
          ((position + radius + shift) % (2 * (radius : ℤ) + 1) - radius) + radius + -shift =
            (position + radius + shift) % (2 * (radius : ℤ) + 1) - shift := by ring
      rw [hcancel, Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
      congr 1
      ring
    rw [hreduce]
    have hnonneg : 0 ≤ position + radius := by have h := hposition.1; omega
    have hlt : position + radius < 2 * (radius : ℤ) + 1 := by have h := hposition.2; omega
    rw [Int.emod_eq_of_lt hnonneg hlt]
    ring
  · rw [move_outside radius shift position hposition, move_outside radius (-shift) position hposition]

def permutation (radius : ℕ) (shift : ℤ) : Equiv.Perm ℤ where
  toFun := move radius shift
  invFun := move radius (-shift)
  left_inv := move_inverse radius shift
  right_inv := by intro position; simpa using move_inverse radius (-shift) position

theorem permutation_symm (radius : ℕ) (shift : ℤ) :
    (permutation radius shift).symm = permutation radius (-shift) := by
  ext position
  rfl

theorem move_eq_translation (radius : ℕ) (shift position : ℤ)
    (hposition : inside radius position) (hshifted : inside radius (position + shift)) :
    permutation radius shift position = position + shift := by
  change move radius shift position = _
  rw [move, if_pos hposition]
  have hnonneg : 0 ≤ position + radius + shift := by have h := hshifted.1; omega
  have hlt : position + radius + shift < 2 * (radius : ℤ) + 1 := by have h := hshifted.2; omega
  rw [Int.emod_eq_of_lt hnonneg hlt]
  ring

theorem inside_of_abs_le (radius : ℕ) (position : ℤ) (hposition : |position| ≤ (radius : ℤ)) :
    inside radius position := by
  exact abs_le.mp hposition

end TapeRotation

namespace Machine

variable {State Symbol : Type*}

theorem run_permute_of_neighbors (machine : Machine State Symbol)
    (configuration : Configuration State Symbol) (permutation : Equiv.Perm ℤ) (steps : ℕ)
    (neighbors : ∀ time, time < steps →
      let before := machine.run time configuration
      let direction := (machine.transition before.state (before.tape before.head)).2.2
      permutation (before.head + direction.displacement) =
        permutation before.head + direction.displacement) :
    machine.run steps (configuration.permute permutation) =
      (machine.run steps configuration).permute permutation := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [run, ih (fun time htime => neighbors time (by omega))]
      exact machine.step_permute (machine.run steps configuration) permutation
        (neighbors steps (by omega))

/-- A bounded finite-window rotation preserves a whole computation, not just
its output. The clearance hypothesis is a numerical head-distance bound. -/
theorem run_rotate (machine : Machine State Symbol)
    (configuration : Configuration State Symbol) (radius steps : ℕ) (shift : ℤ)
    (clearance : |configuration.head| + (steps : ℤ) + |shift| ≤ (radius : ℤ)) :
    machine.run steps (configuration.permute (TapeRotation.permutation radius shift)) =
      (machine.run steps configuration).permute (TapeRotation.permutation radius shift) := by
  apply machine.run_permute_of_neighbors
  intro time htime
  let before := machine.run time configuration
  let direction := (machine.transition before.state (before.tape before.head)).2.2
  have hbefore : |before.head| ≤ |configuration.head| + (time : ℤ) := by
    calc
      |before.head| = |configuration.head + (before.head - configuration.head)| := by congr 1; ring
      _ ≤ |configuration.head| + |before.head - configuration.head| := abs_add _ _
      _ ≤ _ := add_le_add_left (machine.head_distance_le configuration time) _
  have hafter : |before.head + direction.displacement| ≤ |configuration.head| + (steps : ℤ) := by
    have h := abs_add before.head direction.displacement
    have hd := direction.abs_displacement_le_one
    have ht : (time : ℤ) + 1 ≤ (steps : ℤ) := by omega
    omega
  have hhead := TapeRotation.inside_of_abs_le radius before.head (by
    have hs := abs_nonneg shift
    have ht : (time : ℤ) ≤ (steps : ℤ) := by omega
    omega)
  have hnext := TapeRotation.inside_of_abs_le radius (before.head + direction.displacement) (by
    have hs := abs_nonneg shift
    omega)
  have hshiftHead := TapeRotation.inside_of_abs_le radius (before.head + shift) (by
    have ht : (time : ℤ) ≤ (steps : ℤ) := by omega
    have h := abs_add before.head shift
    omega)
  have hshiftNext := TapeRotation.inside_of_abs_le radius (before.head + direction.displacement + shift) (by
    have h := abs_add (before.head + direction.displacement) shift
    omega)
  change TapeRotation.permutation radius shift (before.head + direction.displacement) =
    TapeRotation.permutation radius shift before.head + direction.displacement
  rw [TapeRotation.move_eq_translation radius shift _ hnext hshiftNext,
    TapeRotation.move_eq_translation radius shift _ hhead hshiftHead]
  ring

end Machine

end ObliviousPhase
