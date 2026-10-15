import TapeRotation

/-!
# Local, unit-motion multitape source machines

The number of tapes, state type and cell alphabet are fixed. A transition
sees only the state and the scanned symbol on each tape. It cannot inspect
head addresses or the unscanned tape, and every head moves by at most one.
This is the source interface for the permitted fast-multiplication import
and the remaining efficient multitape compiler.
-/

noncomputable section
namespace MultitapeTuring
open ObliviousPhase

structure Machine (tapes : ℕ) (State Symbol : Type*) where
  initialState : State
  transition : State → (Fin tapes → Symbol) → State × (Fin tapes → Symbol) × (Fin tapes → Direction)

structure Configuration (tapes : ℕ) (State Symbol : Type*) where
  state : State
  head : Fin tapes → ℤ
  tape : Fin tapes → ℤ → Symbol

namespace Configuration
variable {tapes : ℕ} {State Symbol : Type*}

@[ext] theorem ext {first second : Configuration tapes State Symbol}
    (state : first.state = second.state) (head : first.head = second.head)
    (tape : first.tape = second.tape) : first = second := by
  cases first
  cases second
  simp_all

def permute (permutations : Fin tapes → Equiv.Perm ℤ) (configuration : Configuration tapes State Symbol) :
    Configuration tapes State Symbol where
  state := configuration.state
  head tape := permutations tape (configuration.head tape)
  tape tape position := configuration.tape tape ((permutations tape).symm position)

@[simp] theorem permute_inverse (permutations : Fin tapes → Equiv.Perm ℤ)
    (configuration : Configuration tapes State Symbol) :
    permute (fun tape => (permutations tape).symm) (permute permutations configuration) = configuration := by
  apply ext <;> simp [permute]

end Configuration

namespace Machine
variable {tapes : ℕ} {State Symbol : Type*}

def scanned (configuration : Configuration tapes State Symbol) : Fin tapes → Symbol :=
  fun tape => configuration.tape tape (configuration.head tape)

def step (machine : Machine tapes State Symbol) (configuration : Configuration tapes State Symbol) :
    Configuration tapes State Symbol :=
  let action := machine.transition configuration.state (scanned configuration)
  { state := action.1
    head := fun tape => configuration.head tape + (action.2.2 tape).displacement
    tape := fun tape => Function.update (configuration.tape tape) (configuration.head tape) (action.2.1 tape) }

def run (machine : Machine tapes State Symbol) : ℕ → Configuration tapes State Symbol → Configuration tapes State Symbol
  | 0, configuration => configuration
  | time + 1, configuration => machine.step (machine.run time configuration)

theorem run_add (machine : Machine tapes State Symbol) (first last : ℕ)
    (configuration : Configuration tapes State Symbol) :
    machine.run (first + last) configuration = machine.run last (machine.run first configuration) := by
  induction last with
  | zero => simp [run]
  | succ last ih => simp [run, ih]

theorem head_distance_le (machine : Machine tapes State Symbol) (configuration : Configuration tapes State Symbol)
    (time : ℕ) (tape : Fin tapes) :
    |(machine.run time configuration).head tape - configuration.head tape| ≤ (time : ℤ) := by
  induction time with
  | zero => simp [run]
  | succ time ih =>
      let before := machine.run time configuration
      let direction := (machine.transition before.state (scanned before)).2.2 tape
      change |before.head tape + direction.displacement - configuration.head tape| ≤ (time + 1 : ℕ)
      calc
        _ = |(before.head tape - configuration.head tape) + direction.displacement| := by congr 1; ring
        _ ≤ |before.head tape - configuration.head tape| + |direction.displacement| := abs_add _ _
        _ ≤ (time : ℤ) + 1 := add_le_add ih direction.abs_displacement_le_one
        _ = (time + 1 : ℕ) := by simp

@[simp] theorem scanned_permute (configuration : Configuration tapes State Symbol)
    (permutations : Fin tapes → Equiv.Perm ℤ) : scanned (configuration.permute permutations) = scanned configuration := by
  funext tape
  simp [scanned, Configuration.permute]

theorem step_permute (machine : Machine tapes State Symbol) (configuration : Configuration tapes State Symbol)
    (permutations : Fin tapes → Equiv.Perm ℤ)
    (neighbors : ∀ tape, permutations tape
      (configuration.head tape + ((machine.transition configuration.state (scanned configuration)).2.2 tape).displacement) =
      permutations tape (configuration.head tape) +
        ((machine.transition configuration.state (scanned configuration)).2.2 tape).displacement) :
    machine.step (configuration.permute permutations) = (machine.step configuration).permute permutations := by
  apply Configuration.ext
  · change (machine.transition configuration.state (scanned (configuration.permute permutations))).1 =
      (machine.transition configuration.state (scanned configuration)).1
    rw [scanned_permute]
  · funext tape
    change permutations tape (configuration.head tape) +
        ((machine.transition configuration.state (scanned (configuration.permute permutations))).2.2 tape).displacement =
      permutations tape (configuration.head tape +
        ((machine.transition configuration.state (scanned configuration)).2.2 tape).displacement)
    rw [scanned_permute]
    exact (neighbors tape).symm
  · funext tape position
    change Function.update (fun cell => configuration.tape tape ((permutations tape).symm cell))
        (permutations tape (configuration.head tape))
        ((machine.transition configuration.state (scanned (configuration.permute permutations))).2.1 tape) position =
      Function.update (configuration.tape tape) (configuration.head tape)
        ((machine.transition configuration.state (scanned configuration)).2.1 tape) ((permutations tape).symm position)
    rw [scanned_permute]
    by_cases hposition : position = permutations tape (configuration.head tape)
    · subst position
      rw [Equiv.symm_apply_apply]
      simp
    · have hinverse : (permutations tape).symm position ≠ configuration.head tape := by
        intro heq
        apply hposition
        rw [← heq]
        simp
      simp [hposition, hinverse]

theorem run_permute_of_neighbors (machine : Machine tapes State Symbol)
    (configuration : Configuration tapes State Symbol) (permutations : Fin tapes → Equiv.Perm ℤ) (steps : ℕ)
    (neighbors : ∀ time, time < steps → ∀ tape,
      let before := machine.run time configuration
      let direction := (machine.transition before.state (scanned before)).2.2 tape
      permutations tape (before.head tape + direction.displacement) =
        permutations tape (before.head tape) + direction.displacement) :
    machine.run steps (configuration.permute permutations) =
      (machine.run steps configuration).permute permutations := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [run, ih (fun time htime => neighbors time (by omega))]
      exact machine.step_permute (machine.run steps configuration) permutations (neighbors steps (by omega))

/-- Different tapes may use different compression shifts. Their joint
permutation preserves every write and the shared control transition. -/
theorem run_rotate (machine : Machine tapes State Symbol)
    (configuration : Configuration tapes State Symbol) (radius steps : ℕ) (shifts : Fin tapes → ℤ)
    (clearance : ∀ tape, |configuration.head tape| + (steps : ℤ) + |shifts tape| ≤ (radius : ℤ)) :
    machine.run steps (configuration.permute (fun tape => TapeRotation.permutation radius (shifts tape))) =
      (machine.run steps configuration).permute (fun tape => TapeRotation.permutation radius (shifts tape)) := by
  apply machine.run_permute_of_neighbors
  intro time htime tape
  let before := machine.run time configuration
  let direction := (machine.transition before.state (scanned before)).2.2 tape
  have hc := clearance tape
  have hbefore : |before.head tape| ≤ |configuration.head tape| + (time : ℤ) := by
    calc
      _ = |configuration.head tape + (before.head tape - configuration.head tape)| := by congr 1; ring
      _ ≤ |configuration.head tape| + |before.head tape - configuration.head tape| := abs_add _ _
      _ ≤ _ := add_le_add_left (machine.head_distance_le configuration time tape) _
  have hafter : |before.head tape + direction.displacement| ≤ |configuration.head tape| + (steps : ℤ) := by
    have h := abs_add (before.head tape) direction.displacement
    have hd := direction.abs_displacement_le_one
    have ht : (time : ℤ) + 1 ≤ (steps : ℤ) := by omega
    omega
  have hhead := TapeRotation.inside_of_abs_le radius (before.head tape) (by
    have hs := abs_nonneg (shifts tape)
    have ht : (time : ℤ) ≤ (steps : ℤ) := by omega
    omega)
  have hnext := TapeRotation.inside_of_abs_le radius (before.head tape + direction.displacement) (by
    have hs := abs_nonneg (shifts tape)
    omega)
  have hshiftHead := TapeRotation.inside_of_abs_le radius (before.head tape + shifts tape) (by
    have ht : (time : ℤ) ≤ (steps : ℤ) := by omega
    have h := abs_add (before.head tape) (shifts tape)
    omega)
  have hshiftNext := TapeRotation.inside_of_abs_le radius (before.head tape + direction.displacement + shifts tape) (by
    have h := abs_add (before.head tape + direction.displacement) (shifts tape)
    omega)
  change TapeRotation.permutation radius (shifts tape) (before.head tape + direction.displacement) =
    TapeRotation.permutation radius (shifts tape) (before.head tape) + direction.displacement
  rw [TapeRotation.move_eq_translation radius _ _ hnext hshiftNext,
    TapeRotation.move_eq_translation radius _ _ hhead hshiftHead]
  ring

theorem terminal_step_fixed (machine : Machine tapes State Symbol) (configuration : Configuration tapes State Symbol)
    (terminal : ∀ symbols, machine.transition configuration.state symbols =
      (configuration.state, symbols, fun _ => Direction.stay)) : machine.step configuration = configuration := by
  apply Configuration.ext
  · simp [step, terminal]
  · simp [step, terminal, Direction.displacement]
  · funext tape
    simp [step, terminal, scanned, Function.update_eq_self]

theorem terminal_run_fixed (machine : Machine tapes State Symbol) (configuration : Configuration tapes State Symbol)
    (terminal : ∀ symbols, machine.transition configuration.state symbols =
      (configuration.state, symbols, fun _ => Direction.stay)) (steps : ℕ) : machine.run steps configuration = configuration := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [run, ih, terminal_step_fixed machine configuration terminal]

theorem terminal_run_after (machine : Machine tapes State Symbol) (configuration : Configuration tapes State Symbol)
    (finish total : ℕ) (htime : finish ≤ total)
    (terminal : ∀ symbols, machine.transition (machine.run finish configuration).state symbols =
      ((machine.run finish configuration).state, symbols, fun _ => Direction.stay)) :
    machine.run total configuration = machine.run finish configuration := by
  rw [show total = finish + (total - finish) by omega, run_add]
  exact terminal_run_fixed machine _ terminal _

end Machine
end MultitapeTuring
