import ObliviousProgram
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Log

/-!
# Oblivious phase construction: source semantics and phase accounting

The source has a fixed finite state/alphabet and moves its head by at most
one cell. Tape contents are memory, never part of finite control. The phase
plan follows the recursive compress/simulate/expand construction of Pippenger
and Fischer (1979, Section 3). This file proves the local conjugacy and exact
phase-work identities used in the construction. Expansion of the tape
rotations into fixed finite-control read/write programs is still required
before these work counts become the complete simulation runtime theorem.
-/

noncomputable section

namespace ObliviousPhase

inductive Direction
  | left | stay | right
  deriving DecidableEq, Fintype, Repr

def Direction.displacement : Direction → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

theorem Direction.abs_displacement_le_one (direction : Direction) :
    |direction.displacement| ≤ 1 := by
  cases direction <;> norm_num [Direction.displacement]

structure Machine (State Symbol : Type*) where
  initialState : State
  transition : State → Symbol → State × Symbol × Direction

structure Configuration (State Symbol : Type*) where
  state : State
  head : ℤ
  tape : ℤ → Symbol

namespace Configuration

variable {State Symbol : Type*}

@[ext] theorem ext {first second : Configuration State Symbol}
    (state : first.state = second.state) (head : first.head = second.head)
    (tape : first.tape = second.tape) : first = second := by
  cases first
  cases second
  simp_all

/-- Rename physical tape cells by a permutation. -/
def permute (permutation : Equiv.Perm ℤ) (configuration : Configuration State Symbol) :
    Configuration State Symbol where
  state := configuration.state
  head := permutation configuration.head
  tape := fun position => configuration.tape (permutation.symm position)

@[simp] theorem permute_inverse (permutation : Equiv.Perm ℤ)
    (configuration : Configuration State Symbol) :
    permute permutation.symm (permute permutation configuration) = configuration := by
  apply ext <;> simp [permute]

end Configuration

namespace Machine

variable {State Symbol : Type*}

def step (machine : Machine State Symbol) (configuration : Configuration State Symbol) :
    Configuration State Symbol :=
  let action := machine.transition configuration.state (configuration.tape configuration.head)
  { state := action.1
    head := configuration.head + action.2.2.displacement
    tape := Function.update configuration.tape configuration.head action.2.1 }

def run (machine : Machine State Symbol) : ℕ → Configuration State Symbol → Configuration State Symbol
  | 0, configuration => configuration
  | time + 1, configuration => machine.step (machine.run time configuration)

theorem run_add (machine : Machine State Symbol) (first last : ℕ)
    (configuration : Configuration State Symbol) :
    machine.run (first + last) configuration = machine.run last (machine.run first configuration) := by
  induction last with
  | zero => simp [run]
  | succ last ih => simp [run, ih]

/-- The head cannot travel more than one cell per source step. -/
theorem head_distance_le (machine : Machine State Symbol) (configuration : Configuration State Symbol)
    (time : ℕ) : |(machine.run time configuration).head - configuration.head| ≤ (time : ℤ) := by
  induction time with
  | zero => simp [run]
  | succ time ih =>
      let before := machine.run time configuration
      let direction := (machine.transition before.state (before.tape before.head)).2.2
      change |before.head + direction.displacement - configuration.head| ≤ (time + 1 : ℕ)
      calc
        |before.head + direction.displacement - configuration.head| =
            |(before.head - configuration.head) + direction.displacement| := by congr 1; ring
        _ ≤ |before.head - configuration.head| + |direction.displacement| := abs_add _ _
        _ ≤ (time : ℤ) + 1 := add_le_add ih direction.abs_displacement_le_one
        _ = (time + 1 : ℕ) := by simp

/-- A cell renaming commutes with one source step when it preserves that
step's local neighboring-head movement. All writes are transported exactly. -/
theorem step_permute (machine : Machine State Symbol) (configuration : Configuration State Symbol)
    (permutation : Equiv.Perm ℤ)
    (neighbor : permutation
      (configuration.head + (machine.transition configuration.state
        (configuration.tape configuration.head)).2.2.displacement) =
      permutation configuration.head + (machine.transition configuration.state
        (configuration.tape configuration.head)).2.2.displacement) :
    machine.step (configuration.permute permutation) = (machine.step configuration).permute permutation := by
  apply Configuration.ext
  · simp [step, Configuration.permute]
  · simpa [step, Configuration.permute] using neighbor.symm
  · funext position
    simp only [step, Configuration.permute, Equiv.symm_apply_apply]
    by_cases hposition : position = permutation configuration.head
    · subst position
      rw [Equiv.symm_apply_apply]
      simp
    · have hinverse : permutation.symm position ≠ configuration.head := by
        intro heq
        apply hposition
        rw [← heq]
        simp
      simp [hposition, hinverse]

end Machine

/-- The recursive schedule contains no input-dependent branch. A compression
executes both predetermined shift scans and enables writes for one of them. -/
inductive Command
  | step
  | compress (level : ℕ)
  | expand (level : ℕ)
  deriving DecidableEq, Repr

def phase : ℕ → List Command
  | 0 => [.step]
  | level + 1 =>
      [.compress (level + 1)] ++ phase level ++
      [.compress (level + 1)] ++ phase level ++
      [.expand (level + 1), .expand (level + 1)]

def sourceSteps (commands : List Command) : ℕ :=
  (commands.map fun command => match command with | .step => 1 | _ => 0).sum

def linearWork (command : Command) : ℕ :=
  match command with
  | .step => 1
  | .compress level => 2 ^ level
  | .expand level => 2 ^ level

def totalLinearWork (commands : List Command) : ℕ := (commands.map linearWork).sum

/-- A level-`j` phase simulates exactly `2^j` source steps. -/
theorem sourceSteps_phase (level : ℕ) : sourceSteps (phase level) = 2 ^ level := by
  induction level with
  | zero => simp [phase, sourceSteps]
  | succ level ih =>
      simp only [phase, sourceSteps, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [zero_add, add_zero]
      change sourceSteps (phase level) + sourceSteps (phase level) = 2 ^ (level + 1)
      rw [ih, pow_succ]
      ring

/-- Exact phase accounting. Each cell-linear compression or expansion has
weight `2^j`; leaf steps have constant weight. -/
theorem totalLinearWork_phase (level : ℕ) :
    totalLinearWork (phase level) = (4 * level + 1) * 2 ^ level := by
  induction level with
  | zero => simp [phase, totalLinearWork, linearWork]
  | succ level ih =>
      simp only [phase, totalLinearWork, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, linearWork]
      simp only [zero_add, add_zero]
      change 2 ^ (level + 1) + totalLinearWork (phase level) +
        2 ^ (level + 1) + totalLinearWork (phase level) +
        (2 ^ (level + 1) + (2 ^ (level + 1) + 0)) = _
      rw [ih, pow_succ]
      ring

end ObliviousPhase
