import MultitapeTuring
import IntegerMultBounds.Machine.Execution

/-! Step-preserving adaptation of a finite halting machine to the local
multitape semantics. One extra absorbing state converts a genuine halt into
the stuttering terminal configuration needed by the oblivious compiler. -/

noncomputable section
namespace MultiplicationMachineBridge

abbrev ExternalProgram := IntegerMultBounds.Machine.Program
abbrev ExternalConfig := IntegerMultBounds.Machine.Config

def direction : IntegerMultBounds.Machine.Move → ObliviousPhase.Direction
  | .left => .left
  | .stay => .stay
  | .right => .right

@[simp] theorem direction_displacement (move : IntegerMultBounds.Machine.Move) :
    (direction move).displacement = move.offset := by cases move <;> rfl

def machine {tapes states extra : ℕ} (program : ExternalProgram tapes states extra) :
    MultitapeTuring.Machine tapes (Option (Fin states)) (Fin (extra + 4)) where
  initialState := some program.start
  transition state symbols := match state with
    | none => (none, symbols, fun _ => .stay)
    | some state => match program.transition state symbols with
      | none => (none, symbols, fun _ => .stay)
      | some action =>
          (some action.1, fun tape => (action.2 tape).1, fun tape => direction (action.2 tape).2)

def configuration {tapes states extra : ℕ} (source : ExternalConfig tapes states extra) :
    MultitapeTuring.Configuration tapes (Option (Fin states)) (Fin (extra + 4)) :=
  ⟨some source.state, source.head, source.tape⟩

theorem step_corresponds {tapes states extra : ℕ} (program : ExternalProgram tapes states extra)
    (source target : ExternalConfig tapes states extra)
    (hstep : IntegerMultBounds.Machine.step program source = some target) :
    (machine program).step (configuration source) = configuration target := by
  have hscan : MultitapeTuring.Machine.scanned (configuration source) =
      (fun tape => source.tape tape (source.head tape)) := rfl
  unfold IntegerMultBounds.Machine.step at hstep
  split at hstep
  · contradiction
  · rename_i action ha
    simp only [Option.some.injEq] at hstep
    subst target
    apply MultitapeTuring.Configuration.ext
    · dsimp only [MultitapeTuring.Machine.step, MultitapeTuring.Machine.scanned, configuration, machine]
      unfold MultitapeTuring.Machine.scanned
      rw [ha]
    · funext tape
      dsimp only [MultitapeTuring.Machine.step, MultitapeTuring.Machine.scanned, configuration, machine]
      unfold MultitapeTuring.Machine.scanned
      rw [ha]
      simp only [direction_displacement]
    · funext tape position
      dsimp only [MultitapeTuring.Machine.step, MultitapeTuring.Machine.scanned, configuration, machine]
      unfold MultitapeTuring.Machine.scanned
      rw [ha]
      simp only [Function.update_apply]

theorem run_corresponds {tapes states extra : ℕ} (program : ExternalProgram tapes states extra)
    (time : ℕ) (source target : ExternalConfig tapes states extra)
    (hrun : IntegerMultBounds.Machine.run program time source = some target) :
    (machine program).run time (configuration source) = configuration target := by
  induction time generalizing source with
  | zero =>
      simp only [IntegerMultBounds.Machine.run, Option.some.injEq] at hrun
      subst target
      rfl
  | succ time ih =>
      simp only [IntegerMultBounds.Machine.run] at hrun
      cases hs : IntegerMultBounds.Machine.step program source with
      | none => simp [hs] at hrun
      | some next =>
          simp only [hs, Option.some_bind] at hrun
          rw [show time + 1 = 1 + time by omega, MultitapeTuring.Machine.run_add]
          simp only [MultitapeTuring.Machine.run]
          rw [step_corresponds program source next hs]
          exact ih next hrun

theorem halted_step {tapes states extra : ℕ} (program : ExternalProgram tapes states extra)
    (source : ExternalConfig tapes states extra)
    (halted : IntegerMultBounds.Machine.step program source = none) :
    (machine program).step (configuration source) = ⟨none, source.head, source.tape⟩ := by
  have hscan : MultitapeTuring.Machine.scanned (configuration source) =
      (fun tape => source.tape tape (source.head tape)) := rfl
  have ht : program.transition source.state (fun tape => source.tape tape (source.head tape)) = none := by
    unfold IntegerMultBounds.Machine.step at halted
    cases hh : program.transition source.state (fun tape => source.tape tape (source.head tape)) with
    | none => rfl
    | some action => simp [hh] at halted
  apply MultitapeTuring.Configuration.ext
  · dsimp only [MultitapeTuring.Machine.step, MultitapeTuring.Machine.scanned, configuration, machine]
    unfold MultitapeTuring.Machine.scanned
    rw [ht]
  · funext tape
    dsimp only [MultitapeTuring.Machine.step, MultitapeTuring.Machine.scanned, configuration, machine]
    unfold MultitapeTuring.Machine.scanned
    rw [ht]
    simp only [ObliviousPhase.Direction.displacement, add_zero]
  · funext tape position
    dsimp only [MultitapeTuring.Machine.step, MultitapeTuring.Machine.scanned, configuration, machine]
    unfold MultitapeTuring.Machine.scanned
    rw [ht]
    simp only [Function.update_eq_self]

theorem terminal {tapes states extra : ℕ} (program : ExternalProgram tapes states extra)
    (symbols : Fin tapes → Fin (extra + 4)) :
    (machine program).transition none symbols = (none, symbols, fun _ => .stay) := rfl

theorem padded_run {tapes states extra : ℕ} (program : ExternalProgram tapes states extra)
    (source target : ExternalConfig tapes states extra) (finish total : ℕ)
    (hrun : IntegerMultBounds.Machine.run program finish source = some target)
    (halted : IntegerMultBounds.Machine.step program target = none) (hbound : finish + 1 ≤ total) :
    (machine program).run total (configuration source) = ⟨none, target.head, target.tape⟩ := by
  have hfinish : (machine program).run (finish + 1) (configuration source) =
      ⟨none, target.head, target.tape⟩ := by
    rw [MultitapeTuring.Machine.run, run_corresponds program finish source target hrun]
    exact halted_step program target halted
  rw [(machine program).terminal_run_after _ (finish + 1) total hbound (by
    rw [hfinish]
    exact terminal program), hfinish]

end MultiplicationMachineBridge
