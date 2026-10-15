import RoutedAutoregressive
import RoutedLocalMap

/-!
# Finite local programs with causal source indices

The schedule contains only input-independent source positions and opcodes.
The token recurrence is computed from the prompt and strictly earlier
tokens. There is no supplied generation/circuit/matrix correctness field.
-/

noncomputable section
namespace RoutedSchedule
open TransformerAC0

structure Schedule (front steps heads opcodes : ℕ) where
  front_positive : 0 < front
  source : (time : Fin (steps + 1)) → Fin heads → Fin (front + time.val)
  opcode : Fin (steps + 1) → Fin opcodes

variable {front steps heads opcodes vocabulary : ℕ}

def word (prompt : Fin front → Fin vocabulary) (time : ℕ) (previous : Fin time → Fin vocabulary) :
    Fin (front + time) → Fin vocabulary := Fin.addCases prompt previous

def token (schedule : Schedule front steps heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (prompt : Fin front → Fin vocabulary) (time : Fin (steps + 1)) : Fin vocabulary :=
  transition (schedule.opcode time) (fun head => word prompt time.val
    (fun previous => token schedule transition prompt ⟨previous.val, previous.isLt.trans time.isLt⟩)
    (schedule.source time head))
termination_by time.val

def position (schedule : Schedule front steps heads opcodes) (time : Fin (steps + 1)) : Fin (front + steps) :=
  ⟨front + time.val - 1, by have ht := time.isLt; have hf := schedule.front_positive; omega⟩

def activeTime (schedule : Schedule front steps heads opcodes) (position : Fin (front + steps)) :
    Option (Fin (steps + 1)) :=
  if h : front - 1 ≤ position.val then
    some ⟨position.val + 1 - front, by have hp := position.isLt; have hf := schedule.front_positive; omega⟩
  else none

@[simp] theorem activeTime_position (schedule : Schedule front steps heads opcodes) (time : Fin (steps + 1)) :
    activeTime schedule (position schedule time) = some time := by
  have hf := schedule.front_positive
  have hbound : front - 1 ≤ (position schedule time).val := by change front - 1 ≤ front + time.val - 1; omega
  simp only [activeTime, dif_pos hbound]
  congr 1
  apply Fin.ext
  change front + time.val - 1 + 1 - front = time.val
  omega

def priorTime (schedule : Schedule front steps heads opcodes) (time : Fin (steps + 1)) (head : Fin heads) :
    Fin (steps + 1) :=
  ⟨(schedule.source time head).val - front, by
    have hp := (schedule.source time head).isLt
    have ht := time.isLt
    omega⟩

theorem activeTime_some (schedule : Schedule front steps heads opcodes) (position : Fin (front + steps))
    (time : Fin (steps + 1)) (hactive : activeTime schedule position = some time) :
    position.val + 1 = front + time.val := by
  unfold activeTime at hactive
  split_ifs at hactive with h
  · have ht := congrArg Fin.val (Option.some.inj hactive)
    dsimp only at ht
    have hf := schedule.front_positive
    omega

theorem contextWord_word (hv : 0 < vocabulary) (prompt : Fin front → Fin vocabulary)
    (time : ℕ) (previous : Fin time → Fin vocabulary) (bounded : front + time ≤ window)
    (position : Fin (front + time)) :
    RoutedMatrix.contextWord hv prompt time previous (Fin.castLE bounded position) = word prompt time previous position := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) position
  · simp [RoutedMatrix.contextWord, word, p.isLt]
  · have hp : ¬front + p.val < front := by omega
    simp [RoutedMatrix.contextWord, word, hp, p.isLt]

def ofPlan (plan : RoutedMatrix.Plan vocabulary window heads opcodes)
    (hfront : 0 < front) (bounded : front + steps ≤ window) : Schedule front steps heads opcodes where
  front_positive := hfront
  source time head :=
    let query : Fin window := ⟨front + time.val - 1, by have ht := time.isLt; omega⟩
    ⟨(plan.route query head).val, by have hr := plan.causal query head; change _ ≤ front + time.val - 1 at hr; omega⟩
  opcode time := plan.opcode ⟨front + time.val - 1, by have ht := time.isLt; omega⟩

theorem source_ofPlan (plan : RoutedMatrix.Plan vocabulary window heads opcodes)
    (hfront : 0 < front) (bounded : front + steps ≤ window) (time : Fin (steps + 1)) (head : Fin heads)
    (hv : 0 < vocabulary) (prompt : Fin front → Fin vocabulary) (previous : Fin time.val → Fin vocabulary) :
    word prompt time.val previous ((ofPlan plan hfront bounded).source time head) =
      RoutedMatrix.contextWord hv prompt time.val previous
        (plan.route ⟨front + time.val - 1, by have ht := time.isLt; omega⟩ head) := by
  have hbound : front + time.val ≤ window := by have ht := time.isLt; omega
  have heq : Fin.castLE hbound ((ofPlan plan hfront bounded).source time head) =
      plan.route ⟨front + time.val - 1, by have ht := time.isLt; omega⟩ head := rfl
  rw [← heq]
  exact (contextWord_word hv prompt time.val previous hbound _).symm

theorem token_ofPlan (plan : RoutedMatrix.Plan vocabulary window heads opcodes)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (hv : 0 < vocabulary) (ho : 0 < opcodes) (hfront : 0 < front) (bounded : front + steps ≤ window)
    (prompt : Fin front → Fin vocabulary) (time : Fin (steps + 1)) :
    token (ofPlan plan hfront bounded) transition prompt time =
      RoutedMatrix.routedToken plan (RoutedMatrix.transitionMap hv ho transition) hv hfront bounded prompt time := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h n ih =>
      rw [token, RoutedMatrix.routedToken, RoutedMatrix.transitionMap_features]
      have hprevious : (fun previous : Fin time.val =>
          token (ofPlan plan hfront bounded) transition prompt ⟨previous.val, previous.isLt.trans time.isLt⟩) =
          (fun previous : Fin time.val => RoutedMatrix.routedToken plan (RoutedMatrix.transitionMap hv ho transition)
            hv hfront bounded prompt ⟨previous.val, previous.isLt.trans time.isLt⟩) := by
        funext previous
        exact ih previous.val (by omega) _ rfl
      rw [hprevious]
      change transition (plan.opcode _) _ = transition (plan.opcode _) _
      congr 1
      funext head
      exact source_ofPlan plan hfront bounded time head hv prompt _

end RoutedSchedule
