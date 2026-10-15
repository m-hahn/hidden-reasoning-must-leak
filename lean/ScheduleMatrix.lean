import RoutedSchedule

/-!
# Actual shared-matrix realization of a static causal schedule

The numerical parameters are built from the schedule's source indices and
finite opcode transition. Correctness is derived from the original greedy
growing-prefix driver, not supplied as a realization field.
-/

noncomputable section
namespace RoutedSchedule
open TransformerAC0
variable {front steps heads opcodes vocabulary : ℕ}

@[ext] theorem Schedule.ext {first second : Schedule front steps heads opcodes}
    (source : first.source = second.source) (opcode : first.opcode = second.opcode) : first = second := by
  cases first
  cases second
  simp_all

def toPlan (schedule : Schedule front steps heads opcodes) : RoutedMatrix.Plan vocabulary (front + steps) heads opcodes where
  route query head := match activeTime schedule query with
    | none => ⟨0, by have hf := schedule.front_positive; omega⟩
    | some time => ⟨(schedule.source time head).val, by
        have hs := (schedule.source time head).isLt
        have ht := time.isLt
        omega⟩
  causal := by
    intro query head
    dsimp only
    split
    · exact Nat.zero_le _
    · rename_i time hactive
      have hquery := activeTime_some schedule query time hactive
      have hs := (schedule.source time head).isLt
      change (schedule.source time head).val ≤ query.val
      omega
  opcode query := schedule.opcode ((activeTime schedule query).getD ⟨0, Nat.zero_lt_succ _⟩)

theorem toPlan_route (schedule : Schedule front steps heads opcodes) (time : Fin (steps + 1)) (head : Fin heads) :
    ((toPlan (vocabulary := vocabulary) schedule).route (position schedule time) head).val = (schedule.source time head).val := by
  simp [toPlan, activeTime_position]

theorem toPlan_opcode (schedule : Schedule front steps heads opcodes) (time : Fin (steps + 1)) :
    (toPlan (vocabulary := vocabulary) schedule).opcode (position schedule time) = schedule.opcode time := by
  simp [toPlan, activeTime_position]

theorem ofPlan_toPlan (schedule : Schedule front steps heads opcodes) :
    ofPlan (toPlan (vocabulary := vocabulary) schedule) schedule.front_positive le_rfl = schedule := by
  have hs : (ofPlan (toPlan (vocabulary := vocabulary) schedule) schedule.front_positive le_rfl).source = schedule.source := by
    funext time head
    apply Fin.ext
    exact toPlan_route schedule time head
  have ho : (ofPlan (toPlan (vocabulary := vocabulary) schedule) schedule.front_positive le_rfl).opcode = schedule.opcode := by
    funext time
    exact toPlan_opcode (vocabulary := vocabulary) schedule time
  exact Schedule.ext hs ho

def opcodePositive (schedule : Schedule front steps heads opcodes) : 0 < opcodes :=
  Nat.zero_lt_of_lt ((schedule.opcode ⟨0, Nat.zero_lt_succ _⟩).isLt)

def model (schedule : Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool) :=
  RoutedMatrix.causalModel (toPlan schedule) (RoutedMatrix.transitionMap hv (opcodePositive schedule) transition)
    label hv schedule.front_positive le_rfl

theorem generated_correct (schedule : Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (prompt : Fin front → Fin vocabulary) (time : Fin (steps + 1)) :
    (model schedule hv transition label).generatedToken (RoutedMatrix.promptInput prompt) time =
      token schedule transition prompt time := by
  unfold model
  rw [RoutedMatrix.autoregressive_correct]
  have h := token_ofPlan (toPlan schedule) transition hv (opcodePositive schedule) schedule.front_positive le_rfl prompt time
  rw [ofPlan_toPlan] at h
  exact h.symm

theorem output_correct (schedule : Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (prompt : Fin front → Fin vocabulary) :
    (model schedule hv transition label).answer (RoutedMatrix.promptInput prompt) =
      label (token schedule transition prompt (Fin.last steps)) := by
  unfold CausalAutoregressive.Model.answer
  rw [generated_correct]
  rfl

end RoutedSchedule
