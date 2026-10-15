import ScheduleRelabel

/-!
# Public-position recoding of a causal computation

The vocabulary may identify tokens whose roles are recoverable from their
public source positions. The recovery maps are finite opcodes, not extra
layers or input-dependent advice. Correctness is proved from source recovery;
no recovery or realization certificate is stored in the numerical model.
-/

noncomputable section
namespace ScheduleRecoding
open TransformerAC0 RoutedSchedule
variable {front steps heads opcodes oldVocabulary vocabulary : ℕ}

abbrev Opcode (opcodes heads vocabulary oldVocabulary : ℕ) :=
  Fin opcodes × (Fin heads → Fin vocabulary → Fin oldVocabulary)
noncomputable instance opcodeFintype (opcodes heads vocabulary oldVocabulary : ℕ) :
    Fintype (Opcode opcodes heads vocabulary oldVocabulary) := Fintype.ofFinite _
def opcodeCount (opcodes heads vocabulary oldVocabulary : ℕ) :=
  Fintype.card (Opcode opcodes heads vocabulary oldVocabulary)
def opcodeCode : Opcode opcodes heads vocabulary oldVocabulary ≃
    Fin (opcodeCount opcodes heads vocabulary oldVocabulary) := Fintype.equivFin _

def schedule (original : Schedule front steps heads opcodes)
    (recover : Fin (steps + 1) → Fin heads → Fin vocabulary → Fin oldVocabulary) :
    Schedule front steps heads (opcodeCount opcodes heads vocabulary oldVocabulary) where
  front_positive := original.front_positive
  source := original.source
  opcode time := opcodeCode (original.opcode time, recover time)

def transition (erase : Fin oldVocabulary → Fin vocabulary)
    (original : Fin opcodes → (Fin heads → Fin oldVocabulary) → Fin oldVocabulary)
    (opcode : Fin (opcodeCount opcodes heads vocabulary oldVocabulary)) (selected : Fin heads → Fin vocabulary) :=
  erase (original (opcodeCode.symm opcode).1 (fun head => (opcodeCode.symm opcode).2 head (selected head)))

theorem token_correct (original : Schedule front steps heads opcodes)
    (erase : Fin oldVocabulary → Fin vocabulary)
    (recover : Fin (steps + 1) → Fin heads → Fin vocabulary → Fin oldVocabulary)
    (run : Fin opcodes → (Fin heads → Fin oldVocabulary) → Fin oldVocabulary)
    (prompt : Fin front → Fin oldVocabulary)
    (recovery : ∀ time head, recover time head (erase (word prompt time.val
      (fun previous => token original run prompt ⟨previous.val, previous.isLt.trans time.isLt⟩)
      (original.source time head))) = word prompt time.val
      (fun previous => token original run prompt ⟨previous.val, previous.isLt.trans time.isLt⟩)
      (original.source time head)) (time : Fin (steps + 1)) :
    token (schedule original recover) (transition erase run) (fun p => erase (prompt p)) time =
      erase (token original run prompt time) := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h count ih =>
      rw [token]
      conv_rhs => rw [token]
      have hprevious : (fun previous : Fin time.val => token (schedule original recover)
          (transition erase run) (fun p => erase (prompt p)) ⟨previous.val, previous.isLt.trans time.isLt⟩) =
          (fun previous : Fin time.val => erase (token original run prompt ⟨previous.val, previous.isLt.trans time.isLt⟩)) := by
        funext previous
        exact ih previous.val (by omega) _ rfl
      rw [hprevious]
      simp only [schedule, transition, Equiv.symm_apply_apply]
      congr 2
      funext head
      dsimp only
      rw [word_map, recovery]

end ScheduleRecoding
