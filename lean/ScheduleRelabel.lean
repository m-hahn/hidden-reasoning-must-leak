import ReadoutSchedule

/-! # Relabeling a causal recurrence without changing its computation -/

noncomputable section
namespace RoutedSchedule
open TransformerAC0
variable {front steps heads opcodes first second : ℕ}

def liftTransition (encode : Fin first → Fin second) (decode : Fin second → Fin first)
    (run : Fin opcodes → (Fin heads → Fin first) → Fin first) :
    Fin opcodes → (Fin heads → Fin second) → Fin second :=
  fun opcode selected => encode (run opcode (fun head => decode (selected head)))

theorem word_map (encode : Fin first → Fin second) (prompt : Fin front → Fin first)
    (previous : Fin time → Fin first) (source : Fin (front + time)) :
    word (fun p => encode (prompt p)) time (fun p => encode (previous p)) source =
      encode (word prompt time previous source) := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) source <;> simp [word]

theorem token_lift (schedule : Schedule front steps heads opcodes)
    (encode : Fin first → Fin second) (decode : Fin second → Fin first)
    (inverse : ∀ token, decode (encode token) = token)
    (run : Fin opcodes → (Fin heads → Fin first) → Fin first)
    (prompt : Fin front → Fin first) (time : Fin (steps + 1)) :
    token schedule (liftTransition encode decode run) (fun p => encode (prompt p)) time =
      encode (token schedule run prompt time) := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h count ih =>
      rw [token]
      conv_rhs => rw [token]
      have hprevious : (fun previous : Fin time.val =>
          token schedule (liftTransition encode decode run) (fun p => encode (prompt p))
            ⟨previous.val, previous.isLt.trans time.isLt⟩) =
          (fun previous : Fin time.val => encode (token schedule run prompt
            ⟨previous.val, previous.isLt.trans time.isLt⟩)) := by
        funext previous
        exact ih previous.val (by omega) _ rfl
      rw [hprevious]
      change encode (run (schedule.opcode time) _) = encode (run (schedule.opcode time) _)
      congr 2
      funext head
      dsimp only
      rw [word_map, inverse]

end RoutedSchedule
