import ScheduleMatrix

/-!
# Append readouts of an already generated causal prefix

Readout addresses and opcodes are public static data. All readout heads
refer to the prompt or to the original payload, never to other readouts.
The prefix and suffix use one common finite transition and one common
shared-matrix construction.
-/

noncomputable section
namespace ReadoutSchedule
open TransformerAC0 RoutedSchedule
variable {front payload extra heads opcodes readHeads readOpcodes vocabulary : ℕ}

structure Readouts (front payload extra readHeads readOpcodes : ℕ) where
  source : Fin (extra + 1) → Fin readHeads → Fin (front + payload)
  opcode : Fin (extra + 1) → Fin readOpcodes

def prefixTime (time : Fin (payload + extra + 1)) (before : time.val < payload) : Fin (payload + 1) :=
  ⟨time.val, by omega⟩

def readTime (time : Fin (payload + extra + 1)) (after : ¬time.val < payload) : Fin (extra + 1) :=
  ⟨time.val - payload, by have ht := time.isLt; omega⟩

def extendTime (time : Fin payload) : Fin (payload + extra + 1) := Fin.castLE (by omega) time

def schedule (original : Schedule front payload heads opcodes)
    (readouts : Readouts front payload extra readHeads readOpcodes) :
    Schedule front (payload + extra) (heads + readHeads) (opcodes + readOpcodes) where
  front_positive := original.front_positive
  source time := if before : time.val < payload then
    Fin.addCases (fun head => original.source (prefixTime time before) head)
      (fun _ => ⟨0, by have hf := original.front_positive; omega⟩)
    else Fin.addCases (fun _ => ⟨0, by have hf := original.front_positive; omega⟩)
      (fun head => Fin.castLE (by omega) (readouts.source (readTime time before) head))
  opcode time := if before : time.val < payload then
    Fin.castAdd readOpcodes (original.opcode (prefixTime time before))
    else Fin.natAdd opcodes (readouts.opcode (readTime time before))

def transition (original : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (read : Fin readOpcodes → (Fin readHeads → Fin vocabulary) → Fin vocabulary)
    (opcode : Fin (opcodes + readOpcodes)) (selected : Fin (heads + readHeads) → Fin vocabulary) : Fin vocabulary :=
  Fin.addCases (fun op => original op (fun head => selected (Fin.castAdd readHeads head)))
    (fun op => read op (fun head => selected (Fin.natAdd heads head))) opcode

theorem source_before_readouts (original : Schedule front payload heads opcodes)
    (readouts : Readouts front payload extra readHeads readOpcodes)
    (time : Fin (payload + extra + 1)) (head : Fin (heads + readHeads)) :
    ((schedule original readouts).source time head).val < front + payload := by
  by_cases hbefore : time.val < payload
  · simp only [schedule, hbefore, ↓reduceDIte]
    refine Fin.addCases (fun h => ?_) (fun _ => ?_) head
    · simp only [Fin.addCases_left]
      have hs := (original.source (prefixTime time hbefore) h).isLt
      change _ < front + time.val at hs
      omega
    · simp only [Fin.addCases_right]
      have hf := original.front_positive
      omega
  · simp only [schedule, hbefore, ↓reduceDIte]
    refine Fin.addCases (fun _ => ?_) (fun h => ?_) head
    · simp only [Fin.addCases_left]
      have hf := original.front_positive
      omega
    · simp only [Fin.addCases_right]
      exact (readouts.source (readTime time hbefore) h).isLt

theorem word_prefix {first second : ℕ} (bounded : first ≤ second)
    (prompt : Fin front → Fin vocabulary) (short : Fin first → Fin vocabulary) (long : Fin second → Fin vocabulary)
    (agree : ∀ i, long (Fin.castLE bounded i) = short i) (source : Fin (front + first)) :
    word prompt second long (Fin.castLE (Nat.add_le_add_left bounded front) source) = word prompt first short source := by
  refine Fin.addCases (fun position => ?_) (fun position => ?_) source
  · have hcast : Fin.castLE (Nat.add_le_add_left bounded front) (Fin.castAdd first position) =
        Fin.castAdd second position := rfl
    rw [hcast]
    simp [word]
  · have hcast : Fin.castLE (Nat.add_le_add_left bounded front) (Fin.natAdd front position) =
        Fin.natAdd front (Fin.castLE bounded position) := rfl
    rw [hcast]
    simp only [word, Fin.addCases_right]
    exact agree position

theorem prefix_correct (original : Schedule front payload heads opcodes)
    (readouts : Readouts front payload extra readHeads readOpcodes)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (read : Fin readOpcodes → (Fin readHeads → Fin vocabulary) → Fin vocabulary)
    (prompt : Fin front → Fin vocabulary) (time : Fin payload) :
    token (schedule original readouts) (transition run read) prompt (extendTime time) =
      token original run prompt time.castSucc := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h count ih =>
      rw [token]
      conv_rhs => rw [token]
      have hbefore : (extendTime (extra := extra) time).val < payload := time.isLt
      simp only [schedule, hbefore, ↓reduceDIte, transition, Fin.addCases_left]
      congr 1
      funext head
      apply word_prefix le_rfl prompt _ _
      intro previous
      have hlt : previous.val < time.val := previous.isLt
      exact ih previous.val (by omega) ⟨previous.val, previous.isLt.trans time.isLt⟩ rfl

theorem read_correct (original : Schedule front payload heads opcodes)
    (readouts : Readouts front payload extra readHeads readOpcodes)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (read : Fin readOpcodes → (Fin readHeads → Fin vocabulary) → Fin vocabulary)
    (prompt : Fin front → Fin vocabulary) (index : Fin (extra + 1)) :
    token (schedule original readouts) (transition run read) prompt
      ⟨payload + index.val, by have h := index.isLt; omega⟩ =
      read (readouts.opcode index) (fun head => word prompt payload
        (fun previous => token original run prompt previous.castSucc) (readouts.source index head)) := by
  rw [token]
  have hnot : ¬payload + index.val < payload := by omega
  have hindex : readTime (⟨payload + index.val, by have h := index.isLt; omega⟩ : Fin (payload + extra + 1)) hnot = index := by
    apply Fin.ext
    simp [readTime]
  simp only [schedule, hnot, ↓reduceDIte, hindex, transition, Fin.addCases_right]
  congr 1
  funext head
  apply word_prefix (by omega) prompt _ _
  intro previous
  exact prefix_correct original readouts run read prompt previous

end ReadoutSchedule
