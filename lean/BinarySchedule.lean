import RoutedSchedule

/-!
# Literal binary generation of a finite-alphabet causal computation

Each original event is emitted as its fixed-width one-hot binary code.
Heads reconstruct selected earlier events from their emitted bits. Opcodes
carry only the static original instruction and output-bit index. A final
step emits the original Boolean answer, rather than its event code.
-/

noncomputable section
namespace BinarySchedule
open TransformerAC0

variable {front steps heads opcodes vocabulary : ℕ}

def bitToken (bit : Bool) : Fin 2 := if bit then 1 else 0
def tokenBit (token : Fin 2) : Bool := decide (token = 1)

@[simp] theorem tokenBit_bitToken (bit : Bool) : tokenBit (bitToken bit) = bit := by
  cases bit <;> simp [tokenBit, bitToken]

@[simp] theorem bitToken_tokenBit (token : Fin 2) : bitToken (tokenBit token) = token := by
  fin_cases token <;> simp [tokenBit, bitToken]

def eventTime (hv : 0 < vocabulary) (time : Fin (steps * vocabulary + 1)) : Fin (steps + 1) :=
  ⟨time.val / vocabulary, by
    have ht := time.isLt
    have hd := Nat.div_mul_le_self time.val vocabulary
    have hm := Nat.mod_lt time.val hv
    have he := Nat.mod_add_div time.val vocabulary
    nlinarith⟩

def codeBit (hv : 0 < vocabulary) (time : Fin (steps * vocabulary + 1)) : Fin vocabulary :=
  ⟨time.val % vocabulary, Nat.mod_lt _ hv⟩

def readPosition (hv : 0 < vocabulary) (time : Fin (steps * vocabulary + 1))
    (source : Fin (front + (eventTime hv time).val)) (bit : Fin vocabulary) :
    Fin (front * vocabulary + time.val) :=
  ⟨source.val * vocabulary + bit.val, by
    have hs := source.isLt
    have hb := bit.isLt
    have hq := Nat.div_mul_le_self time.val vocabulary
    have hsource := Nat.mul_le_mul_right vocabulary (Nat.succ_le_of_lt hs)
    change (_ + 1) * vocabulary ≤ (front + time.val / vocabulary) * vocabulary at hsource
    nlinarith⟩

def sourcePosition (schedule : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (time : Fin (steps * vocabulary + 1)) (head : Fin heads) (bit : Fin vocabulary) :
    Fin (front * vocabulary + time.val) := readPosition hv time (schedule.source (eventTime hv time) head) bit

def opcode (schedule : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (time : Fin (steps * vocabulary + 1)) : Fin (opcodes * (vocabulary + 1)) :=
  finProdFinEquiv (schedule.opcode (eventTime hv time),
    if time.val = steps * vocabulary then Fin.last vocabulary else (codeBit hv time).castSucc)

def schedule (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary) :
    RoutedSchedule.Schedule (front * vocabulary) (steps * vocabulary) (heads * vocabulary) (opcodes * (vocabulary + 1)) where
  front_positive := Nat.mul_pos original.front_positive hv
  source time head := sourcePosition original hv time (finProdFinEquiv.symm head).1 (finProdFinEquiv.symm head).2
  opcode := opcode original hv

def transition (hv : 0 < vocabulary)
    (original : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (instruction : Fin (opcodes * (vocabulary + 1))) (selected : Fin (heads * vocabulary) → Fin 2) : Fin 2 :=
  let data := finProdFinEquiv.symm instruction
  let token := original data.1 (fun head => RoutedMatrix.decodeIndicator hv
    (fun bit => tokenBit (selected (finProdFinEquiv (head, bit)))))
  bitToken (Fin.lastCases (label token) (fun bit => RoutedMatrix.indicator token bit) data.2)

def prompt (original : Fin front → Fin vocabulary) : Fin (front * vocabulary) → Fin 2 :=
  fun wire => let pair := finProdFinEquiv.symm wire; bitToken (RoutedMatrix.indicator (original pair.1) pair.2)

def target (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (originalTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (plain : Fin front → Fin vocabulary) (time : Fin (steps * vocabulary + 1)) : Fin 2 :=
  if time.val = steps * vocabulary then bitToken (label (RoutedSchedule.token original originalTransition plain (Fin.last steps)))
  else bitToken (RoutedMatrix.indicator (RoutedSchedule.token original originalTransition plain (eventTime hv time)) (codeBit hv time))

theorem quotient_block (hv : 0 < vocabulary) (time : ℕ) (bit : Fin vocabulary) :
    (time * vocabulary + bit.val) / vocabulary = time := by
  rw [Nat.add_comm, Nat.mul_comm time vocabulary, Nat.add_mul_div_left _ _ hv, Nat.div_eq_of_lt bit.isLt]
  omega

theorem remainder_block (time : ℕ) (bit : Fin vocabulary) :
    (time * vocabulary + bit.val) % vocabulary = bit.val := by
  rw [Nat.add_comm, Nat.mul_comm time vocabulary, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bit.isLt]

theorem read_word (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (originalTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (plain : Fin front → Fin vocabulary) (time : Fin (steps * vocabulary + 1))
    (source : Fin (front + (eventTime hv time).val)) (bit : Fin vocabulary) :
    tokenBit (RoutedSchedule.word (prompt plain) time.val
      (fun previous => target original hv originalTransition label plain ⟨previous.val, previous.isLt.trans time.isLt⟩)
      (readPosition hv time source bit)) =
        RoutedMatrix.indicator (RoutedSchedule.word plain (eventTime hv time).val
          (fun previous => RoutedSchedule.token original originalTransition plain
            ⟨previous.val, previous.isLt.trans (eventTime hv time).isLt⟩) source) bit := by
  refine Fin.addCases (fun initial => ?_) (fun previous => ?_) source
  · have hposition : readPosition hv time (Fin.castAdd (eventTime hv time).val initial) bit =
        Fin.castAdd time.val (finProdFinEquiv (initial, bit)) := by
      apply Fin.ext
      change initial.val * vocabulary + bit.val = bit.val + vocabulary * initial.val
      ring
    rw [hposition]
    simp [RoutedSchedule.word, prompt]
  · let prior : Fin time.val := ⟨previous.val * vocabulary + bit.val, by
      have hp := (readPosition hv time (Fin.natAdd front previous) bit).isLt
      change (front + previous.val) * vocabulary + bit.val < front * vocabulary + time.val at hp
      nlinarith⟩
    have hposition : readPosition hv time (Fin.natAdd front previous) bit = Fin.natAdd (front * vocabulary) prior := by
      apply Fin.ext
      change (front + previous.val) * vocabulary + bit.val = front * vocabulary + (previous.val * vocabulary + bit.val)
      ring
    have hnotlast : prior.val ≠ steps * vocabulary := by have ht := time.isLt; have hp := prior.isLt; omega
    have hevent : eventTime hv (⟨prior.val, prior.isLt.trans time.isLt⟩ : Fin (steps * vocabulary + 1)) =
        ⟨previous.val, previous.isLt.trans (eventTime hv time).isLt⟩ := by
      apply Fin.ext
      exact quotient_block hv previous.val bit
    have hbit : codeBit hv (⟨prior.val, prior.isLt.trans time.isLt⟩ : Fin (steps * vocabulary + 1)) = bit := by
      apply Fin.ext
      exact remainder_block previous.val bit
    rw [hposition]
    simp only [RoutedSchedule.word, Fin.addCases_right, target, if_neg hnotlast, tokenBit_bitToken, hevent, hbit]

theorem step_correct (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (originalTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (plain : Fin front → Fin vocabulary) (time : Fin (steps * vocabulary + 1)) :
    transition hv originalTransition label ((schedule original hv).opcode time)
      (fun head => RoutedSchedule.word (prompt plain) time.val
        (fun previous => target original hv originalTransition label plain ⟨previous.val, previous.isLt.trans time.isLt⟩)
        ((schedule original hv).source time head)) = target original hv originalTransition label plain time := by
  simp only [transition, schedule, opcode, Equiv.symm_apply_apply]
  have hreads : (fun head => RoutedMatrix.decodeIndicator hv
      (fun bit => tokenBit (RoutedSchedule.word (prompt plain) time.val
        (fun previous => target original hv originalTransition label plain ⟨previous.val, previous.isLt.trans time.isLt⟩)
        (sourcePosition original hv time (finProdFinEquiv.symm (finProdFinEquiv (head, bit))).1
          (finProdFinEquiv.symm (finProdFinEquiv (head, bit))).2)))) =
      (fun head => RoutedSchedule.word plain (eventTime hv time).val
        (fun previous => RoutedSchedule.token original originalTransition plain
          ⟨previous.val, previous.isLt.trans (eventTime hv time).isLt⟩) (original.source (eventTime hv time) head)) := by
    funext head
    simp only [Equiv.symm_apply_apply, sourcePosition, read_word, RoutedMatrix.decodeIndicator_indicator]
  simp only [Equiv.symm_apply_apply] at hreads
  rw [hreads]
  have hplain : originalTransition (original.opcode (eventTime hv time))
      (fun head => RoutedSchedule.word plain (eventTime hv time).val
        (fun previous => RoutedSchedule.token original originalTransition plain
          ⟨previous.val, previous.isLt.trans (eventTime hv time).isLt⟩) (original.source (eventTime hv time) head)) =
      RoutedSchedule.token original originalTransition plain (eventTime hv time) := by rw [RoutedSchedule.token]
  rw [hplain]
  by_cases hlast : time.val = steps * vocabulary
  · have hevent : eventTime hv time = Fin.last steps := by
      apply Fin.ext
      change time.val / vocabulary = steps
      rw [hlast, Nat.mul_div_cancel _ hv]
    simp [target, hlast, hevent]
  · simp [target, hlast]

theorem token_correct (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (originalTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (plain : Fin front → Fin vocabulary) (time : Fin (steps * vocabulary + 1)) :
    RoutedSchedule.token (schedule original hv) (transition hv originalTransition label) (prompt plain) time =
      target original hv originalTransition label plain time := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h n ih =>
      rw [RoutedSchedule.token]
      have hprevious : (fun previous : Fin time.val =>
          RoutedSchedule.token (schedule original hv) (transition hv originalTransition label) (prompt plain)
            ⟨previous.val, previous.isLt.trans time.isLt⟩) =
          (fun previous : Fin time.val => target original hv originalTransition label plain
            ⟨previous.val, previous.isLt.trans time.isLt⟩) := by
        funext previous
        exact ih previous.val (by omega) _ rfl
      rw [hprevious]
      exact step_correct original hv originalTransition label plain time

end BinarySchedule
