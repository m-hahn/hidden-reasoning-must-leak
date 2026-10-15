import ScheduleMatrix

/-!
# A natively generated separator and output suffix

Insert one new token into a causal local program, shifting its subsequent
source addresses. The same one-layer numerical matrices generate the
payload, the separator, and every output-suffix token. The output suffix
can have any positive finite length; it is not an external serialization.
-/

noncomputable section
namespace ProtocolMatrix
open TransformerAC0 RoutedSchedule
variable {front steps heads opcodes vocabulary : ℕ}

def dataToken (token : Fin vocabulary) : Fin (vocabulary + 1) := token.castSucc
def separator (vocabulary : ℕ) : Fin (vocabulary + 1) := Fin.last vocabulary
def decode (hv : 0 < vocabulary) (token : Fin (vocabulary + 1)) : Fin vocabulary :=
  if h : token.val < vocabulary then ⟨token.val, h⟩ else ⟨0, hv⟩

@[simp] theorem decode_data (hv : 0 < vocabulary) (token : Fin vocabulary) : decode hv (dataToken token) = token := by
  simp [decode, dataToken, token.isLt]

theorem data_ne_separator (token : Fin vocabulary) : dataToken token ≠ separator vocabulary := by
  intro h
  have he := congrArg Fin.val h
  have ht := token.isLt
  change token.val = vocabulary at he
  omega

def oldTime (boundary : ℕ) (bounded : boundary ≤ steps) (time : Fin (steps + 2)) : Fin (steps + 1) :=
  ⟨if time.val ≤ boundary then time.val else time.val - 1, by split_ifs <;> have ht := time.isLt <;> omega⟩

def inserted (boundary value : ℕ) : ℕ := if value < boundary then value else value + 1

theorem oldTime_inserted (boundary : ℕ) (bounded : boundary ≤ steps) (time : Fin (steps + 1)) :
    oldTime boundary bounded ⟨inserted boundary time.val, by unfold inserted; split_ifs <;> have ht := time.isLt <;> omega⟩ = time := by
  apply Fin.ext
  simp only [oldTime, inserted]
  split_ifs <;> omega

def liftSource (boundary : ℕ) (bounded : boundary ≤ steps) (time : Fin (steps + 2))
    (source : Fin (front + (oldTime boundary bounded time).val)) : Fin (front + time.val) :=
  ⟨if source.val < front then source.val else front + inserted boundary (source.val - front), by
    have hs := source.isLt
    dsimp only [oldTime] at hs
    unfold inserted
    split_ifs at hs ⊢ <;> omega⟩

def schedule (original : Schedule front steps heads opcodes) (boundary : ℕ) (bounded : boundary ≤ steps) :
    Schedule front (steps + 1) heads (opcodes + 1) where
  front_positive := original.front_positive
  source time head := if h : time.val = boundary then ⟨0, by have hf := original.front_positive; omega⟩
    else liftSource boundary bounded time (original.source (oldTime boundary bounded time) head)
  opcode time := if time.val = boundary then Fin.last opcodes
    else (original.opcode (oldTime boundary bounded time)).castSucc

def transition (hv : 0 < vocabulary)
    (original : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (opcode : Fin (opcodes + 1)) (selected : Fin heads → Fin (vocabulary + 1)) : Fin (vocabulary + 1) :=
  Fin.lastCases (separator vocabulary)
    (fun op => dataToken (original op (fun head => decode hv (selected head)))) opcode

def target (original : Schedule front steps heads opcodes)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (boundary : ℕ) (bounded : boundary ≤ steps) (prompt : Fin front → Fin vocabulary)
    (time : Fin (steps + 2)) : Fin (vocabulary + 1) :=
  if time.val = boundary then separator vocabulary
  else dataToken (token original run prompt (oldTime boundary bounded time))

theorem read_word (original : Schedule front steps heads opcodes)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (hv : 0 < vocabulary)
    (boundary : ℕ) (bounded : boundary ≤ steps) (prompt : Fin front → Fin vocabulary)
    (time : Fin (steps + 2)) (previous : Fin time.val → Fin (vocabulary + 1))
    (correct : ∀ p, previous p = target original run boundary bounded prompt ⟨p.val, p.isLt.trans time.isLt⟩)
    (source : Fin (front + (oldTime boundary bounded time).val)) :
    decode hv (word (fun p => dataToken (prompt p)) time.val previous (liftSource boundary bounded time source)) =
      word prompt (oldTime boundary bounded time).val
        (fun p => token original run prompt ⟨p.val, p.isLt.trans (oldTime boundary bounded time).isLt⟩) source := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) source
  · have he : liftSource boundary bounded time (Fin.castAdd _ p) = Fin.castAdd time.val p := by
      apply Fin.ext
      simp [liftSource, p.isLt]
    rw [he]
    simp [word]
  · have hp : inserted boundary p.val < time.val := by
      have h := p.isLt
      dsimp only [oldTime] at h
      unfold inserted
      split_ifs at h ⊢ <;> omega
    have he : liftSource boundary bounded time (Fin.natAdd front p) =
        Fin.natAdd front ⟨inserted boundary p.val, hp⟩ := by
      apply Fin.ext
      simp [liftSource, show ¬front + p.val < front by omega]
    rw [he]
    simp only [word, Fin.addCases_right]
    rw [correct]
    have hnot : inserted boundary p.val ≠ boundary := by unfold inserted; split_ifs <;> omega
    simp only [target, hnot, ↓reduceIte, decode_data]
    congr 1
    apply Fin.ext
    change (if inserted boundary p.val ≤ boundary then inserted boundary p.val else inserted boundary p.val - 1) = p.val
    unfold inserted
    split_ifs <;> omega

theorem token_correct (original : Schedule front steps heads opcodes)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (hv : 0 < vocabulary)
    (boundary : ℕ) (bounded : boundary ≤ steps) (prompt : Fin front → Fin vocabulary) (time : Fin (steps + 2)) :
    token (schedule original boundary bounded) (transition hv run) (fun p => dataToken (prompt p)) time =
      target original run boundary bounded prompt time := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h count ih =>
      rw [token]
      by_cases hsep : time.val = boundary
      · simp [schedule, hsep, transition, target]
      · simp only [schedule, hsep, ↓reduceIte, transition, Fin.lastCases_castSucc, target]
        rw [token]
        congr 1
        congr 1
        funext head
        exact read_word original run hv boundary bounded prompt time _
          (fun p => ih p.val (by omega) ⟨p.val, p.isLt.trans time.isLt⟩ rfl) _

def label (original : Fin vocabulary → Bool) : Fin (vocabulary + 1) → Bool :=
  Fin.lastCases false original

def model (original : Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (output : Fin vocabulary → Bool)
    (boundary : ℕ) (bounded : boundary ≤ steps) :=
  RoutedSchedule.model (schedule original boundary bounded) (Nat.zero_lt_succ vocabulary)
    (transition hv run) (label output)

theorem generated_correct (original : Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (output : Fin vocabulary → Bool)
    (boundary : ℕ) (bounded : boundary ≤ steps) (prompt : Fin front → Fin vocabulary) (time : Fin (steps + 2)) :
    (model original hv run output boundary bounded).generatedToken
      (RoutedMatrix.promptInput (fun p => dataToken (prompt p))) time = target original run boundary bounded prompt time := by
  rw [model, RoutedSchedule.generated_correct, token_correct]

theorem separator_generated (original : Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (output : Fin vocabulary → Bool)
    (boundary : ℕ) (bounded : boundary ≤ steps) (prompt : Fin front → Fin vocabulary) :
    (model original hv run output boundary bounded).generatedToken
      (RoutedMatrix.promptInput (fun p => dataToken (prompt p))) ⟨boundary, by omega⟩ = separator vocabulary := by
  rw [generated_correct]
  simp [target]

theorem output_suffix_correct (original : Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (output : Fin vocabulary → Bool)
    (boundary : ℕ) (bounded : boundary ≤ steps) (prompt : Fin front → Fin vocabulary)
    (offset : Fin (steps - boundary + 1)) :
    (model original hv run output boundary bounded).generatedToken
      (RoutedMatrix.promptInput (fun p => dataToken (prompt p)))
      ⟨boundary + 1 + offset.val, by have h := offset.isLt; omega⟩ =
      dataToken (token original run prompt ⟨boundary + offset.val, by have h := offset.isLt; omega⟩) := by
  rw [generated_correct]
  simp only [target, show boundary + 1 + offset.val ≠ boundary by omega, ↓reduceIte]
  congr 1
  congr 1
  apply Fin.ext
  simp only [oldTime, show ¬boundary + 1 + offset.val ≤ boundary by omega, ↓reduceIte]
  omega

theorem precision_fixed (original : Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (run : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (output : Fin vocabulary → Bool)
    (boundary : ℕ) (bounded : boundary ≤ steps) :
    (model original hv run output boundary bounded).parameters.scalarBits =
      RoutedMatrix.precision (vocabulary + 1) heads (opcodes + 1) := rfl

end ProtocolMatrix
