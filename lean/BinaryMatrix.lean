import BinarySchedule
import ScheduleMatrix

/-!
# Actual binary-token matrix generation

The one-layer shared numerical model emits one of two vocabulary tokens at
every event, rather than emitting a larger alphabet followed by a binary
encoding. Its local heads reconstruct the original computation's selected
events from the previously emitted fixed-width binary blocks.
-/

noncomputable section
namespace BinaryMatrix
open TransformerAC0
variable {front steps heads opcodes vocabulary : ℕ}

def negateLiteral : Autoregressive.ContextLiteral n → Autoregressive.ContextLiteral n
  | .constant bit => .constant (!bit)
  | .positive wire => .negative wire
  | .negative wire => .positive wire

@[simp] theorem negateLiteral_correct (literal : Autoregressive.ContextLiteral n) (input : Bits n) :
    (negateLiteral literal).eval input = !(literal.eval input) := by
  cases literal <;> simp [negateLiteral, Autoregressive.ContextLiteral.eval]

def promptLiteral (literal : Fin (front * vocabulary) → Autoregressive.ContextLiteral n) :
    Fin (front * vocabulary * 2) → Autoregressive.ContextLiteral n := fun wire =>
  let pair := finProdFinEquiv.symm wire
  if pair.2 = 1 then literal pair.1 else negateLiteral (literal pair.1)

def model (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool) :=
  RoutedSchedule.model (BinarySchedule.schedule original hv) (by decide : 0 < 2)
    (BinarySchedule.transition hv transition label) BinarySchedule.tokenBit

def inputEncoding (plain : Fin front → Fin vocabulary) := RoutedMatrix.promptInput (BinarySchedule.prompt plain)

theorem promptLiteral_correct (literal : Fin (front * vocabulary) → Autoregressive.ContextLiteral n)
    (input : Bits n) (plain : Fin front → Fin vocabulary)
    (correct : ∀ wire, (literal wire).eval input = RoutedMatrix.promptInput plain wire)
    (wire : Fin (front * vocabulary * 2)) :
    (promptLiteral literal wire).eval input = inputEncoding plain wire := by
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  fin_cases token <;>
    simp [promptLiteral, correct, inputEncoding, RoutedMatrix.promptInput, BinarySchedule.prompt,
      BinarySchedule.bitToken, RoutedMatrix.indicator] <;> split_ifs <;> simp_all

theorem generated_correct (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (plain : Fin front → Fin vocabulary) (time : Fin (steps * vocabulary + 1)) :
    (model original hv transition label).generatedToken (inputEncoding plain) time =
      BinarySchedule.target original hv transition label plain time := by
  unfold model inputEncoding
  rw [RoutedSchedule.generated_correct, BinarySchedule.token_correct]

theorem output_correct (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (plain : Fin front → Fin vocabulary) :
    (model original hv transition label).answer (inputEncoding plain) =
      label (RoutedSchedule.token original transition plain (Fin.last steps)) := by
  unfold CausalAutoregressive.Model.answer
  rw [generated_correct]
  change BinarySchedule.tokenBit (BinarySchedule.target original hv transition label plain (Fin.last (steps * vocabulary))) = _
  simp [BinarySchedule.target]

def inputLiteral (front vocabulary : ℕ) : Fin (front * vocabulary * 2) → Autoregressive.ContextLiteral (front * vocabulary) :=
  fun wire => let pair := finProdFinEquiv.symm wire
    if pair.2 = 1 then .positive pair.1 else .negative pair.1

theorem inputLiteral_correct (plain : Fin front → Fin vocabulary) (wire : Fin (front * vocabulary * 2)) :
    (inputLiteral front vocabulary wire).eval (RoutedMatrix.promptInput plain) = inputEncoding plain wire := by
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  fin_cases token <;>
    simp [inputLiteral, Autoregressive.ContextLiteral.eval, inputEncoding, RoutedMatrix.promptInput,
      BinarySchedule.prompt, BinarySchedule.bitToken, RoutedMatrix.indicator] <;> split_ifs <;> simp_all

def inputCircuit (front vocabulary : ℕ) : Circuit (front * vocabulary) (front * vocabulary * 2) :=
  .bundle fun wire => (inputLiteral front vocabulary wire).circuit

theorem inputCircuit_correct (plain : Fin front → Fin vocabulary) :
    Circuit.eval (inputCircuit front vocabulary) (RoutedMatrix.promptInput plain) = inputEncoding plain := by
  funext wire
  simp only [inputCircuit, Circuit.eval, Autoregressive.ContextLiteral.eval_circuit]
  exact inputLiteral_correct plain wire

theorem inputCircuit_depth (front vocabulary : ℕ) : Circuit.depth (inputCircuit front vocabulary) ≤ 1 := by
  simp only [inputCircuit, Circuit.depth]
  exact Finset.sup_le fun _ _ => Autoregressive.ContextLiteral.depth_circuit_le_one _

theorem precision_fixed (original : RoutedSchedule.Schedule front steps heads opcodes) (hv : 0 < vocabulary)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool) :
    (model original hv transition label).parameters.scalarBits =
      RoutedMatrix.precision 2 (heads * vocabulary) (opcodes * (vocabulary + 1)) := rfl

end BinaryMatrix
