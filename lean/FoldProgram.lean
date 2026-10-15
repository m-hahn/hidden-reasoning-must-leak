import EncryptedObliviousMatrix
import ProtocolMatrix
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Linear-time finite-state folds, with actual numerical execution

Every input cell is read once in its public order. The constant finite
control is the accumulator, never a whole input or a tape configuration.
The final local instruction stutters and supplies a genuine output event.
-/

noncomputable section
namespace FoldProgram
open TransformerAC0 ObliviousProgram
variable {Control Alphabet : Type*} [Inhabited Alphabet] {n : ℕ}

def program (initial : Control) (update : Control → Alphabet → Control) (n : ℕ) :
    Program (Fin n → Alphabet) ℕ Control Alphabet where
  instruction time := if time < n then .read time update else .local time id
  initialControl := initial
  initialMemory input address := if h : address < n then input ⟨address, h⟩ else default

theorem memory_unchanged (initial : Control) (update : Control → Alphabet → Control)
    (input : Fin n → Alphabet) (time : ℕ) :
    ((program initial update n).configurationAt input time).memory =
      (program initial update n).initialMemory input := by
  induction time with
  | zero => rfl
  | succ time ih =>
      have hsymbol : ∀ control symbol,
          ((program initial update n).instruction time).nextSymbol control symbol = symbol := by
        intros
        dsimp [program]
        split_ifs <;> rfl
      funext address
      simp only [Program.configurationAt, execute, hsymbol]
      rw [ih]
      split_ifs with h
      · rw [h]
      · rfl

def inputPrefix (input : Fin n → Alphabet) (time : ℕ) (bounded : time ≤ n) : List Alphabet :=
  List.ofFn (fun index : Fin time => input (Fin.castLE bounded index))

theorem prefix_succ (input : Fin n → Alphabet) (time : ℕ) (bounded : time + 1 ≤ n) :
    inputPrefix input (time + 1) bounded =
      inputPrefix input time (by omega) ++ [input ⟨time, by omega⟩] := by
  rw [inputPrefix, List.ofFn_succ']
  simp only [List.concat_eq_append, inputPrefix]
  congr 2

theorem control_prefix (initial : Control) (update : Control → Alphabet → Control)
    (input : Fin n → Alphabet) (time : ℕ) (bounded : time ≤ n) :
    ((program initial update n).configurationAt input time).control =
      (inputPrefix input time bounded).foldl update initial := by
  induction time with
  | zero => simp [Program.configurationAt, program, inputPrefix]
  | succ time ih =>
      have ht : time < n := by omega
      have hins : (program initial update n).instruction time = .read time update := by simp [program, ht]
      simp only [Program.configurationAt, execute, hins,
        Instruction.address, Instruction.nextControl]
      rw [memory_unchanged, ih (by omega), prefix_succ]
      simp [program, ht]

theorem control_final (initial : Control) (update : Control → Alphabet → Control)
    (input : Fin n → Alphabet) :
    ((program initial update n).configurationAt input (n + 1)).control =
      (List.ofFn input).foldl update initial := by
  have h := control_prefix initial update input n le_rfl
  simpa [Program.configurationAt, execute, program, Instruction.nextControl, inputPrefix] using h

section Matrices
variable [Fintype Control] [Fintype Alphabet] [Inhabited Control]

def schedule (initial : Control) (update : Control → Alphabet → Control) (n : ℕ) :=
  EncryptedObliviousMatrix.schedule (program initial update n) n

def model (initial : Control) (update : Control → Alphabet → Control) (n : ℕ) :=
  ProtocolMatrix.model (schedule initial update n) ObliviousMatrix.vocabulary_positive
    ObliviousMatrix.transition (fun _ => false) n le_rfl

def inputEncoding (initial : Control) (update : Control → Alphabet → Control) (input : Fin n → Alphabet) :=
  RoutedMatrix.promptInput (fun p => ProtocolMatrix.dataToken (ObliviousMatrix.prompt (program initial update n) n input p))

/-- The actual greedy output token encodes the entire accumulator, not a
Boolean label or a supplied realization certificate. -/
theorem generated_result (initial : Control) (update : Control → Alphabet → Control)
    (input : Fin n → Alphabet) :
    ObliviousMatrix.controlOf (ObliviousMatrix.tokenCode.symm
      (ProtocolMatrix.decode ObliviousMatrix.vocabulary_positive
        ((model initial update n).generatedToken (inputEncoding initial update input) (Fin.last (n + 1))))) =
      (List.ofFn input).foldl update initial := by
  have hgenerated : (model initial update n).generatedToken (inputEncoding initial update input) (Fin.last (n + 1)) =
      ProtocolMatrix.dataToken (RoutedSchedule.token (schedule initial update n) ObliviousMatrix.transition
        (ObliviousMatrix.prompt (program initial update n) n input) (Fin.last n)) := by
    simpa [model, inputEncoding] using ProtocolMatrix.output_suffix_correct
      (schedule initial update n) ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition (fun _ => false)
      n le_rfl (ObliviousMatrix.prompt (program initial update n) n input) ⟨0, by omega⟩
  rw [hgenerated]
  rw [ProtocolMatrix.decode_data]
  unfold schedule
  rw [EncryptedObliviousMatrix.token_correct]
  simp only [ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply, ObliviousMatrix.controlOf,
    Program.traceToken_control]
  exact control_final initial update input

theorem separator_generated (initial : Control) (update : Control → Alphabet → Control)
    (input : Fin n → Alphabet) :
    (model initial update n).generatedToken (inputEncoding initial update input)
      ⟨n, by omega⟩ = ProtocolMatrix.separator (ObliviousMatrix.vocabulary Control Alphabet) :=
  ProtocolMatrix.separator_generated _ _ _ _ _ _ _

theorem context_linear (initial : Control) (update : Control → Alphabet → Control) (n : ℕ) :
    (model initial update n).architecture.contextLength = 2 * n + 3 := by
  change n + 2 + (n + 1) = _
  omega

theorem one_layer (initial : Control) (update : Control → Alphabet → Control) (n : ℕ) :
    (model initial update n).architecture.layers = 1 := rfl

theorem two_heads (initial : Control) (update : Control → Alphabet → Control) (n : ℕ) :
    (model initial update n).architecture.heads = 2 := rfl

theorem precision_fixed (initial : Control) (update : Control → Alphabet → Control) (n : ℕ) :
    (model initial update n).parameters.scalarBits =
      RoutedMatrix.precision (ObliviousMatrix.vocabulary Control Alphabet + 1) 2
        (ObliviousMatrix.opcodes Control Alphabet + 1) := rfl

end Matrices
end FoldProgram
