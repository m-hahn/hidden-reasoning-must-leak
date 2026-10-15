import PlainBinaryWord
import ExactTasks

/-! # Unconditional exact-alphabet upper models for the elementary tasks -/
noncomputable section
namespace PlainTasks
open TransformerAC0 Encryption TaskReductions ElementaryTaskUpper ExactTaskAlphabet
variable {Control Input : Type*} [Fintype Control] [Fintype Input] [Inhabited Control] [Inhabited Input]
variable {vocabulary n : ℕ}

def model (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (label : Fin vocabulary → Bool) (n : ℕ) :=
  ExactFold.model alphabet initial update n (PlainBinaryWord.zeroPad (EncryptedFold.payloadLength Control Input n + 1)) label

def inputEncoding (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (input : Fin n → Input) :=
  ExactFold.inputEncoding alphabet initial update input (fun index : Fin 0 => Fin.elim0 index)

theorem generated_output (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (label : Fin vocabulary → Bool)
    (input : Fin n → Input) (output : Fin 2) :
    (model alphabet initial update label n).generatedToken (inputEncoding alphabet initial update input)
      ⟨EncryptedFold.payloadLength Control Input n + 1 + output.val, by
        change EncryptedFold.payloadLength Control Input n + 1 + output.val < EncryptedFold.payloadLength Control Input n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (alphabet.output (EncryptedFold.outputCode
        (if output = 0 then some ((List.ofFn input).foldl update initial) else none))) :=
  ExactFold.generated_output _ _ _ _ _ _ _ _

theorem context_linear (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (label : Fin vocabulary → Bool) (n : ℕ) :
    (model alphabet initial update label n).architecture.contextLength =
      (2 * n + 4) * ObliviousMatrix.vocabulary Control Input + 2 :=
  EncryptedFold.context_length initial update n (PlainBinaryWord.zeroPad _) |>.trans (by simp)

theorem architecture_fixed (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (label : Fin vocabulary → Bool) :
    ∃ heads precision : ℕ, ∀ n, (model alphabet initial update label n).architecture.layers = 1 ∧
      (model alphabet initial update label n).architecture.heads = heads ∧
      (model alphabet initial update label n).parameters.scalarBits = precision := by
  refine ⟨(model alphabet initial update label 0).architecture.heads, (model alphabet initial update label 0).parameters.scalarBits, ?_⟩
  intro n
  exact ⟨rfl, rfl, rfl⟩

def padFamily : NC0GeneratorFamily (fun _ => 0) (fun n => EncryptedFold.payloadLength Control Input n + 1) where
  locality := 0
  generator _ := PlainBinaryWord.zeroPad _

theorem polynomial_resources (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (label : Fin vocabulary → Bool) :
    ∃ D P : ℕ, ∀ n, (model alphabet initial update label n).architecture.hiddenWidth ≤ D * (n + 1) ∧
      (model alphabet initial update label n).architecture.parameterCount ≤ P * (n + 1) ^ 2 := by
  simpa only [pow_one, Nat.mul_one] using ExactEncryptedAlphabet.polynomial_resources alphabet
    (EncryptedFold.originalSchedule initial update) EncryptedFold.originalTransition (padFamily (Control := Control) (Input := Input))
    (fun n => EncryptedFold.sources n) (fun _ => EncryptedFold.decode (Control := Control) (Alphabet := Input)) label
    (4 * ObliviousMatrix.vocabulary Control Input + 3) 1 (fun n => by
      change (model alphabet initial update label n).architecture.contextLength + 1 ≤ _
      rw [context_linear, pow_one]
      nlinarith)

theorem parity_output (input : Bits n) (output : Fin 2) :
    (model binaryAlphabet false Bool.xor binaryAlphabet.readBit n).generatedToken
      (inputEncoding binaryAlphabet false Bool.xor input)
      ⟨EncryptedFold.payloadLength Bool Bool n + 1 + output.val, by
        change EncryptedFold.payloadLength Bool Bool n + 1 + output.val < EncryptedFold.payloadLength Bool Bool n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (binaryOutput (boolCode (if output = 0 then some (Tal.parity input) else none))) := by
  rw [generated_output, show (List.ofFn input).foldl Bool.xor false = Tal.parity input from xorFold_parity input]
  rfl

local instance : Fintype S5 := groupEnumeration
theorem s5_output (input : Fin n → S5) (output : Fin 2) :
    (model groupAlphabet (1 : S5) (· * ·) groupReadBit n).generatedToken
      (inputEncoding groupAlphabet (1 : S5) (· * ·) input)
      ⟨EncryptedFold.payloadLength S5 S5 n + 1 + output.val, by
        change EncryptedFold.payloadLength S5 S5 n + 1 + output.val < EncryptedFold.payloadLength S5 S5 n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (groupOutput (groupOptionCode (if output = 0 then some (orderedProduct input) else none))) := by
  rw [generated_output, ← List.prod_eq_foldl, orderedProduct_ofFn]
  rfl

theorem addition_output (input : Fin n → Fin 100) (output : Fin 2) :
    (model additionAlphabet false additionUpdate additionAlphabet.readBit n).generatedToken
      (inputEncoding additionAlphabet false additionUpdate input)
      ⟨EncryptedFold.payloadLength Bool (Fin 100) n + 1 + output.val, by
        change EncryptedFold.payloadLength Bool (Fin 100) n + 1 + output.val < EncryptedFold.payloadLength Bool (Fin 100) n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (additionOutput (boolCode (if output = 0 then
        some (additionLSB (fun i => (input i).val + 1)) else none))) := by
  rw [generated_output, fold_addition, List.map_ofFn]
  simp only [Function.comp_def]
  rw [show (List.ofFn (fun i => ElementaryTaskUpper.additionBit (input i))).foldl Bool.xor false =
    additionLSB (fun i => (input i).val + 1) from (xorFold_parity _).trans (addition_parity input)]
  rfl

end PlainTasks
