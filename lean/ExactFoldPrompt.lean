import ExactFold
import CausalSymbolicToken

/-! # Literal raw-symbol initialization of the exact-alphabet fold matrices -/

noncomputable section
namespace ExactFoldPrompt
open TransformerAC0 UniformTaskFootprint Encryption
variable {Input Control : Type*} [DecidableEq Input]
variable [Fintype Input] [Fintype Control] [Inhabited Input] [Inhabited Control]
variable {n vocabulary seedLength : ℕ}

def negate : SymbolLiteral n Input → SymbolLiteral n Input
  | .constant bit => .constant (!bit)
  | .equals index symbol => .test index (fun value => !(decide (value = symbol)))
  | .test index predicate => .test index (fun value => !(predicate value))

@[simp] theorem negate_correct (literal : SymbolLiteral n Input) (input : Fin n → Input) :
    (negate literal).eval input = !(literal.eval input) := by cases literal <;> rfl

theorem position (initial : Control) (update : Control → Input → Control) (n time : ℕ) :
    (FoldProgram.program initial update n).position time = time := by
  dsimp [ObliviousProgram.Program.position, FoldProgram.program]
  split_ifs <;> rfl

def finiteLiteral (initial : Control) (n : ℕ) :
    Fin ((n + 3) * ObliviousMatrix.vocabulary Control Input) → SymbolLiteral n Input := fun wire =>
  let pair := finProdFinEquiv.symm wire
  Fin.cases (.constant (decide (pair.2 = ObliviousMatrix.tokenCode (.inl initial))))
    (fun time => if h : time.val < n then
      .test ⟨time.val, h⟩ (fun value => decide (pair.2 = ObliviousMatrix.tokenCode (.inr (.inl value))))
      else .constant (decide (pair.2 = ObliviousMatrix.tokenCode (.inr (.inl (default : Input)))))) pair.1

theorem finiteLiteral_correct (initial : Control) (update : Control → Input → Control)
    (input : Fin n → Input) (wire) :
    (finiteLiteral initial n wire).eval input = RoutedMatrix.promptInput
      (ObliviousMatrix.prompt (FoldProgram.program initial update n) (n + 1) input) wire := by
  obtain ⟨⟨p, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [finiteLiteral, RoutedMatrix.promptInput, ObliviousMatrix.front, Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun time => ?_) p
  · simp only [ObliviousMatrix.prompt, ObliviousMatrix.front, Equiv.symm_apply_apply, Fin.cases_zero, SymbolLiteral.eval]
    rfl
  · simp only [Fin.cases_succ, ObliviousMatrix.prompt, ObliviousMatrix.front, Equiv.symm_apply_apply, position]
    dsimp [FoldProgram.program]
    split_ifs <;> rfl

def binaryLiteral (initial : Control) (n : ℕ) :
    Fin ((n + 3) * ObliviousMatrix.vocabulary Control Input * 2) → SymbolLiteral n Input := fun wire =>
  let pair := finProdFinEquiv.symm wire
  if pair.2 = 1 then finiteLiteral initial n pair.1 else negate (finiteLiteral initial n pair.1)

theorem binaryLiteral_correct (initial : Control) (update : Control → Input → Control)
    (input : Fin n → Input) (wire) :
    (binaryLiteral initial n wire).eval input = RoutedMatrix.promptInput (EncryptedFold.plainPrompt initial update input) wire := by
  obtain ⟨⟨p, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  have hc := finiteLiteral_correct initial update input p
  fin_cases token <;>
    simp [binaryLiteral, hc, EncryptedFold.plainPrompt, ObliviousMatrix.front, EncryptedFold.eventCount,
      RoutedMatrix.promptInput, BinarySchedule.prompt, BinarySchedule.bitToken, RoutedMatrix.indicator] <;>
      split_ifs <;> simp_all

def mappedLiteral (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary outputCard)
    (literal : Fin 2 → SymbolLiteral n Input) (token : Fin (vocabulary + 1)) : SymbolLiteral n Input :=
  if token = ProtocolMatrix.dataToken (alphabet.bit false) then literal 0
  else if token = ProtocolMatrix.dataToken (alphabet.bit true) then literal 1
  else .constant false

theorem mappedLiteral_correct (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary outputCard)
    (literal : Fin 2 → SymbolLiteral n Input) (input : Fin n → Input) (plain : Fin 2)
    (correct : ∀ token, (literal token).eval input = decide (token = plain)) (token : Fin (vocabulary + 1)) :
    (mappedLiteral alphabet literal token).eval input =
      decide (token = ProtocolMatrix.dataToken (alphabet.bit (BinarySchedule.tokenBit plain))) := by
  have hne : ProtocolMatrix.dataToken (alphabet.bit false) ≠ ProtocolMatrix.dataToken (alphabet.bit true) := by
    intro heq
    have hb := ExactEncryptedAlphabet.bit_injective alphabet (Fin.castSucc_injective _ heq)
    cases hb
  fin_cases plain <;>
    by_cases hfalse : token = ProtocolMatrix.dataToken (alphabet.bit false) <;>
    by_cases htrue : token = ProtocolMatrix.dataToken (alphabet.bit true)
  all_goals simp [mappedLiteral, hfalse, htrue, correct, BinarySchedule.tokenBit]
  all_goals simp_all [SymbolLiteral.eval]

def prompt (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (n : ℕ) (seed : Bits seedLength) :
    Fin ((seedLength + (n + 3) * ObliviousMatrix.vocabulary Control Input) * (vocabulary + 1)) → SymbolLiteral n Input := fun wire =>
  let pair := finProdFinEquiv.symm wire
  Fin.addCases
    (fun index => .constant (decide (pair.2 = ProtocolMatrix.dataToken (alphabet.bit (seed index)))))
    (fun index => mappedLiteral alphabet (fun token => binaryLiteral initial n (finProdFinEquiv (index, token))) pair.2) pair.1

theorem prompt_correct (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (input : Fin n → Input) (seed : Bits seedLength) :
    CausalSymbolicToken.promptInput (prompt alphabet initial n seed) input =
      ExactFold.inputEncoding alphabet initial update input seed := by
  rw [ExactFold.inputEncoding, ExactEncryptedAlphabet.inputEncoding_eq]
  funext wire
  obtain ⟨⟨p, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [CausalSymbolicToken.promptInput, prompt, RoutedMatrix.promptInput, EncryptedFold.plainPrompt,
    ObliviousMatrix.front, EncryptedFold.eventCount, Equiv.symm_apply_apply]
  refine Fin.addCases (fun index => ?_) (fun index => ?_) p
  · simp only [Equiv.symm_apply_apply, Fin.addCases_left, SymbolLiteral.eval]
  · simp only [Equiv.symm_apply_apply, Fin.addCases_right]
    apply mappedLiteral_correct
    intro value
    simpa only [RoutedMatrix.promptInput, EncryptedFold.plainPrompt, ObliviousMatrix.front,
      EncryptedFold.eventCount, Equiv.symm_apply_apply] using
      binaryLiteral_correct initial update input (finProdFinEquiv (index, value))

end ExactFoldPrompt
