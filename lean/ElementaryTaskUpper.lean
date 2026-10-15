import FoldProgram
import TaskReductions

/-!
# Unconditional linear-time upper constructions for the elementary tasks

The S₅ result is the complete ordered product on the complete S₅ input
alphabet. Addition uses the paper's positive alphabet {1,…,100}.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace ElementaryTaskUpper
open TransformerAC0 TaskReductions
variable {n : ℕ}

-- An opaque finite enumeration avoids reducing the full permutation
-- enumeration during matrix-dimension unification.
local instance : Fintype S5 := Fintype.ofFinite S5

def xorFold (word : List Bool) := word.foldl Bool.xor false

theorem fold_xor_initial (word : List Bool) (initial : Bool) :
    word.foldl Bool.xor initial = Bool.xor initial (xorFold word) := by
  induction word generalizing initial with
  | nil => simp [xorFold]
  | cons head tail ih =>
      simp only [List.foldl_cons, xorFold, Bool.false_xor]
      rw [ih (Bool.xor initial head), ih head]
      simp [Bool.xor_assoc]

theorem xorFold_parity (input : Bits n) : xorFold (List.ofFn input) = Tal.parity input := by
  induction n with
  | zero => simp [Tal.parity, xorFold]
  | succ n ih =>
      rw [List.ofFn_succ, xorFold, List.foldl_cons, Bool.false_xor,
        fold_xor_initial, ih, Tal.parity]
      rfl

def parityModel (n : ℕ) := FoldProgram.model false Bool.xor n

theorem parity_correct (input : Bits n) :
    ObliviousMatrix.controlOf (ObliviousMatrix.tokenCode.symm
      (ProtocolMatrix.decode ObliviousMatrix.vocabulary_positive
        ((parityModel n).generatedToken (FoldProgram.inputEncoding false Bool.xor input) (Fin.last (n + 1))))) =
      Tal.parity input := by
  rw [parityModel, FoldProgram.generated_result]
  exact xorFold_parity input

theorem orderedProduct_ofFn {M : Type*} [Monoid M] (input : Fin n → M) :
    (List.ofFn input).prod = orderedProduct input := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons, orderedProduct, ih]
      rfl

def s5Model (n : ℕ) := FoldProgram.model (1 : S5) (· * ·) n

theorem s5_full_product_correct (input : Fin n → S5) :
    ObliviousMatrix.controlOf (Control := S5) (Symbol := S5) (ObliviousMatrix.tokenCode.symm
      (ProtocolMatrix.decode (ObliviousMatrix.vocabulary_positive (Control := S5) (Symbol := S5))
        ((s5Model n).generatedToken (FoldProgram.inputEncoding (1 : S5) (· * ·) input) (Fin.last (n + 1))))) =
      orderedProduct input := by
  exact (FoldProgram.generated_result (1 : S5) (· * ·) input).trans
    ((List.prod_eq_foldl.symm).trans (orderedProduct_ofFn input))

def additionBit (symbol : Fin 100) := decide ((symbol.val + 1) % 2 = 1)
def additionUpdate (state : Bool) (symbol : Fin 100) := Bool.xor state (additionBit symbol)
def additionModel (n : ℕ) := FoldProgram.model false additionUpdate n

theorem fold_addition (word : List (Fin 100)) (initial : Bool) :
    word.foldl additionUpdate initial = (word.map additionBit).foldl Bool.xor initial := by
  induction word generalizing initial with
  | nil => rfl
  | cons head tail ih => simpa [additionUpdate] using ih (additionUpdate initial head)

theorem lsb_add (a b : ℕ) : Bool.xor (decide (a % 2 = 1)) (decide (b % 2 = 1)) =
    decide ((a + b) % 2 = 1) := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  conv_rhs => rw [Nat.add_mod]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp only [ha, hb] <;> decide

theorem addition_parity (input : Fin n → Fin 100) :
    Tal.parity (fun i => additionBit (input i)) = additionLSB (fun i => (input i).val + 1) := by
  induction n with
  | zero => simp [Tal.parity, additionLSB]
  | succ n ih =>
      rw [Tal.parity]
      change Bool.xor (additionBit (input 0)) (Tal.parity (fun i => additionBit (input i.succ))) = _
      rw [ih (fun i => input i.succ)]
      simp only [additionLSB, Fin.sum_univ_succ]
      exact lsb_add ((input 0).val + 1) (∑ i : Fin n, ((input i.succ).val + 1))

theorem addition_correct (input : Fin n → Fin 100) :
    ObliviousMatrix.controlOf (Control := Bool) (Symbol := Fin 100) (ObliviousMatrix.tokenCode.symm
      (ProtocolMatrix.decode (ObliviousMatrix.vocabulary_positive (Control := Bool) (Symbol := Fin 100))
        ((additionModel n).generatedToken (FoldProgram.inputEncoding false additionUpdate input) (Fin.last (n + 1))))) =
      additionLSB (fun i => (input i).val + 1) := by
  rw [additionModel, FoldProgram.generated_result, fold_addition, List.map_ofFn]
  exact (xorFold_parity (fun i => additionBit (input i))).trans (addition_parity input)

end ElementaryTaskUpper
