import TokenSymbolic
import ElementaryTaskUpper

/-!
# The full-uniform addition lower bound on the paper's alphabet {1,…,100}

`Fin 100` names the symbols, but their numerical values are `symbol.val+1`.
The pairing flips the parity coordinate of the older zero-based pairing.
-/

noncomputable section
namespace TaskReductions

def flipAdditionPair : Bool × Fin 50 ≃ Bool × Fin 50 where
  toFun pair := (!pair.1, pair.2)
  invFun pair := (!pair.1, pair.2)
  left_inv pair := by simp
  right_inv pair := by simp

def positiveAdditionPairing100 : Fin 100 ≃ Bool × Fin 50 := additionPairing100.trans flipAdditionPair

@[simp] theorem positiveAdditionPairing100_fst (symbol : Fin 100) :
    (positiveAdditionPairing100 symbol).1 = decide ((symbol.val + 1) % 2 = 1) := by
  have hmod : symbol.val % 2 = 0 ∨ symbol.val % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;>
    simp [positiveAdditionPairing100, flipAdditionPair, additionPairing100, Nat.add_mod, hmod]

end TaskReductions

namespace TokenSymbolic
open TransformerAC0 TaskReductions
variable {n bound : ℕ}

theorem positive_addition100_uniform_expected_length
    (tal : Tal.FourierTailTheorem) (model : Generator n bound (Fin 100))
    (correct : ∀ input, model.answer input = additionLSB (fun i => (input i).val + 1))
    (hn : 1 ≤ n) (hv : 1 < model.core.architecture.vocabulary) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) /
      Real.logb 2 (model.core.architecture.vocabulary : ℝ) ≤ model.expectedLength := by
  apply model.uniform_expected_length_lower_bound tal positiveAdditionPairing100 _ hn hv
  intro input
  rw [correct, ← ElementaryTaskUpper.addition_parity]
  simp only [positiveAdditionPairing100_fst, ElementaryTaskUpper.additionBit]

end TokenSymbolic
