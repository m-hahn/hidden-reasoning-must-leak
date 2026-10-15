import MultitapeMatrix
import DelimitedWord

/-!
# Output capacity derived from source time and raw input length

Unit-motion heads cannot write at or beyond their initial address plus the
number of elapsed transitions. A raw N-symbol input and T source transitions
therefore supply an output capacity N+T+1, including EOS. Output length is
not an extra simulation assumption.
-/

noncomputable section
namespace MultitapeTuring.Machine
variable {tapes : ℕ} {State Symbol : Type*}

theorem tape_eq_initial_above (machine : MultitapeTuring.Machine tapes State Symbol)
    (configuration : MultitapeTuring.Configuration tapes State Symbol) (time : ℕ) (tape : Fin tapes) (position : ℤ)
    (above : configuration.head tape + (time : ℤ) ≤ position) :
    (machine.run time configuration).tape tape position = configuration.tape tape position := by
  induction time with
  | zero => rfl
  | succ time ih =>
      have hhead := (abs_le.mp (machine.head_distance_le configuration time tape)).2
      have hne : position ≠ (machine.run time configuration).head tape := by omega
      simp only [run, step]
      rw [Function.update_of_ne hne]
      exact ih (by omega)

end MultitapeTuring.Machine

namespace MultitapeOutputCapacity
open TransformerAC0 MultitapeMatrix
variable {tapes n : ℕ} {State Symbol Alphabet : Type*}

theorem blank_above (machine : MultitapeTuring.Machine tapes State Symbol) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (input : Bits n) (time : ℕ) :
    (machine.run time (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).tape
      outputTape ((n + time : ℕ) : ℤ) = blank := by
  rw [machine.tape_eq_initial_above _ time outputTape _ (by
    change (0 : ℤ) + time ≤ ((n + time : ℕ) : ℤ)
    omega)]
  change bitTape blank bitSymbol inputTape input outputTape ((n + time : ℕ) : ℤ) = blank
  unfold bitTape
  rw [dif_neg (by omega)]

theorem word_length (machine : MultitapeTuring.Machine tapes State Symbol) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (input : Bits n) (time : ℕ)
    (read : Symbol → Option Alphabet) (blank_eos : read blank = none) (word : List Alphabet)
    (source_correct : ∀ position : ℕ,
      read ((machine.run time (MultitapeEfficientPhase.sourceInitial machine
        (bitTape blank bitSymbol inputTape input))).tape outputTape (position : ℤ)) = word[position]?) :
    word.length ≤ n + time := by
  have hnone : word[n + time]? = none := by
    rw [← source_correct, blank_above, blank_eos]
  exact List.getElem?_eq_none_iff.mp hnone

theorem capacity_polynomial (time n coefficient exponent : ℕ) (hexponent : 1 ≤ exponent)
    (htime : time ≤ coefficient * (n + 1) ^ exponent) :
    n + time + 1 ≤ (coefficient + 1) * (n + 1) ^ exponent := by
  have hp : n + 1 ≤ (n + 1) ^ exponent := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < n + 1) hexponent
  nlinarith

end MultitapeOutputCapacity
