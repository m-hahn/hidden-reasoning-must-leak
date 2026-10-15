import Mathlib.Data.List.OfFn

/-!
# First-EOS decoding, including empty and variable-length output words

`none` is EOS and `some symbol` is a data symbol. The decoder stops at the
first EOS; the public capacity is not mistaken for the output length.
-/

namespace DelimitedWord
variable {Alphabet : Type*}

def decode : List (Option Alphabet) → List Alphabet
  | [] => []
  | none :: _ => []
  | some symbol :: tail => symbol :: decode tail

theorem decode_getElem (word : List Alphabet) (capacity : ℕ) (bounded : word.length < capacity) :
    decode (List.ofFn (fun index : Fin capacity => word[index.val]?)) = word := by
  induction word generalizing capacity with
  | nil =>
      cases capacity with
      | zero => simp at bounded
      | succ capacity => simp [List.ofFn_succ, decode]
  | cons symbol tail ih =>
      cases capacity with
      | zero => simp at bounded
      | succ capacity =>
          simp only [List.ofFn_succ, Fin.val_zero, List.getElem?_cons_zero, decode,
            Fin.val_succ, List.getElem?_cons_succ]
          congr 1
          exact ih capacity (by simpa using bounded)

theorem first_eos (word : List Alphabet) (capacity : ℕ) (bounded : word.length < capacity) :
    (fun index : Fin capacity => word[index.val]?) ⟨word.length, bounded⟩ = none ∧
      ∀ index : Fin capacity, index.val < word.length → word[index.val]? ≠ none := by
  constructor
  · simp
  · intro index h
    simp [List.getElem?_eq_getElem h]

end DelimitedWord
