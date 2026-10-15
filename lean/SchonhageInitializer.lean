import MultitapeLiteralInitialization
import MultiplicationFootprint
import IntegerMultBounds.Schoenhage.Butterfly

/-! The classical multiplier's prepared operand words contain only raw
input bits and constant padding/separators. No arithmetic result is part
of the initializer. -/

noncomputable section
namespace SchonhageInitializer
open TransformerAC0 MultitapeLiteralInitialization IntegerMultBounds.Schoenhage
open IntegerMultBounds.Machine

abbrev inputTape : Fin 64 := 50
abbrev sizeTape : Fin 64 := 43

def rawWord (n : ℕ) (right : Bool) (input : Bits (n + n)) : List Bool :=
  List.ofFn fun index : Fin n => input (finSumFinEquiv (if right then .inr index else .inl index))

def rawValue (n : ℕ) (right : Bool) (input : Bits (n + n)) : ℕ := bval (rawWord n right input)

theorem rawValue_lt (n : ℕ) (right : Bool) (input : Bits (n + n)) :
    rawValue n right input < 2 ^ n := by
  simpa only [rawValue, rawWord, List.length_ofFn] using bval_lt (rawWord n right input)

theorem bits_getElem (n v i : ℕ) (hi : i < n) :
    (bits n v)[i]'(by simp; exact hi) = Nat.testBit v i := by
  induction n generalizing v i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [bits, Nat.testBit_zero]
      | succ i =>
          simpa only [bits, List.getElem_cons_succ, Nat.testBit_succ] using
            ih (v / 2) i (by omega)

theorem bits_eq_ofFn (n v : ℕ) : bits n v = List.ofFn (fun i : Fin n => Nat.testBit v i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_ofFn]
  exact bits_getElem n v i (by simpa only [length_bits] using hi)

theorem left_value (n : ℕ) (input : Bits (n + n)) :
    rawValue n false input = ((MultiplicationFootprint.residuePairBitsEquiv n).symm input).1.val := by
  let pair := (MultiplicationFootprint.residuePairBitsEquiv n).symm input
  have hword : rawWord n false input = bits n pair.1.val := by
    rw [bits_eq_ofFn]
    unfold rawWord
    congr 1
    funext i
    have h := MultiplicationFootprint.residuePairBitsEquiv_left n pair.1 pair.2 i
    rw [show MultiplicationFootprint.residuePairBitsEquiv n (pair.1, pair.2) = input from
      (MultiplicationFootprint.residuePairBitsEquiv n).apply_symm_apply input] at h
    exact h
  change bval (rawWord n false input) = pair.1.val
  rw [hword, bval_bits, Nat.mod_eq_of_lt (ZMod.val_lt pair.1)]

theorem right_value (n : ℕ) (input : Bits (n + n)) :
    rawValue n true input = ((MultiplicationFootprint.residuePairBitsEquiv n).symm input).2.val := by
  let pair := (MultiplicationFootprint.residuePairBitsEquiv n).symm input
  have hword : rawWord n true input = bits n pair.2.val := by
    rw [bits_eq_ofFn]
    unfold rawWord
    congr 1
    funext i
    have h := MultiplicationFootprint.residuePairBitsEquiv_right n pair.1 pair.2 i
    rw [show MultiplicationFootprint.residuePairBitsEquiv n (pair.1, pair.2) = input from
      (MultiplicationFootprint.residuePairBitsEquiv n).apply_symm_apply input] at h
    exact h
  change bval (rawWord n true input) = pair.2.val
  rw [hword, bval_bits, Nat.mod_eq_of_lt (ZMod.val_lt pair.2)]

def paddedWord (n width : ℕ) (right : Bool) (input : Bits (n + n)) : List Bool :=
  rawWord n right input ++ List.replicate (width + 1 - n) false

theorem paddedWord_eq (n width : ℕ) (hwidth : n ≤ width + 1) (right : Bool) (input : Bits (n + n)) :
    paddedWord n width right input = rwd width (rawValue n right input) := by
  have hlength : (paddedWord n width right input).length = width + 1 := by
    simp only [paddedWord, rawWord, List.length_append, List.length_ofFn, List.length_replicate]
    omega
  have hvalue : bval (paddedWord n width right input) = rawValue n right input := by
    simp only [paddedWord, bval_append, bval_replicate_false, mul_zero, add_zero]
    rfl
  have h := bits_bval (paddedWord n width right input)
  rw [hlength, hvalue] at h
  exact h.symm

def operandSources (n width : ℕ) (right : Bool) : List (SymbolSource (n + n) (Fin 4)) :=
  (List.ofFn fun index : Fin n => .bit
    (finSumFinEquiv (if right then .inr index else .inl index)) bitSymbol) ++
    List.replicate (width + 1 - n) (.constant (bitSymbol false))

theorem operandSources_eval (n width : ℕ) (right : Bool) (input : Bits (n + n)) :
    (operandSources n width right).map (fun source => source.eval input) =
      (paddedWord n width right input).map bitSymbol := by
  simp [operandSources, paddedWord, rawWord, SymbolSource.eval, List.map_ofFn, List.map_map, Function.comp_def]

def symbolList (n width : ℕ) (tape : Fin 64) : List (SymbolSource (n + n) (Fin 4)) :=
  if tape = inputTape then
    operandSources n width false ++ [.constant separator] ++
      operandSources n width true ++ [.constant separator]
  else if tape = sizeTape then
    List.replicate width (.constant (bitSymbol true)) ++ [.constant separator]
  else []

def sources (n width : ℕ) : Fin 64 → ℤ → SymbolSource (n + n) (Fin 4) :=
  fun tape cell => if 0 ≤ cell then (symbolList n width tape)[cell.toNat]?.getD (.constant blank)
    else .constant blank

def bank (n width : ℕ) (input : Bits (n + n)) : Fin 64 → WTape :=
  fun tape => if tape = inputTape then
    ⟨[], [paddedWord n width false input, paddedWord n width true input]⟩
  else if tape = sizeTape then ⟨[], [ones width]⟩
  else ⟨[], []⟩

theorem symbols_eval (n width : ℕ) (input : Bits (n + n)) (tape : Fin 64) :
    (symbolList n width tape).map (fun source => source.eval input) = cells (a := 0) ((bank n width input tape).right) := by
  unfold symbolList bank
  split_ifs <;>
    simp only [List.map_append, operandSources_eval] <;>
    simp [cells, syms, sym, ones, SymbolSource.eval, List.map_append, List.map_map, Function.comp_def]

theorem sources_correct (n width : ℕ) (input : Bits (n + n)) :
    initialTape (sources n width) input = (enc (a := 0) (bank n width input)).tape := by
  funext tape cell
  have hleft : (bank n width input tape).left = [] := by
    unfold bank
    split_ifs <;> rfl
  simp only [initialTape, sources, enc, WTape.tape, WTape.words, hleft, List.reverse_nil,
    List.nil_append, wordTape]
  split_ifs with hc
  · rw [← symbols_eval, List.getElem?_map]
    cases (symbolList n width tape)[cell.toNat]? <;> rfl
  · rfl

theorem heads_zero (n width : ℕ) (input : Bits (n + n)) :
    (enc (a := 0) (bank n width input)).head = fun _ => 0 := by
  funext tape
  change (bank n width input tape).pos = 0
  unfold WTape.pos bank
  split_ifs <;> rfl

end SchonhageInitializer
