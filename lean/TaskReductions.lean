import EntropyCoding
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Perm

/-!
# Exact reductions of the paper's auxiliary tasks to parity

This file supplies the two elementary reductions used in the footprint
corollary.  For `S₅`, the sign homomorphism sends composition to XOR.  For
iterated addition, the least significant bit of the sum is the XOR of the
least significant input bits.
-/

open scoped BigOperators

noncomputable section

namespace TaskReductions

open TransformerAC0

/-! ## `S₅` state tracking -/

abbrev S5 := Equiv.Perm (Fin 5)

def oddUnit (unit : ℤˣ) : Bool := decide (unit = -1)

@[simp] theorem oddUnit_one : oddUnit 1 = false := by
  norm_num [oddUnit]

@[simp] theorem oddUnit_neg_one : oddUnit (-1) = true := by
  simp [oddUnit]

theorem oddUnit_mul (first second : ℤˣ) :
    oddUnit (first * second) = Bool.xor (oddUnit first) (oddUnit second) := by
  rcases Int.units_eq_one_or first with hfirst | hfirst <;>
    rcases Int.units_eq_one_or second with hsecond | hsecond <;>
    subst first <;> subst second <;> norm_num [oddUnit]

def orderedProduct {M : Type*} [Monoid M] : {n : ℕ} → (Fin n → M) → M
  | 0, _ => 1
  | _ + 1, value => value 0 * orderedProduct (Fin.tail value)

theorem map_orderedProduct {M N : Type*} [Monoid M] [Monoid N]
    (homomorphism : M →* N) {n : ℕ} (value : Fin n → M) :
    homomorphism (orderedProduct value) =
      orderedProduct (fun index => homomorphism (value index)) := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih =>
      rw [orderedProduct, map_mul, orderedProduct, ih]
      congr 1

theorem oddUnit_orderedProduct_parity {n : ℕ} (value : Fin n → ℤˣ) :
    oddUnit (orderedProduct value) =
      Tal.parity (fun index => oddUnit (value index)) := by
  induction n with
  | zero => simp [Tal.parity, orderedProduct]
  | succ n ih =>
      rw [orderedProduct, oddUnit_mul, Tal.parity, ih]
      rfl

/-- The Boolean quotient of `S₅` state tracking. -/
def s5StateTrackingParity {length : ℕ} (input : Fin length → S5) : Bool :=
  Tal.parity (fun index => oddUnit (Equiv.Perm.sign (input index)))

/-- The quotient is exactly the sign of the composed permutation, not merely
an ad hoc bitwise definition. -/
theorem s5StateTrackingParity_eq_product_sign {length : ℕ}
    (input : Fin length → S5) :
    s5StateTrackingParity input =
      oddUnit (Equiv.Perm.sign (orderedProduct input)) := by
  rw [s5StateTrackingParity, map_orderedProduct]
  exact (oddUnit_orderedProduct_parity _).symm

/-- Embed one parity bit as an even or odd element of `S₅`. -/
def s5Encode : Bool → S5
  | false => 1
  | true => Equiv.swap (0 : Fin 5) (1 : Fin 5)

@[simp] theorem sign_s5Encode (bit : Bool) :
    oddUnit (Equiv.Perm.sign (s5Encode bit)) = bit := by
  cases bit
  · simp [s5Encode]
  · rw [s5Encode, Equiv.Perm.sign_swap (by decide)]
    simp

/-- Exact many-one reduction from parity to the sign bit of `S₅` state
tracking. -/
theorem s5_reduces_parity {length : ℕ} (input : Bits length) :
    s5StateTrackingParity (fun index => s5Encode (input index)) =
      Tal.parity input := by
  simp [s5StateTrackingParity]

/-! ## Iterated addition -/

def bitNat : Bool → ℕ
  | false => 0
  | true => 1

/-- Least significant bit of an ordinary natural-number sum. -/
def additionLSB {length : ℕ} (input : Fin length → ℕ) : Bool :=
  decide ((∑ index, input index) % 2 = 1)

theorem parity_eq_sum_bitNat_mod_two {length : ℕ} (input : Bits length) :
    Tal.parity input =
      decide ((∑ index, bitNat (input index)) % 2 = 1) := by
  induction length with
  | zero => simp [Tal.parity]
  | succ length ih =>
      let tail : Bits length := Fin.tail input
      let tailSum := ∑ index : Fin length, bitNat (tail index)
      rw [Tal.parity, Fin.sum_univ_succ, ih tail]
      change Bool.xor (input 0) (decide (tailSum % 2 = 1)) =
        decide ((bitNat (input 0) + tailSum) % 2 = 1)
      cases hhead : input 0
      · simp [bitNat, hhead]
      · simp only [hhead, bitNat, Bool.true_xor]
        have hmod : tailSum % 2 = 0 ∨ tailSum % 2 = 1 := by
          have hlt : tailSum % 2 < 2 := Nat.mod_lt _ (by omega)
          omega
        rcases hmod with hzero | hone
        · simp [Nat.add_mod, hzero]
        · simp [Nat.add_mod, hone]

/-- Embed parity bits as the natural numbers zero and one. -/
def additionEncode (bit : Bool) : ℕ := bitNat bit

/-- Exact reduction from parity to the least significant result bit of
iterated addition. -/
theorem iterated_addition_reduces_parity {length : ℕ} (input : Bits length) :
    additionLSB (fun index => additionEncode (input index)) =
      Tal.parity input := by
  symm
  exact parity_eq_sum_bitNat_mod_two input

/-- The same reduction lands in the paper's alphabet `[100]`. -/
def additionEncode100 (bit : Bool) : Fin 100 :=
  if bit then ⟨1, by omega⟩ else ⟨0, by omega⟩

@[simp] theorem additionEncode100_val (bit : Bool) :
    (additionEncode100 bit).val = bitNat bit := by
  cases bit <;> rfl

theorem iterated_addition100_reduces_parity {length : ℕ} (input : Bits length) :
    additionLSB (fun index => (additionEncode100 (input index)).val) =
      Tal.parity input := by
  simpa using iterated_addition_reduces_parity input

/-! ## Pairings of the complete uniform task alphabets -/

/-- The even representative in each odd/even pair of permutations. -/
abbrev EvenS5 := {permutation : S5 // oddUnit (Equiv.Perm.sign permutation) = false}

instance evenS5Nonempty : Nonempty EvenS5 := ⟨⟨1, by simp⟩⟩

@[simp] theorem s5Encode_mul_self (bit : Bool) : s5Encode bit * s5Encode bit = 1 := by
  cases bit <;> simp [s5Encode, Equiv.swap_mul_self]

/-- An explicit bijection pairing every odd permutation with an even one.
Consequently uniform `S₅` symbols have independent uniform parity bits. -/
def s5Pairing : S5 ≃ Bool × EvenS5 where
  toFun permutation :=
    let bit := oddUnit (Equiv.Perm.sign permutation)
    (bit, ⟨s5Encode bit * permutation, by
      rw [Equiv.Perm.sign_mul, oddUnit_mul, sign_s5Encode]
      simp [bit]⟩)
  invFun pair := s5Encode pair.1 * pair.2.val
  left_inv permutation := by
    dsimp only
    rw [← mul_assoc, s5Encode_mul_self, one_mul]
  right_inv pair := by
    rcases pair with ⟨bit, even⟩
    have hsign : oddUnit (Equiv.Perm.sign (s5Encode bit * even.val)) = bit := by
      rw [Equiv.Perm.sign_mul, oddUnit_mul, sign_s5Encode, even.property]
      simp
    apply Prod.ext
    · exact hsign
    · apply Subtype.ext
      dsimp only
      rw [hsign, ← mul_assoc, s5Encode_mul_self, one_mul]

@[simp] theorem s5Pairing_fst (permutation : S5) :
    (s5Pairing permutation).1 = oddUnit (Equiv.Perm.sign permutation) := rfl

theorem evenS5_card : Fintype.card EvenS5 = 60 := by
  have h := Fintype.card_congr s5Pairing
  rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at h
  norm_num at h
  omega

/-- Pair all one hundred addition symbols, with the even representative
indexed by `Fin 50`. -/
def additionPairing100 : Fin 100 ≃ Bool × Fin 50 where
  toFun symbol := (decide (symbol.val % 2 = 1), ⟨symbol.val / 2, by omega⟩)
  invFun pair := ⟨2 * pair.2.val + bitNat pair.1, by
    have h := pair.2.isLt
    cases pair.1 <;> simp [bitNat] <;> omega⟩
  left_inv symbol := by
    apply Fin.ext
    dsimp only
    have hmod : symbol.val % 2 = 0 ∨ symbol.val % 2 = 1 := by omega
    rcases hmod with hmod | hmod <;> simp [hmod, bitNat] <;> omega
  right_inv pair := by
    rcases pair with ⟨bit, representative⟩
    cases bit <;> apply Prod.ext
    all_goals simp [bitNat]
    all_goals apply Fin.ext; simp; omega

@[simp] theorem additionPairing100_fst (symbol : Fin 100) :
    (additionPairing100 symbol).1 = decide (symbol.val % 2 = 1) := rfl

/-- The least significant bit of an arbitrary sum is exactly parity of the
least significant bits of all summands. -/
theorem additionLSB_eq_parity {length : ℕ} (input : Fin length → ℕ) :
    additionLSB input = Tal.parity (fun index => decide (input index % 2 = 1)) := by
  rw [parity_eq_sum_bitNat_mod_two]
  unfold additionLSB
  rw [Finset.sum_nat_mod]
  congr 3
  apply Finset.sum_congr rfl
  intro index _
  have hmod : input index % 2 = 0 ∨ input index % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [hmod, bitNat]

/-! ## End-to-end footprint and length corollaries -/

theorem s5_autoregressive_footprint
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator n traceLength)
    (correct : ∀ input,
      model.answer input =
        s5StateTrackingParity (fun index => s5Encode (input index)))
    (hn : 1 ≤ n) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (Real.sqrt (Tal.tailBound model.explicitFiberDepth
          model.explicitFiberSize n)) ≤
      (model.parityTrace (fun input => by
        rw [correct input, s5_reduces_parity])).uniformMutualInformation := by
  exact model.footprint tal
    (fun input => by rw [correct input, s5_reduces_parity]) hn hsize

theorem iterated_addition_autoregressive_footprint
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator n traceLength)
    (correct : ∀ input,
      model.answer input =
        additionLSB (fun index => (additionEncode100 (input index)).val))
    (hn : 1 ≤ n) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (Real.sqrt (Tal.tailBound model.explicitFiberDepth
          model.explicitFiberSize n)) ≤
      (model.parityTrace (fun input => by
        rw [correct input, iterated_addition100_reduces_parity])).uniformMutualInformation := by
  exact model.footprint tal
    (fun input => by rw [correct input, iterated_addition100_reduces_parity]) hn hsize

theorem s5_autoregressive_binary_length_lower_bound
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator n traceLength)
    (correct : ∀ input,
      model.answer input =
        s5StateTrackingParity (fun index => s5Encode (input index)))
    (hn : 1 ≤ n) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (Real.sqrt (Tal.tailBound model.explicitFiberDepth
          model.explicitFiberSize n)) ≤ traceLength := by
  apply EntropyCoding.autoregressive_binary_length_lower_bound tal model _ hn hsize
  intro input
  rw [correct input, s5_reduces_parity]

theorem iterated_addition_autoregressive_binary_length_lower_bound
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator n traceLength)
    (correct : ∀ input,
      model.answer input =
        additionLSB (fun index => (additionEncode100 (input index)).val))
    (hn : 1 ≤ n) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (Real.sqrt (Tal.tailBound model.explicitFiberDepth
          model.explicitFiberSize n)) ≤ traceLength := by
  apply EntropyCoding.autoregressive_binary_length_lower_bound tal model _ hn hsize
  intro input
  rw [correct input, iterated_addition100_reduces_parity]

end TaskReductions
