import FourierCorrelation

/-!
# Fourier tails under restrictions

Checked foundations for a local proof of Tal's Fourier-tail theorem.
These results do not take `Tal.FourierTailTheorem` as an argument.

We remove a queried coordinate from the Boolean cube, rather than retaining
an unused coordinate. The normalization is therefore the uniform expectation
on the remaining cube. The single-coordinate inequality is Lemma 11 of
Avishay Tal, *Tight Bounds on the Fourier Spectrum of AC0*, CCC 2017.
-/

open scoped BigOperators
noncomputable section

namespace TalRestriction
open TransformerAC0

/-- Restrict coordinate `i` to `value`, and remove it from the input cube. -/
def slice {n : ℕ} (f : Bits (n + 1) → ℝ) (i : Fin (n + 1))
    (value : Bool) : Bits n → ℝ :=
  fun input => f (i.insertNth value input)

/-- Lift a set of remaining coordinates back to the original cube. -/
def liftSet {n : ℕ} (i : Fin (n + 1)) (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.map (Fin.succAboveEmb i)

@[simp] theorem not_mem_liftSet {n : ℕ} (i : Fin (n + 1)) (S : Finset (Fin n)) :
    i ∉ liftSet i S := by
  simp [liftSet, Finset.mem_map, Fin.succAbove_ne]

@[simp] theorem mem_liftSet_succAbove {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin n)) (j : Fin n) : i.succAbove j ∈ liftSet i S ↔ j ∈ S := by
  simp [liftSet]

@[simp] theorem card_liftSet {n : ℕ} (i : Fin (n + 1)) (S : Finset (Fin n)) :
    (liftSet i S).card = S.card := Finset.card_map _

/-- A subset is equivalently its Boolean membership vector. -/
def subsetEquiv (n : ℕ) : Finset (Fin n) ≃ Bits n where
  toFun S i := decide (i ∈ S)
  invFun input := Finset.univ.filter fun i => input i = true
  left_inv S := by ext i; simp
  right_inv input := by funext i; simp

theorem subsetEquiv_insertNth_false {n : ℕ} (i : Fin (n + 1)) (input : Bits n) :
    (subsetEquiv (n + 1)).symm (i.insertNth false input) =
      liftSet i ((subsetEquiv n).symm input) := by
  ext j
  cases j using i.succAboveCases <;> simp [subsetEquiv]

theorem subsetEquiv_insertNth_true {n : ℕ} (i : Fin (n + 1)) (input : Bits n) :
    (subsetEquiv (n + 1)).symm (i.insertNth true input) =
      insert i (liftSet i ((subsetEquiv n).symm input)) := by
  ext j
  cases j using i.succAboveCases <;> simp [subsetEquiv, Fin.succAbove_ne]

/-- Split a sum over all subsets according to whether they contain `i`. -/
theorem sum_subsets_split {n : ℕ} (i : Fin (n + 1))
    (g : Finset (Fin (n + 1)) → ℝ) :
    (∑ S, g S) = (∑ S : Finset (Fin n), g (liftSet i S)) +
      ∑ S : Finset (Fin n), g (insert i (liftSet i S)) := by
  calc
    (∑ S, g S) = ∑ input : Bits (n + 1), g ((subsetEquiv (n + 1)).symm input) :=
      (Equiv.sum_comp (subsetEquiv (n + 1)).symm g).symm
    _ = ∑ pair : Bool × Bits n,
        g ((subsetEquiv (n + 1)).symm (i.insertNth pair.1 pair.2)) :=
      (Equiv.sum_comp (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) i)
        (fun input => g ((subsetEquiv (n + 1)).symm input))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp_rw [subsetEquiv_insertNth_true, subsetEquiv_insertNth_false]
      rw [← Equiv.sum_comp (subsetEquiv n).symm (fun S => g (insert i (liftSet i S))),
        ← Equiv.sum_comp (subsetEquiv n).symm (fun S => g (liftSet i S))]
      exact add_comm _ _

/-- Uniform expectation is the average of its two coordinate restrictions. -/
theorem uniformExpectation_split {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    Tal.uniformExpectation f =
      (Tal.uniformExpectation (slice f i false) +
        Tal.uniformExpectation (slice f i true)) / 2 := by
  have hsum : (∑ input : Bits (n + 1), f input) =
      (∑ input : Bits n, slice f i false input) +
        ∑ input : Bits n, slice f i true input := by
    rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) i) f,
      Fintype.sum_prod_type, Fintype.sum_bool]
    exact add_comm _ _
  unfold Tal.uniformExpectation
  rw [hsum]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_succ]
  ring

@[simp] theorem walsh_liftSet {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin n)) (value : Bool) (input : Bits n) :
    Tal.walshCharacter (liftSet i S) (i.insertNth value input) =
      Tal.walshCharacter S input := by
  simp [Tal.walshCharacter, liftSet, Finset.prod_map]

@[simp] theorem walsh_insert_liftSet {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin n)) (value : Bool) (input : Bits n) :
    Tal.walshCharacter (insert i (liftSet i S)) (i.insertNth value input) =
      Tal.boolSign value * Tal.walshCharacter S input := by
  rw [Tal.walshCharacter, Finset.prod_insert (not_mem_liftSet i S)]
  simp only [Fin.insertNth_apply_same]
  rw [← Tal.walshCharacter, walsh_liftSet]

/-- Coefficients not containing the queried bit are the averages of the slices. -/
theorem coefficient_liftSet {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) (S : Finset (Fin n)) :
    Tal.fourierCoefficient f (liftSet i S) =
      (Tal.fourierCoefficient (slice f i false) S +
        Tal.fourierCoefficient (slice f i true) S) / 2 := by
  unfold Tal.fourierCoefficient
  rw [uniformExpectation_split _ i]
  unfold slice
  simp only [walsh_liftSet]

/-- Coefficients containing the queried bit are the half-differences of the slices. -/
theorem coefficient_insert_liftSet {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) (S : Finset (Fin n)) :
    Tal.fourierCoefficient f (insert i (liftSet i S)) =
      (Tal.fourierCoefficient (slice f i false) S -
        Tal.fourierCoefficient (slice f i true) S) / 2 := by
  unfold Tal.fourierCoefficient
  rw [uniformExpectation_split _ i]
  unfold slice
  simp only [walsh_insert_liftSet, Tal.boolSign_false, Tal.boolSign_true,
    one_mul, neg_one_mul, mul_neg]
  simp [Tal.uniformExpectation, Finset.sum_neg_distrib, neg_div, sub_eq_add_neg]

/-- The two paired coefficient squares obey an exact energy identity. -/
theorem coefficient_energy_split {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) (S : Finset (Fin n)) :
    Tal.fourierCoefficient f (liftSet i S) ^ 2 +
      Tal.fourierCoefficient f (insert i (liftSet i S)) ^ 2 =
        (Tal.fourierCoefficient (slice f i false) S ^ 2 +
          Tal.fourierCoefficient (slice f i true) S ^ 2) / 2 := by
  rw [coefficient_liftSet, coefficient_insert_liftSet]
  ring

/-- Every set containing the queried coordinate is an inserted lifted set. -/
theorem exists_insert_liftSet {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    ∃ T : Finset (Fin n), S = insert i (liftSet i T) := by
  let input := subsetEquiv (n + 1) S
  have hbit : input i = true := by simp [input, subsetEquiv, hi]
  have heq : (subsetEquiv (n + 1)).symm
      (i.insertNth true (Fin.removeNth i input)) = S := by
    rw [← hbit, Fin.insertNth_self_removeNth]
    exact (subsetEquiv (n + 1)).symm_apply_apply S
  rw [subsetEquiv_insertNth_true] at heq
  exact ⟨_, heq.symm⟩

/-- Ignoring a coordinate forces every coefficient containing it to vanish. -/
theorem coefficient_eq_zero_of_slices_eq {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hi : i ∈ S)
    (hindependent : slice f i false = slice f i true) :
    Tal.fourierCoefficient f S = 0 := by
  obtain ⟨T, rfl⟩ := exists_insert_liftSet i S hi
  rw [coefficient_insert_liftSet, hindependent, sub_self, zero_div]

@[simp] theorem uniformExpectation_const (n : ℕ) (value : ℝ) :
    Tal.uniformExpectation (fun _ : Bits n => value) = value := by
  unfold Tal.uniformExpectation
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ value (by positivity : ((2 ^ n : ℕ) : ℝ) ≠ 0)

/-- The only Fourier coefficient of a constant is its constant coefficient. -/
theorem coefficient_const {n : ℕ} (value : ℝ) (S : Finset (Fin n)) :
    Tal.fourierCoefficient (fun _ : Bits n => value) S =
      if S = ∅ then value else 0 := by
  by_cases hS : S = ∅
  · subst S
    simp [Tal.fourierCoefficient, Tal.walshCharacter]
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
        exact coefficient_eq_zero_of_slices_eq (fun _ => value) i S hi rfl

/-- Every positive-degree tail of a constant is zero. -/
@[simp] theorem tailWeight_const {n : ℕ} (value : ℝ) (k : ℕ) :
    Tal.tailWeight (fun _ : Bits n => value) (k + 1) = 0 := by
  unfold Tal.tailWeight
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S = ∅
  · subst S
    simp
  · rw [coefficient_const, if_neg hS]
    simp

/-- Every Fourier tail is nonnegative, including for real-valued functions. -/
theorem tailWeight_nonneg {n : ℕ} (f : Bits n → ℝ) (k : ℕ) :
    0 ≤ Tal.tailWeight f k := by
  apply Finset.sum_nonneg
  intro S _
  split_ifs <;> positivity

/-- Increasing the degree threshold cannot increase the Fourier tail. -/
theorem tailWeight_mono {n : ℕ} (f : Bits n → ℝ) {k l : ℕ} (hkl : k ≤ l) :
    Tal.tailWeight f l ≤ Tal.tailWeight f k := by
  apply Finset.sum_le_sum
  intro S _
  by_cases hl : l ≤ S.card
  · simp only [if_pos hl, if_pos (hkl.trans hl)]
    exact le_rfl
  · simp only [if_neg hl]
    split_ifs <;> positivity

/-- Parseval bounds every Boolean sign tail by one. -/
theorem tailWeight_le_one_of_sign {n : ℕ} (f : Bits n → Bool) (k : ℕ) :
    Tal.tailWeight (fun input => Tal.boolSign (f input)) k ≤ 1 := by
  rw [FourierCorrelation.tailWeight_eq_filter]
  exact FourierCorrelation.restricted_sq_sum_le_one_of_sign f _

/-- Exact spectral effect of fixing one coordinate to a uniform random bit.

For each original coefficient, only the degree of `S \ {i}` remains. This
is the one-coordinate Fourier-weight transfer identity, before any tail
estimate or switching lemma is applied.
-/
theorem average_slice_tailWeight {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) (k : ℕ) :
    (Tal.tailWeight (slice f i false) k + Tal.tailWeight (slice f i true) k) / 2 =
      ∑ S : Finset (Fin (n + 1)),
        if k ≤ (S.erase i).card then Tal.fourierCoefficient f S ^ 2 else 0 := by
  symm
  rw [sum_subsets_split i, ← Finset.sum_add_distrib]
  simp only [Finset.erase_eq_of_not_mem (not_mem_liftSet i _),
    Finset.erase_insert (not_mem_liftSet i _), card_liftSet]
  unfold Tal.tailWeight
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs with h
  · exact coefficient_energy_split f i S
  · norm_num

/-- Exact one-coordinate `p`-random restriction identity.

For `0 ≤ p ≤ 1`, the left side leaves `i` alive with probability `p`, or
fixes it to a uniform bit with probability `1-p`. The identity itself is
algebraic and holds for every real `p`.
-/
theorem random_coordinate_tailWeight {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) (p : ℝ) (k : ℕ) :
    p * Tal.tailWeight f k + (1 - p) *
        ((Tal.tailWeight (slice f i false) k + Tal.tailWeight (slice f i true) k) / 2) =
      ∑ S : Finset (Fin (n + 1)),
        (p * (if k ≤ S.card then 1 else 0) +
          (1 - p) * (if k ≤ (S.erase i).card then 1 else 0)) *
            Tal.fourierCoefficient f S ^ 2 := by
  rw [average_slice_tailWeight]
  unfold Tal.tailWeight
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> ring

/-- Tal's Lemma 11: querying one coordinate costs at most one Fourier degree.

The stronger natural-number form with threshold `k + 1` avoids any ambiguity
at degree zero. No circuit hypothesis or switching lemma is used.
-/
theorem tailWeight_slice {n : ℕ} (f : Bits (n + 1) → ℝ)
    (i : Fin (n + 1)) (k : ℕ) :
    Tal.tailWeight f (k + 1) ≤
      (Tal.tailWeight (slice f i false) k +
        Tal.tailWeight (slice f i true) k) / 2 := by
  unfold Tal.tailWeight
  rw [sum_subsets_split i, ← Finset.sum_add_distrib]
  simp only [card_liftSet, Finset.card_insert_of_not_mem (not_mem_liftSet i _)]
  calc
    _ ≤ ∑ S : Finset (Fin n), if k ≤ S.card then
        Tal.fourierCoefficient f (liftSet i S) ^ 2 +
          Tal.fourierCoefficient f (insert i (liftSet i S)) ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hk : k ≤ S.card
      · have hk' : k + 1 ≤ S.card + 1 := by omega
        simp only [if_pos hk, if_pos hk']
        split_ifs <;> nlinarith [sq_nonneg (Tal.fourierCoefficient f (liftSet i S))]
      · have hk' : ¬k + 1 ≤ S.card + 1 := by omega
        have hk'' : ¬k + 1 ≤ S.card := by omega
        simp only [if_neg hk, if_neg hk', if_neg hk'', zero_add, le_refl]
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs with h
      · exact coefficient_energy_split f i S
      · norm_num

/-- An adaptive restriction tree; each query removes its coordinate.

Leaves do not carry answers. A leaf instead selects the restriction of the
original function obtained along its root-to-leaf path, as in Tal's Definition 12.
-/
inductive RestrictionTree : ℕ → Type
  | leaf {n : ℕ} : RestrictionTree n
  | query {n : ℕ} (coordinate : Fin (n + 1))
      (zero one : RestrictionTree n) : RestrictionTree (n + 1)

namespace RestrictionTree

def depth : {n : ℕ} → RestrictionTree n → ℕ
  | _, .leaf => 0
  | _, .query _ zero one => max (depth zero) (depth one) + 1

/-- Every path ends in a restricted function with the stated Fourier-tail bound. -/
def LeafTailBound : {n : ℕ} → RestrictionTree n → (Bits n → ℝ) → ℕ → ℝ → Prop
  | _, .leaf, f, k, epsilon => Tal.tailWeight f k ≤ epsilon
  | _, .query i zero one, f, k, epsilon =>
      LeafTailBound zero (slice f i false) k epsilon ∧
        LeafTailBound one (slice f i true) k epsilon

/-- Tal's Lemma 13, at the exact depth of the restriction tree. -/
theorem tailWeight_bound {n : ℕ} (tree : RestrictionTree n) (f : Bits n → ℝ)
    (k : ℕ) (epsilon : ℝ) (h : tree.LeafTailBound f k epsilon) :
    Tal.tailWeight f (k + tree.depth) ≤ epsilon := by
  induction tree with
  | leaf => simpa only [depth, Nat.add_zero] using h
  | query i zero one ihzero ihone =>
      obtain ⟨hzero, hone⟩ := h
      have hz := ihzero (slice f i false) hzero
      have ho := ihone (slice f i true) hone
      have hz' := (tailWeight_mono (slice f i false)
        (Nat.add_le_add_left (Nat.le_max_left zero.depth one.depth) k)).trans hz
      have ho' := (tailWeight_mono (slice f i true)
        (Nat.add_le_add_left (Nat.le_max_right zero.depth one.depth) k)).trans ho
      have hs := tailWeight_slice f i (k + max zero.depth one.depth)
      change Tal.tailWeight f (k + (max zero.depth one.depth + 1)) ≤ epsilon
      rw [← Nat.add_assoc]
      linarith

/-- Tal's Lemma 13 for any upper bound on the adaptive query depth. -/
theorem tailWeight_bound_of_depth_le {n : ℕ} (tree : RestrictionTree n)
    (f : Bits n → ℝ) (k D : ℕ) (epsilon : ℝ)
    (hdepth : tree.depth ≤ D) (h : tree.LeafTailBound f k epsilon) :
    Tal.tailWeight f (k + D) ≤ epsilon :=
  (tailWeight_mono f (Nat.add_le_add_left hdepth k)).trans (tree.tailWeight_bound f k epsilon h)

end RestrictionTree

/-- A real-valued decision tree whose queries remove their coordinates. -/
inductive DecisionTree : ℕ → Type
  | leaf {n : ℕ} (value : ℝ) : DecisionTree n
  | query {n : ℕ} (coordinate : Fin (n + 1))
      (zero one : DecisionTree n) : DecisionTree (n + 1)

namespace DecisionTree

def depth : {n : ℕ} → DecisionTree n → ℕ
  | _, .leaf _ => 0
  | _, .query _ zero one => max zero.depth one.depth + 1

def eval : {n : ℕ} → DecisionTree n → Bits n → ℝ
  | _, .leaf value, _ => value
  | _, .query i zero one, input =>
      if input i then one.eval (Fin.removeNth i input) else zero.eval (Fin.removeNth i input)

@[simp] theorem slice_query_false {n : ℕ} (i : Fin (n + 1))
    (zero one : DecisionTree n) : slice (DecisionTree.query i zero one).eval i false = zero.eval := by
  funext input
  simp [slice, eval]

@[simp] theorem slice_query_true {n : ℕ} (i : Fin (n + 1))
    (zero one : DecisionTree n) : slice (DecisionTree.query i zero one).eval i true = one.eval := by
  funext input
  simp [slice, eval]

/-- A depth-`D` decision tree has no Fourier mass above degree `D`. -/
theorem tailWeight_depth_succ {n : ℕ} (tree : DecisionTree n) :
    Tal.tailWeight tree.eval (tree.depth + 1) = 0 := by
  induction tree with
  | leaf value => exact tailWeight_const value 0
  | query i zero one ihzero ihone =>
      have hz : Tal.tailWeight zero.eval (max zero.depth one.depth + 1) ≤ 0 := by
        rw [← ihzero]
        exact tailWeight_mono zero.eval (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
      have ho : Tal.tailWeight one.eval (max zero.depth one.depth + 1) ≤ 0 := by
        rw [← ihone]
        exact tailWeight_mono one.eval (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
      have hs := tailWeight_slice (DecisionTree.query i zero one).eval i (max zero.depth one.depth + 1)
      simp only [slice_query_false, slice_query_true] at hs
      apply le_antisymm _ (tailWeight_nonneg _ _)
      change Tal.tailWeight (DecisionTree.query i zero one).eval (max zero.depth one.depth + 1 + 1) ≤ 0
      linarith

/-- Coefficient-level form of the decision-tree degree bound. -/
theorem coefficient_eq_zero_of_depth_lt {n : ℕ} (tree : DecisionTree n)
    (S : Finset (Fin n)) (hdegree : tree.depth < S.card) :
    Tal.fourierCoefficient tree.eval S = 0 := by
  have h := Tal.coefficient_sq_le_tailWeight tree.eval S (show tree.depth + 1 ≤ S.card by omega)
  rw [tree.tailWeight_depth_succ] at h
  nlinarith [sq_nonneg (Tal.fourierCoefficient tree.eval S)]

end DecisionTree

end TalRestriction
