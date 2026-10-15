import ElementaryMultiplication
import FourierCorrelation
import EntropyCoding

/-!
# End-to-end footprint for the middle bit of multiplication

This file transports the elementary residue-pair Fourier bound to the
standard Boolean cube, combines it with Tal's Fourier-tail theorem, and feeds
the resulting circuit-correlation bound to the generic autoregressive
footprint theorem.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace MultiplicationFootprint

open TransformerAC0

/-- Binary digits, least significant first, of a residue modulo `2^N`. -/
def residueBits (N : ℕ) (value : ZMod (2 ^ N)) : Bits N :=
  fun index => Nat.testBit value.val index.val

theorem residueBits_injective (N : ℕ) : Function.Injective (residueBits N) := by
  intro left right hequal
  apply ZMod.val_injective
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases hindex : index < N
  · exact congrFun hequal ⟨index, hindex⟩
  · have hpow : 2 ^ N ≤ 2 ^ index :=
      Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
    have hleft : left.val < 2 ^ index := (ZMod.val_lt left).trans_le hpow
    have hright : right.val < 2 ^ index := (ZMod.val_lt right).trans_le hpow
    rw [Nat.testBit_eq_false_of_lt hleft, Nat.testBit_eq_false_of_lt hright]

/-- The canonical bijection between residues modulo `2^N` and `N` bits. -/
def residueBitsEquiv (N : ℕ) : ZMod (2 ^ N) ≃ Bits N :=
  Equiv.ofBijective (residueBits N)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      residueBits_injective N, by simp [Bits]⟩)

def splitBits (N : ℕ) : Bits (N + N) ≃ Bits N × Bits N :=
  (Equiv.piCongrLeft (fun _ : Fin (N + N) => Bool) finSumFinEquiv).symm |>.trans
    (Equiv.sumPiEquivProdPi (fun _ => Bool))

/-- Bijection used to reindex Boolean-cube sums as residue-pair sums. -/
def residuePairBitsEquiv (N : ℕ) :
    (ZMod (2 ^ N) × ZMod (2 ^ N)) ≃ Bits (N + N) :=
  (Equiv.prodCongr (residueBitsEquiv N) (residueBitsEquiv N)).trans
    (splitBits N).symm

@[simp] theorem residuePairBitsEquiv_left (N : ℕ)
    (left right : ZMod (2 ^ N)) (index : Fin N) :
    residuePairBitsEquiv N (left, right) (finSumFinEquiv (Sum.inl index)) =
      Nat.testBit left.val index.val := by
  simp [residuePairBitsEquiv, splitBits, residueBitsEquiv, residueBits]

@[simp] theorem residuePairBitsEquiv_right (N : ℕ)
    (left right : ZMod (2 ^ N)) (index : Fin N) :
    residuePairBitsEquiv N (left, right) (finSumFinEquiv (Sum.inr index)) =
      Nat.testBit right.val index.val := by
  simp [residuePairBitsEquiv, splitBits, residueBitsEquiv, residueBits]
  have hsplit : finSumFinEquiv.symm (index.addNat N) = Sum.inr index := by
    apply finSumFinEquiv.injective
    simp
  rw [hsplit]
  rfl

/-- The lower middle product bit on the ordinary `2N`-bit Boolean cube. -/
def middleBitTarget (N : ℕ) (input : Bits (N + N)) : Bool :=
  let pair := (residuePairBitsEquiv N).symm input
  Nat.testBit (pair.1.val * pair.2.val) (N - 1)

@[simp] theorem middleBitTarget_pair (N : ℕ)
    (left right : ZMod (2 ^ N)) :
    middleBitTarget N (residuePairBitsEquiv N (left, right)) =
      Nat.testBit (left.val * right.val) (N - 1) := by
  simp [middleBitTarget]

theorem boolSign_middleBitTarget_pair (N : ℕ) (hN : 1 ≤ N)
    (left right : ZMod (2 ^ N)) :
    Tal.boolSign (middleBitTarget N (residuePairBitsEquiv N (left, right))) =
      ElementaryMultiplication.productSign N left right := by
  rw [middleBitTarget_pair,
    ElementaryMultiplication.productSign_eq_middle_bit N hN]
  cases Nat.testBit (left.val * right.val) (N - 1) <;>
    rfl

/-- Pair two frequency sets into the corresponding subset of the concatenated
Boolean coordinates. -/
def combinedFrequency {N : ℕ} (frequency : ElementaryMultiplication.Frequency N) :
    Finset (Fin (N + N)) :=
  (Finset.sumEquiv.symm frequency).map finSumFinEquiv.toEmbedding

def frequencyEquiv (N : ℕ) :
    ElementaryMultiplication.Frequency N ≃ Finset (Fin (N + N)) :=
  Finset.sumEquiv.toEquiv.symm.trans (Equiv.finsetCongr finSumFinEquiv)

@[simp] theorem frequencyEquiv_apply (N : ℕ)
    (frequency : ElementaryMultiplication.Frequency N) :
    frequencyEquiv N frequency = combinedFrequency frequency := rfl

@[simp] theorem card_combinedFrequency {N : ℕ}
    (frequency : ElementaryMultiplication.Frequency N) :
    (combinedFrequency frequency).card = ElementaryMultiplication.degree frequency := by
  simp [combinedFrequency, ElementaryMultiplication.degree,
    Finset.card_toLeft_add_card_toRight]

theorem walshCharacter_pair (N : ℕ)
    (frequency : ElementaryMultiplication.Frequency N)
    (left right : ZMod (2 ^ N)) :
    ((Tal.walshCharacter (combinedFrequency frequency)
      (residuePairBitsEquiv N (left, right)) : ℝ) : ℂ) =
      ElementaryMultiplication.walsh frequency.1 left *
        ElementaryMultiplication.walsh frequency.2 right := by
  classical
  rw [Tal.walshCharacter, combinedFrequency, Finset.prod_map]
  rw [Finset.sumEquiv_symm_apply, Finset.prod_disj_sum]
  simp only [Equiv.toEmbedding_apply, residuePairBitsEquiv_left,
    residuePairBitsEquiv_right]
  push_cast
  congr 1
  · rw [ElementaryMultiplication.walsh]
    apply Finset.prod_congr rfl
    intro index _
    cases Nat.testBit left.val index.val <;> norm_num [Tal.boolSign]
  · rw [ElementaryMultiplication.walsh]
    apply Finset.prod_congr rfl
    intro index _
    cases Nat.testBit right.val index.val <;> norm_num [Tal.boolSign]

/-- The residue-pair coefficient proved in `ElementaryMultiplication` is
literally the Walsh coefficient of the Boolean-cube target. -/
theorem fourierCoefficient_combined (N : ℕ) (hN : 1 ≤ N)
    (frequency : ElementaryMultiplication.Frequency N) :
    ((Tal.fourierCoefficient
      (fun input => Tal.boolSign (middleBitTarget N input))
      (combinedFrequency frequency) : ℝ) : ℂ) =
        ElementaryMultiplication.fourierCoeff N frequency := by
  classical
  let cubeFunction : Bits (N + N) → ℂ := fun input =>
    ((Tal.boolSign (middleBitTarget N input) *
      Tal.walshCharacter (combinedFrequency frequency) input : ℝ) : ℂ)
  have hreindex :
      (∑ pair : ZMod (2 ^ N) × ZMod (2 ^ N),
          cubeFunction (residuePairBitsEquiv N pair)) =
        ∑ input : Bits (N + N), cubeFunction input :=
    Equiv.sum_comp (residuePairBitsEquiv N) cubeFunction
  have hnumerator :
      (∑ input : Bits (N + N), cubeFunction input) =
        ElementaryMultiplication.multiplicationBilinear N
          (ElementaryMultiplication.walsh frequency.1)
          (ElementaryMultiplication.walsh frequency.2) := by
    rw [← hreindex, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right _
    dsimp [cubeFunction]
    push_cast
    rw [boolSign_middleBitTarget_pair N hN,
      walshCharacter_pair]
    ring
  have hdenominator :
      ((((2 ^ (N + N) : ℕ) : ℝ) : ℂ)) =
        (((2 ^ N : ℕ) : ℂ) ^ 2) := by
    push_cast
    rw [pow_add]
    ring
  have hnumerator' :
      (∑ input : Bits (N + N),
        (Tal.boolSign (middleBitTarget N input) : ℂ) *
          (Tal.walshCharacter (combinedFrequency frequency) input : ℂ)) =
        ElementaryMultiplication.multiplicationBilinear N
          (ElementaryMultiplication.walsh frequency.1)
          (ElementaryMultiplication.walsh frequency.2) := by
    simpa [cubeFunction] using hnumerator
  have hdenominator' :
      (2 : ℂ) ^ (N + N) = (((2 ^ N : ℕ) : ℂ) ^ 2) := by
    norm_num [pow_add, Nat.cast_pow]
    ring
  unfold Tal.fourierCoefficient Tal.uniformExpectation
  push_cast
  rw [hnumerator', hdenominator']
  rfl

theorem fourierCoefficient_sq_combined (N : ℕ) (hN : 1 ≤ N)
    (frequency : ElementaryMultiplication.Frequency N) :
    Tal.fourierCoefficient
        (fun input => Tal.boolSign (middleBitTarget N input))
        (combinedFrequency frequency) ^ 2 =
      Complex.normSq (ElementaryMultiplication.fourierCoeff N frequency) := by
  have hequal := congrArg Complex.normSq
    (fourierCoefficient_combined N hN frequency)
  simpa [Complex.normSq_apply, pow_two] using hequal

/-- Identification of the low-degree mass in the two coordinate systems. -/
theorem lowerWeight_middleBit_eq (N : ℕ) (hN : 1 ≤ N) :
    FourierCorrelation.lowerWeight
        (fun input => Tal.boolSign (middleBitTarget N input)) (N / 8 + 1) =
      ElementaryMultiplication.lowDegreeWeight N (N / 8) := by
  classical
  let summand : Finset (Fin (N + N)) → ℝ := fun set =>
    if set.card < N / 8 + 1 then
      Tal.fourierCoefficient
        (fun input => Tal.boolSign (middleBitTarget N input)) set ^ 2
    else 0
  have hreindex :
      (∑ frequency : ElementaryMultiplication.Frequency N,
          summand (frequencyEquiv N frequency)) =
        ∑ set : Finset (Fin (N + N)), summand set :=
    Equiv.sum_comp (frequencyEquiv N) summand
  rw [FourierCorrelation.lowerWeight, Finset.sum_filter]
  rw [ElementaryMultiplication.lowDegreeWeight, Finset.sum_filter]
  change (∑ set : Finset (Fin (N + N)), summand set) = _
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro frequency _
  dsimp [summand]
  rw [card_combinedFrequency]
  by_cases hdegree : ElementaryMultiplication.degree frequency ≤ N / 8
  · rw [if_pos (by omega), if_pos hdegree]
    exact fourierCoefficient_sq_combined N hN frequency
  · rw [if_neg (by omega), if_neg hdegree]

/-- The explicit correlation rate obtained by combining the elementary
low-degree estimate with Tal's high-degree circuit tail. -/
def correlationRate (N depth size : ℕ) : ℝ :=
  Real.sqrt (9 * (N : ℝ) ^ 2 * (4 / 5 : ℝ) ^ N) +
    Real.sqrt (Tal.tailBound depth size (N / 8 + 1))

theorem middleBit_signCorrelationBound
    (tal : Tal.FourierTailTheorem) (hN : 2 ≤ N) (hsizeTwo : 1 < size) :
    TaskFootprint.SignCorrelationBound (middleBitTarget N) depth size
      (correlationRate N depth size) := by
  intro circuit hdepth hsize
  calc
    |Tal.uniformExpectation (fun input =>
        Tal.boolSign (Circuit.eval circuit input 0) *
          Tal.boolSign (middleBitTarget N input))| ≤
      Real.sqrt (FourierCorrelation.lowerWeight
        (fun input => Tal.boolSign (middleBitTarget N input)) (N / 8 + 1)) +
        Real.sqrt (Tal.tailBound depth size (N / 8 + 1)) :=
      FourierCorrelation.circuit_correlation_le tal (middleBitTarget N)
        circuit depth size (N / 8 + 1) hdepth hsize hsizeTwo
    _ ≤ correlationRate N depth size := by
      unfold correlationRate
      gcongr
      rw [lowerWeight_middleBit_eq N (by omega)]
      exact ElementaryMultiplication.middle_bit_lowDegreeWeight_bound N hN

theorem correlationRate_pos (N depth size : ℕ) :
    0 < correlationRate N depth size := by
  unfold correlationRate
  have htail : 0 < Real.sqrt (Tal.tailBound depth size (N / 8 + 1)) :=
    Real.sqrt_pos.2 (Tal.tailBound_pos depth size (N / 8 + 1))
  positivity

theorem targetBias_eq_fourier_empty (N : ℕ) :
    TaskFootprint.targetBias (middleBitTarget N) =
      Tal.fourierCoefficient
        (fun input => Tal.boolSign (middleBitTarget N input)) ∅ := by
  unfold TaskFootprint.targetBias TaskFootprint.uniformExpectation
    Tal.fourierCoefficient
  congr 1
  funext input
  simp [Tal.walshCharacter]

theorem abs_targetBias_le (N : ℕ) (hN : 2 ≤ N) :
    |TaskFootprint.targetBias (middleBitTarget N)| ≤
      Real.sqrt (9 * (N : ℝ) ^ 2 * (4 / 5 : ℝ) ^ N) := by
  apply Real.abs_le_sqrt
  rw [targetBias_eq_fourier_empty]
  calc
    Tal.fourierCoefficient
        (fun input => Tal.boolSign (middleBitTarget N input)) ∅ ^ 2 ≤
      FourierCorrelation.lowerWeight
        (fun input => Tal.boolSign (middleBitTarget N input)) (N / 8 + 1) := by
          apply FourierCorrelation.coefficient_sq_le_lowerWeight
          simp
    _ = ElementaryMultiplication.lowDegreeWeight N (N / 8) :=
      lowerWeight_middleBit_eq N (by omega)
    _ ≤ 9 * (N : ℝ) ^ 2 * (4 / 5 : ℝ) ^ N :=
      ElementaryMultiplication.middle_bit_lowDegreeWeight_bound N hN

/-- Fully explicit fiber-probability rate, including the target's (small)
bias. -/
def explicitFiberRate (N depth size : ℕ) : ℝ :=
  2 * Real.sqrt (9 * (N : ℝ) ^ 2 * (4 / 5 : ℝ) ^ N) +
    Real.sqrt (Tal.tailBound depth size (N / 8 + 1))

theorem correlationRate_add_bias_le_explicit
    (N depth size : ℕ) (hN : 2 ≤ N) :
    correlationRate N depth size +
        |TaskFootprint.targetBias (middleBitTarget N)| ≤
      explicitFiberRate N depth size := by
  unfold correlationRate explicitFiberRate
  have hbias := abs_targetBias_le N hN
  linarith

theorem explicitFiberRate_pos (N depth size : ℕ) :
    0 < explicitFiberRate N depth size := by
  unfold explicitFiberRate
  have htail : 0 < Real.sqrt (Tal.tailBound depth size (N / 8 + 1)) :=
    Real.sqrt_pos.2 (Tal.tailBound_pos depth size (N / 8 + 1))
  positivity

/-- End-to-end information footprint for an actual autoregressive
matrix-level fixed-precision Transformer computing the middle product bit. -/
theorem autoregressive_footprint
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator (N + N) traceLength)
    (correct : ∀ input, model.answer input = middleBitTarget N input)
    (hN : 2 ≤ N) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (correlationRate N model.explicitFiberDepth model.explicitFiberSize +
          |TaskFootprint.targetBias (middleBitTarget N)|) ≤
      (model.taskTrace (middleBitTarget N) correct).uniformMutualInformation := by
  apply model.task_footprint (middleBitTarget N) correct
    (middleBit_signCorrelationBound tal hN hsize)
  have hrate := correlationRate_pos N model.explicitFiberDepth model.explicitFiberSize
  positivity

/-- The multiplication footprint composed with the unconditional
finite-alphabet entropy bound. -/
theorem autoregressive_binary_length_lower_bound
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator (N + N) traceLength)
    (correct : ∀ input, model.answer input = middleBitTarget N input)
    (hN : 2 ≤ N) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (correlationRate N model.explicitFiberDepth model.explicitFiberSize +
          |TaskFootprint.targetBias (middleBitTarget N)|) ≤ traceLength := by
  apply EntropyCoding.binary_length_at_least_footprint
    ((model.taskTrace (middleBitTarget N) correct).asParityTrace)
  exact autoregressive_footprint tal model correct hN hsize

/-- Paper-style explicit multiplication footprint with no residual bias term. -/
theorem autoregressive_footprint_explicit
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator (N + N) traceLength)
    (correct : ∀ input, model.answer input = middleBitTarget N input)
    (hN : 2 ≤ N) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (explicitFiberRate N model.explicitFiberDepth model.explicitFiberSize) ≤
      (model.taskTrace (middleBitTarget N) correct).uniformMutualInformation := by
  have hraw := autoregressive_footprint tal model correct hN hsize
  have hsmall := correlationRate_add_bias_le_explicit N
    model.explicitFiberDepth model.explicitFiberSize hN
  have hleft : 0 < correlationRate N model.explicitFiberDepth model.explicitFiberSize +
      |TaskFootprint.targetBias (middleBitTarget N)| := by
    have := correlationRate_pos N model.explicitFiberDepth model.explicitFiberSize
    positivity
  have hright := explicitFiberRate_pos N
    model.explicitFiberDepth model.explicitFiberSize
  have hlog :
      Real.logb 2
          (correlationRate N model.explicitFiberDepth model.explicitFiberSize +
            |TaskFootprint.targetBias (middleBitTarget N)|) ≤
        Real.logb 2
          (explicitFiberRate N model.explicitFiberDepth model.explicitFiberSize) :=
    (Real.logb_le_logb (by norm_num) hleft hright).2 hsmall
  linarith

theorem autoregressive_binary_length_lower_bound_explicit
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator (N + N) traceLength)
    (correct : ∀ input, model.answer input = middleBitTarget N input)
    (hN : 2 ≤ N) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (explicitFiberRate N model.explicitFiberDepth model.explicitFiberSize) ≤
      traceLength := by
  apply EntropyCoding.binary_length_at_least_footprint
    ((model.taskTrace (middleBitTarget N) correct).asParityTrace)
  exact autoregressive_footprint_explicit tal model correct hN hsize

end MultiplicationFootprint
