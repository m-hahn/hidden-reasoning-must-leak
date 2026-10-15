import Footprint
import FiniteInformation

/-!
# Leakage without recovery of any individual bit

The trace below reveals one parity for every adjacent input pair.  It
therefore reveals `pairs` independent bits, while every individual input bit
remains exactly fair even to an arbitrary (unbounded) predictor that sees the
entire trace.  This is the finite, quantitative core of the FAQ proposition.
-/

open scoped BigOperators

noncomputable section

namespace LocalUnrecoverability

open TransformerAC0

/-- The visible trace consists of the XOR of each adjacent pair. -/
def pairedTrace (pairs : ℕ) (input : Bits (pairs * 2)) : Bits pairs :=
  fun pair => Bool.xor
    (input (finProdFinEquiv (pair, (0 : Fin 2))))
    (input (finProdFinEquiv (pair, (1 : Fin 2))))

/-- Flip both members of one pair. -/
def flipPair (pair : Fin pairs) (input : Bits (pairs * 2)) : Bits (pairs * 2) :=
  fun index =>
    if (finProdFinEquiv.symm index).1 = pair then !(input index) else input index

@[simp] theorem flipPair_involutive (pair : Fin pairs) (input : Bits (pairs * 2)) :
    flipPair pair (flipPair pair input) = input := by
  funext index
  by_cases h : (finProdFinEquiv.symm index).1 = pair
  · change index.divNat = pair at h
    simp [flipPair, h]
  · change ¬index.divNat = pair at h
    simp [flipPair, h]

def flipPairEquiv (pair : Fin pairs) : Bits (pairs * 2) ≃ Bits (pairs * 2) where
  toFun := flipPair pair
  invFun := flipPair pair
  left_inv := flipPair_involutive pair
  right_inv := flipPair_involutive pair

@[simp] theorem pairedTrace_flipPair (pair : Fin pairs) (input : Bits (pairs * 2)) :
    pairedTrace pairs (flipPair pair input) = pairedTrace pairs input := by
  funext current
  by_cases h : current = pair
  · subst current
    simp [pairedTrace, flipPair]
  · simp [pairedTrace, flipPair, h]

@[simp] theorem flipPair_own_bit (input : Bits (pairs * 2))
    (bit : Fin (pairs * 2)) :
    flipPair (finProdFinEquiv.symm bit).1 input bit = !(input bit) := by
  simp [flipPair]

/-- Uniform success probability of a predictor for one designated input bit. -/
def predictionSuccess (predictor : Bits pairs → Bool)
    (bit : Fin (pairs * 2)) : ℝ :=
  Tal.uniformExpectation fun input : Bits (pairs * 2) =>
    Footprint.boolIndicator (decide (predictor (pairedTrace pairs input) = input bit))

private theorem paired_success_complement
    (predictor : Bits pairs → Bool) (bit : Fin (pairs * 2))
    (input : Bits (pairs * 2)) :
    Footprint.boolIndicator
          (decide (predictor (pairedTrace pairs input) = input bit)) +
        Footprint.boolIndicator
          (decide (predictor
            (pairedTrace pairs
              (flipPair (finProdFinEquiv.symm bit).1 input)) =
                flipPair (finProdFinEquiv.symm bit).1 input bit)) = 1 := by
  rw [pairedTrace_flipPair, flipPair_own_bit]
  cases predictor (pairedTrace pairs input) <;> cases input bit <;>
    simp [Footprint.boolIndicator]

/-- No observer of the complete paired trace predicts any individual input
bit with success different from chance.  The predictor is unrestricted. -/
theorem no_individual_bit_recoverable
    (predictor : Bits pairs → Bool) (bit : Fin (pairs * 2)) :
    predictionSuccess predictor bit = 1 / 2 := by
  let pair := (finProdFinEquiv.symm bit).1
  let score : Bits (pairs * 2) → ℝ := fun input =>
    Footprint.boolIndicator
      (decide (predictor (pairedTrace pairs input) = input bit))
  have hreindex :
      (∑ input : Bits (pairs * 2), score input) =
        ∑ input : Bits (pairs * 2), score (flipPair pair input) := by
    simpa [flipPairEquiv] using
      (Equiv.sum_comp (flipPairEquiv pair) score).symm
  have hpair : ∀ input : Bits (pairs * 2),
      score input + score (flipPair pair input) = 1 := by
    intro input
    exact paired_success_complement predictor bit input
  have hdouble :
      2 * (∑ input : Bits (pairs * 2), score input) =
        ((2 ^ (pairs * 2) : ℕ) : ℝ) := by
    calc
      2 * (∑ input : Bits (pairs * 2), score input) =
          (∑ input : Bits (pairs * 2), score input) +
            ∑ input : Bits (pairs * 2), score input := by ring
      _ = (∑ input : Bits (pairs * 2), score input) +
            ∑ input : Bits (pairs * 2), score (flipPair pair input) := by rw [← hreindex]
      _ = ∑ input : Bits (pairs * 2),
            (score input + score (flipPair pair input)) :=
          Finset.sum_add_distrib.symm
      _ = ∑ _input : Bits (pairs * 2), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro input _
          exact hpair input
      _ = ((2 ^ (pairs * 2) : ℕ) : ℝ) := by
          simp [Bits]
  unfold predictionSuccess Tal.uniformExpectation
  change (∑ input : Bits (pairs * 2), score input) /
      ((2 ^ (pairs * 2) : ℕ) : ℝ) = 1 / 2
  have hden : (0 : ℝ) < (2 ^ (pairs * 2) : ℕ) := by positivity
  apply (div_eq_iff hden.ne').2
  nlinarith [hdouble]

/-! ## The general complement-pair construction -/

def complement (input : Bits n) : Bits n := fun bit => !(input bit)

@[simp] theorem complement_involutive (input : Bits n) :
    complement (complement input) = input := by
  funext bit
  simp [complement]

def complementEquiv (n : ℕ) : Bits n ≃ Bits n where
  toFun := complement
  invFun := complement
  left_inv := complement_involutive
  right_inv := complement_involutive

@[simp] theorem complement_bit (input : Bits n) (bit : Fin n) :
    complement input bit = !(input bit) := rfl

/-- Any visible trace invariant under global bit complementation leaves every
individual coordinate exactly unpredictable under the uniform input. -/
theorem invariant_under_complement_no_bit_recoverable
    {Trace : Type*} (trace : Bits n → Trace)
    (invariant : ∀ input, trace (complement input) = trace input)
    (predictor : Trace → Bool) (bit : Fin n) :
    Tal.uniformExpectation (fun input : Bits n =>
      Footprint.boolIndicator (decide (predictor (trace input) = input bit))) =
        1 / 2 := by
  let score : Bits n → ℝ := fun input =>
    Footprint.boolIndicator (decide (predictor (trace input) = input bit))
  have hcomplement : ∀ input : Bits n,
      score input + score (complement input) = 1 := by
    intro input
    dsimp [score]
    rw [invariant]
    cases predictor (trace input) <;> cases input bit <;>
      simp [Footprint.boolIndicator]
  have hreindex :
      (∑ input : Bits n, score input) =
        ∑ input : Bits n, score (complement input) := by
    simpa [complementEquiv] using
      (Equiv.sum_comp (complementEquiv n) score).symm
  have hdouble :
      2 * (∑ input : Bits n, score input) = ((2 ^ n : ℕ) : ℝ) := by
    calc
      2 * (∑ input : Bits n, score input) =
          (∑ input : Bits n, score input) + ∑ input : Bits n, score input := by ring
      _ = (∑ input : Bits n, score input) +
          ∑ input : Bits n, score (complement input) := by rw [← hreindex]
      _ = ∑ input : Bits n, (score input + score (complement input)) :=
          Finset.sum_add_distrib.symm
      _ = ∑ _input : Bits n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro input _
          exact hcomplement input
      _ = ((2 ^ n : ℕ) : ℝ) := by simp [Bits]
  unfold Tal.uniformExpectation
  change (∑ input : Bits n, score input) / ((2 ^ n : ℕ) : ℝ) = 1 / 2
  have hden : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  apply (div_eq_iff hden.ne').2
  nlinarith [hdouble]

/-- For an arbitrary function, publish both computations on `input` and its
complement, ordering the pair by one pivot bit.  Complementing the input does
not change this visible trace. -/
def symmetricTrace (pivot : Fin n) (function : Bits n → Output)
    (input : Bits n) : Output × Output :=
  if input pivot then
    (function (complement input), function input)
  else
    (function input, function (complement input))

@[simp] theorem symmetricTrace_complement (pivot : Fin n)
    (function : Bits n → Output) (input : Bits n) :
    symmetricTrace pivot function (complement input) =
      symmetricTrace pivot function input := by
  cases h : input pivot <;>
    simp [symmetricTrace, complement, h, complement_involutive]

/-- The FAQ's general construction: for every function on a fixed nonempty
Boolean cube, its complement-paired trace defeats every individual-bit
predictor exactly, without any computational restriction on the predictor. -/
theorem symmetricTrace_no_individual_bit_recoverable
    (pivot : Fin n) (function : Bits n → Output)
    (predictor : Output × Output → Bool) (bit : Fin n) :
    Tal.uniformExpectation (fun input : Bits n =>
      Footprint.boolIndicator
        (decide (predictor (symmetricTrace pivot function input) = input bit))) =
      1 / 2 :=
  invariant_under_complement_no_bit_recoverable
    (symmetricTrace pivot function)
    (symmetricTrace_complement pivot function) predictor bit

/-! ## Exact information content of the constructions -/

open FiniteInformation

/-- Split each pair into its first bit and its XOR.  This is a bijection, so
all pair parities are independent fair bits under the uniform input. -/
def pairedInputEquiv (pairs : ℕ) : Bits (pairs * 2) ≃ (Bits pairs × Bits pairs) where
  toFun input :=
    (fun pair => input (finProdFinEquiv (pair, (0 : Fin 2))), pairedTrace pairs input)
  invFun value := fun index =>
    let location := finProdFinEquiv.symm index
    if location.2 = 0 then value.1 location.1
    else Bool.xor (value.1 location.1) (value.2 location.1)
  left_inv input := by
    funext index
    obtain ⟨location, hlocation⟩ := finProdFinEquiv.surjective index
    rcases location with ⟨pair, bit⟩
    rw [← hlocation]
    fin_cases bit
    · simp
    · simp [pairedTrace]
  right_inv value := by
    apply Prod.ext
    · funext pair
      simp
    · funext pair
      simp [pairedTrace]

theorem pairedTrace_uniform_probability (candidate : Bits pairs) :
    (Distribution.uniform (Bits (pairs * 2))).pushMass (pairedTrace pairs) candidate =
      1 / (2 ^ pairs : ℕ) := by
  have h := Distribution.uniform_pushMass_equiv (pairedInputEquiv pairs) Prod.snd candidate
  rw [Distribution.uniform_product_pushMass_snd] at h
  simpa [pairedInputEquiv, Bits] using h

theorem pairedTrace_information :
    (Distribution.uniform (Bits (pairs * 2))).mutualInformation id (pairedTrace pairs) =
      (pairs : ℝ) := by
  rw [Distribution.mutualInformation_id_eq_entropy]
  have huniform : ∀ candidate,
      (Distribution.uniform (Bits (pairs * 2))).pushMass (pairedTrace pairs) candidate =
        1 / (Fintype.card (Bits pairs) : ℝ) := by
    intro candidate
    simpa [Bits] using pairedTrace_uniform_probability candidate
  rw [Distribution.entropy_of_uniform_pushMass _ _ huniform]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
  rw [Real.logb, Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp

/-- The complement orbit is identified by all tail bits XOR the pivot. -/
def normalizedTail (input : Bits (n + 1)) : Bits n :=
  fun index => Bool.xor (input index.succ) (input 0)

@[simp] theorem normalizedTail_complement (input : Bits (n + 1)) :
    normalizedTail (complement input) = normalizedTail input := by
  funext index
  simp only [normalizedTail, complement]
  cases input index.succ <;> cases input 0 <;> rfl

/-- Retaining the pivot as well as the normalized tail is a bijection. -/
def normalizedInputEquiv (n : ℕ) : Bits (n + 1) ≃ (Bool × Bits n) where
  toFun input := (input 0, normalizedTail input)
  invFun value := Fin.cons value.1 (fun index => Bool.xor (value.2 index) value.1)
  left_inv input := by
    funext index
    refine Fin.cases ?_ (fun tail => ?_) index
    · simp
    · simp [normalizedTail]
  right_inv value := by
    apply Prod.ext
    · simp
    · funext index
      simp [normalizedTail]

theorem normalizedTail_information :
    (Distribution.uniform (Bits (n + 1))).mutualInformation id normalizedTail = (n : ℝ) := by
  rw [Distribution.mutualInformation_id_eq_entropy]
  have h := Distribution.uniform_entropy_equiv (normalizedInputEquiv n) Prod.snd
  change (Distribution.uniform (Bits (n + 1))).entropy normalizedTail = _ at h
  rw [h, Distribution.entropy_of_uniform_pushMass _ _
    Distribution.uniform_product_pushMass_snd]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
  rw [Real.logb, Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp

/-- The FAQ's complete visible object includes the complement-orbit identifier
and both canonically ordered computations. -/
def canonicalSymmetricTrace (function : Bits (n + 1) → Output)
    (input : Bits (n + 1)) : Bits n × (Output × Output) :=
  (normalizedTail input, symmetricTrace 0 function input)

@[simp] theorem canonicalSymmetricTrace_complement
    (function : Bits (n + 1) → Output) (input : Bits (n + 1)) :
    canonicalSymmetricTrace function (complement input) = canonicalSymmetricTrace function input := by
  simp [canonicalSymmetricTrace]

theorem canonicalSymmetricTrace_no_bit_recoverable
    (function : Bits (n + 1) → Output)
    (predictor : Bits n × (Output × Output) → Bool) (bit : Fin (n + 1)) :
    Tal.uniformExpectation (fun input : Bits (n + 1) =>
      Footprint.boolIndicator
        (decide (predictor (canonicalSymmetricTrace function input) = input bit))) = 1 / 2 :=
  invariant_under_complement_no_bit_recoverable (canonicalSymmetricTrace function)
    (canonicalSymmetricTrace_complement function) predictor bit

theorem canonicalSymmetricTrace_information
    [Fintype Output] [DecidableEq Output] (function : Bits (n + 1) → Output) :
    (Distribution.uniform (Bits (n + 1))).mutualInformation id
      (canonicalSymmetricTrace function) = (n : ℝ) := by
  rw [Distribution.mutualInformation_id_eq_entropy]
  let D := Distribution.uniform (Bits (n + 1))
  have hcanonical : ∀ input : Bits (n + 1),
      symmetricTrace 0 function input =
        (function (Fin.cons false (normalizedTail input)),
          function (complement (Fin.cons false (normalizedTail input)))) := by
    intro input
    cases hbit : input 0
    · have hinput : Fin.cons false (normalizedTail input) = input := by
        funext index
        refine Fin.cases ?_ (fun tail => ?_) index <;> simp [normalizedTail, hbit]
      simp [symmetricTrace, hbit, hinput]
    · have hinput : Fin.cons false (normalizedTail input) = complement input := by
        funext index
        refine Fin.cases ?_ (fun tail => ?_) index <;>
          simp [normalizedTail, complement, hbit]
      simp [symmetricTrace, hbit, hinput]
  have heq : D.entropy (canonicalSymmetricTrace function) = D.entropy normalizedTail := by
    apply D.entropy_eq_of_comp (canonicalSymmetricTrace function) normalizedTail
      (fun tail => (tail, (function (Fin.cons false tail),
        function (complement (Fin.cons false tail)))))
      (fun input => by simp [canonicalSymmetricTrace, hcanonical input])
      Prod.fst (fun _ => rfl)
  rw [heq]
  simpa [Distribution.mutualInformation_id_eq_entropy] using (normalizedTail_information (n := n))

/-- The private readout recovers the requested answer by choosing the member
of the public pair specified by the private pivot. -/
theorem canonicalSymmetricTrace_output
    (function : Bits (n + 1) → Output) (input : Bits (n + 1)) :
    (if input 0 then (canonicalSymmetricTrace function input).2.2
      else (canonicalSymmetricTrace function input).2.1) = function input := by
  cases h : input 0 <;> simp [canonicalSymmetricTrace, symmetricTrace, h]

end LocalUnrecoverability
