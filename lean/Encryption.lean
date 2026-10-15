import HiddenReasoningTax
import Mathlib.Data.Fin.Tuple.Take

/-!
# Encrypted chains of thought

This file formalizes the encryption theorems from the paper appendix.  The
formalization separates the conjectural cryptographic premise from the proved
reductions:

1. `LocalGenerator` expresses the `NC⁰` locality condition, and
   `NC0GeneratorFamily.IsPseudorandom` states security against nonuniform
   polynomial-size circuit families with negligible advantage.
2. `goldreichPredicate` and `goldreichGenerator` formalize the five-local
   Goldreich candidate used by the experiments.
3. `secure_prefix` proves that full-output PRG security passes to the exact
   prefix used by a trace.  This makes explicit the prefix reduction that is
   only implicit (and mistyped once) in the appendix.
4. XOR with a fixed plaintext is a permutation of the Boolean cube, so PRG
   security passes to every encrypted trace.
5. `prediction_le_prior` converts pointwise trace indistinguishability into
   the paper's arbitrary-distribution, arbitrary-predicate guarantee.
6. `randomness_cannot_erase_footprint` proves the complementary information
   bound `I(input; trace) ≥ fixed-seed footprint - seedLength`.

The final theorems in this module are the cryptographic and information-
theoretic cores used by the end-to-end constructions in
`ObliviousSimulation.lean`.  Runtime-dependent trace-length estimates and the
one-layer oblivious-machine construction live there; the parameter `suffix`
is the exact witness that the PRG output is long enough to cover the trace.
-/

open scoped BigOperators

noncomputable section

namespace Encryption

open TransformerAC0

def indicator (b : Bool) : ℝ := if b then 1 else 0

def uniformAcceptance {n : ℕ} (monitor : Bits n → Bool) : ℝ :=
  (∑ x, indicator (monitor x)) / (2 ^ n : ℕ)

def bitXor {n : ℕ} (x y : Bits n) : Bits n := fun i => Bool.xor (x i) (y i)

@[simp] theorem bitXor_self {n : ℕ} (x : Bits n) : bitXor x x = fun _ => false := by
  funext i
  simp [bitXor]

@[simp] theorem bitXor_left_involutive {n : ℕ} (x y : Bits n) :
    bitXor x (bitXor x y) = y := by
  funext i
  simp [bitXor, Bool.xor_assoc]

@[simp] theorem bitXor_right_involutive {n : ℕ} (x y : Bits n) :
    bitXor (bitXor x y) y = x := by
  funext i
  change Bool.xor (Bool.xor (x i) (y i)) (y i) = x i
  cases x i <;> cases y i <;> rfl

def xorEquiv {n : ℕ} (x : Bits n) : Bits n ≃ Bits n where
  toFun := bitXor x
  invFun := bitXor x
  left_inv := bitXor_left_involutive x
  right_inv := bitXor_left_involutive x

theorem uniformAcceptance_xor {n : ℕ} (monitor : Bits n → Bool) (x : Bits n) :
    uniformAcceptance (fun pad => monitor (bitXor x pad)) =
      uniformAcceptance monitor := by
  unfold uniformAcceptance
  congr 1
  exact Equiv.sum_comp (xorEquiv x) (fun y => indicator (monitor y))

def splitBits (front suffix : ℕ) :
    Bits (front + suffix) ≃ Bits front × Bits suffix :=
  (Equiv.piCongrLeft (fun _ : Fin (front + suffix) => Bool) finSumFinEquiv).symm |>.trans
    (Equiv.sumPiEquivProdPi (fun _ => Bool))

@[simp] theorem splitBits_fst (front suffix : ℕ) (x : Bits (front + suffix)) :
    (splitBits front suffix x).1 = Fin.take front (Nat.le_add_right front suffix) x := by
  funext i
  simp [splitBits, Fin.take]
  apply congrArg x
  rfl

theorem uniformAcceptance_take (front suffix : ℕ) (monitor : Bits front → Bool) :
    uniformAcceptance
        (fun x : Bits (front + suffix) =>
          monitor (Fin.take front (Nat.le_add_right front suffix) x)) =
      uniformAcceptance monitor := by
  unfold uniformAcceptance
  have hsum :
      (∑ x : Bits (front + suffix),
          indicator (monitor (Fin.take front (Nat.le_add_right front suffix) x))) =
        (∑ y : Bits front, indicator (monitor y)) * (2 ^ suffix : ℕ) := by
    calc
      (∑ x : Bits (front + suffix),
          indicator (monitor (Fin.take front (Nat.le_add_right front suffix) x))) =
          ∑ p : Bits front × Bits suffix, indicator (monitor p.1) := by
            rw [← Equiv.sum_comp (splitBits front suffix)]
            apply Finset.sum_congr rfl
            intro x _
            rw [splitBits_fst]
      _ = ∑ y : Bits front, ∑ _z : Bits suffix, indicator (monitor y) := by
            rw [Fintype.sum_prod_type]
      _ = (∑ y : Bits front, indicator (monitor y)) * (2 ^ suffix : ℕ) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
              Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            rw [← Finset.mul_sum]
            ring
  rw [hsum]
  push_cast
  rw [pow_add]
  have hs : (0 : ℝ) < 2 ^ suffix := by positivity
  field_simp
  ring

/-! security interfaces -/

abbrev Monitor (n : ℕ) := Bits n → Bool
abbrev MonitorClass (n : ℕ) := Set (Monitor n)

def samplerAcceptance {seedLength outputLength : ℕ}
    (sampler : Bits seedLength → Bits outputLength) (monitor : Monitor outputLength) : ℝ :=
  uniformAcceptance (fun seed => monitor (sampler seed))

def distinguishingAdvantage {seedLength outputLength : ℕ}
    (sampler : Bits seedLength → Bits outputLength) (monitor : Monitor outputLength) : ℝ :=
  |samplerAcceptance sampler monitor - uniformAcceptance monitor|

def SecureAgainst {seedLength outputLength : ℕ}
    (sampler : Bits seedLength → Bits outputLength)
    (monitors : MonitorClass outputLength) (ε : ℝ) : Prop :=
  ∀ monitor, monitor ∈ monitors → distinguishingAdvantage sampler monitor ≤ ε

def prefixGenerator {seedLength front suffix : ℕ}
    (generator : Bits seedLength → Bits (front + suffix)) : Bits seedLength → Bits front :=
  fun seed => Fin.take front (Nat.le_add_right front suffix) (generator seed)

def PrefixClosed {front suffix : ℕ}
    (fullMonitors : MonitorClass (front + suffix))
    (frontMonitors : MonitorClass front) : Prop :=
  ∀ monitor ∈ frontMonitors,
    (fun output => monitor (Fin.take front (Nat.le_add_right front suffix) output)) ∈
      fullMonitors

theorem secure_prefix
    {seedLength front suffix : ℕ}
    (generator : Bits seedLength → Bits (front + suffix))
    (fullMonitors : MonitorClass (front + suffix))
    (frontMonitors : MonitorClass front) (ε : ℝ)
    (secure : SecureAgainst generator fullMonitors ε)
    (closed : PrefixClosed fullMonitors frontMonitors) :
    SecureAgainst (prefixGenerator generator) frontMonitors ε := by
  intro monitor hmonitor
  have h := secure
    (fun output => monitor (Fin.take front (Nat.le_add_right front suffix) output))
    (closed monitor hmonitor)
  unfold distinguishingAdvantage samplerAcceptance at h ⊢
  rw [uniformAcceptance_take] at h
  simpa [prefixGenerator] using h

def xorShift {n : ℕ} (message : Bits n) (monitor : Monitor n) : Monitor n :=
  fun pad => monitor (bitXor message pad)

def XorClosed {n : ℕ} (monitors : MonitorClass n) : Prop :=
  ∀ monitor ∈ monitors, ∀ message, xorShift message monitor ∈ monitors

def encryptedTrace {α : Type*} {seedLength traceLength : ℕ}
    (plainTrace : α → Bits traceLength) (generator : Bits seedLength → Bits traceLength) :
    α → Bits seedLength → Bits traceLength :=
  fun input seed => bitXor (plainTrace input) (generator seed)

/-- The same pad decrypts the XOR-encrypted trace exactly. -/
@[simp] theorem decrypt_encryptedTrace
    {α : Type*} {seedLength traceLength : ℕ}
    (plainTrace : α → Bits traceLength) (generator : Bits seedLength → Bits traceLength)
    (input : α) (seed : Bits seedLength) :
    bitXor (encryptedTrace plainTrace generator input seed) (generator seed) =
      plainTrace input := by
  exact bitXor_right_involutive _ _

theorem encryptedTrace_pointwise_secure
    {α : Type*} {seedLength traceLength : ℕ}
    (plainTrace : α → Bits traceLength) (generator : Bits seedLength → Bits traceLength)
    (monitors : MonitorClass traceLength) (ε : ℝ)
    (secure : SecureAgainst generator monitors ε) (closed : XorClosed monitors)
    (input : α) (monitor : Monitor traceLength) (hmonitor : monitor ∈ monitors) :
    distinguishingAdvantage (encryptedTrace plainTrace generator input) monitor ≤ ε := by
  have h := secure (xorShift (plainTrace input) monitor)
    (closed monitor hmonitor (plainTrace input))
  unfold distinguishingAdvantage samplerAcceptance xorShift at h
  rw [uniformAcceptance_xor] at h
  simpa [distinguishingAdvantage, samplerAcceptance, encryptedTrace] using h

structure LocalGenerator (seedLength outputLength locality : ℕ) where
  generate : Bits seedLength → Bits outputLength
  dependency : Fin outputLength → Fin locality → Fin seedLength
  locality_correct : ∀ output seed₁ seed₂,
    (∀ j, seed₁ (dependency output j) = seed₂ (dependency output j)) →
      generate seed₁ output = generate seed₂ output

namespace LocalGenerator

def take {seedLength front suffix locality : ℕ}
    (G : LocalGenerator seedLength (front + suffix) locality) :
    LocalGenerator seedLength front locality where
  generate := prefixGenerator G.generate
  dependency := fun output => G.dependency (Fin.castLE (Nat.le_add_right front suffix) output)
  locality_correct := by
    intro output seed₁ seed₂ hagree
    exact G.locality_correct
      (Fin.castLE (Nat.le_add_right front suffix) output) seed₁ seed₂ hagree

end LocalGenerator

def goldreichPredicate (input : Bits 5) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (input 0) (input 1)) (input 2))
    (input 3 && input 4)

def goldreichGenerator {seedLength outputLength : ℕ}
    (neighborhood : Fin outputLength → Fin 5 → Fin seedLength) :
    LocalGenerator seedLength outputLength 5 where
  generate := fun seed output => goldreichPredicate (fun j => seed (neighborhood output j))
  dependency := neighborhood
  locality_correct := by
    intro output seed₁ seed₂ hagree
    unfold goldreichPredicate
    simp_rw [hagree]

/-- The appendix samples ordered neighborhoods with five distinct vertices. -/
def DistinctNeighborhoods {seedLength outputLength : ℕ}
    (neighborhood : Fin outputLength → Fin 5 → Fin seedLength) : Prop :=
  ∀ output, Function.Injective (neighborhood output)

theorem goldreichGenerator_is_five_local {seedLength outputLength : ℕ}
    (neighborhood : Fin outputLength → Fin 5 → Fin seedLength)
    (output : Fin outputLength) (seed₁ seed₂ : Bits seedLength)
    (hagree : ∀ j, seed₁ (neighborhood output j) = seed₂ (neighborhood output j)) :
    (goldreichGenerator neighborhood).generate seed₁ output =
      (goldreichGenerator neighborhood).generate seed₂ output :=
  (goldreichGenerator neighborhood).locality_correct output seed₁ seed₂ hagree

/-! Asymptotic circuit-family formulation of the PRG assumption. -/

def Negligible (error : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ error n) ∧
    ∀ exponent : ℕ, ∃ cutoff : ℕ, ∀ n, cutoff ≤ n →
      error n ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ exponent

structure PolynomialMonitorFamily (inputLength : ℕ → ℕ) where
  circuit : ∀ n, Circuit (inputLength n) 1
  coefficient : ℕ
  exponent : ℕ
  size_le : ∀ n,
    Circuit.gateCount (circuit n) ≤ coefficient * (n + 1) ^ exponent

namespace PolynomialMonitorFamily

def monitor {inputLength : ℕ → ℕ} (family : PolynomialMonitorFamily inputLength)
    (n : ℕ) : Monitor (inputLength n) :=
  fun input => Circuit.eval (family.circuit n) input 0

end PolynomialMonitorFamily

structure NC0GeneratorFamily (seedLength outputLength : ℕ → ℕ) where
  locality : ℕ
  generator : ∀ n, LocalGenerator (seedLength n) (outputLength n) locality

namespace NC0GeneratorFamily

/-- Security against nonuniform polynomial-size circuit families. -/
def IsPseudorandom {seedLength outputLength : ℕ → ℕ}
    (family : NC0GeneratorFamily seedLength outputLength) : Prop :=
  ∀ monitor : PolynomialMonitorFamily outputLength,
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n,
      distinguishingAdvantage (family.generator n).generate (monitor.monitor n) ≤ error n

/-- The output length is the prescribed stretch of the seed length. -/
def HasStretch {seedLength outputLength : ℕ → ℕ}
    (_family : NC0GeneratorFamily seedLength outputLength) (stretch : ℕ → ℕ) : Prop :=
  ∀ n, outputLength n = stretch (seedLength n)

end NC0GeneratorFamily

/-! Information leakage with private randomness. -/

def uniformRealExpectation {n : ℕ} (f : Bits n → ℝ) : ℝ :=
  (∑ x, f x) / (2 ^ n : ℕ)

theorem le_uniformRealExpectation {n : ℕ} (f : Bits n → ℝ) (lower : ℝ)
    (h : ∀ x, lower ≤ f x) : lower ≤ uniformRealExpectation f := by
  unfold uniformRealExpectation
  have hden : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  apply (le_div_iff₀ hden).2
  calc
    lower * (2 ^ n : ℕ) = ∑ _x : Bits n, lower := by
      simp [Fintype.card_fun]
      ring
    _ ≤ ∑ x : Bits n, f x := Finset.sum_le_sum fun x _ => h x

structure PrivateRandomnessProfile (seedLength : ℕ) where
  traceMutualInformation : ℝ
  conditionalTraceMutualInformation : ℝ
  conditionalInputSeedMutualInformation : ℝ
  seedEntropy : ℝ
  fixedSeedInformation : Bits seedLength → ℝ
  conditional_eq_average :
    conditionalTraceMutualInformation = uniformRealExpectation fixedSeedInformation
  independent_chain_rule :
    conditionalTraceMutualInformation =
      traceMutualInformation + conditionalInputSeedMutualInformation
  conditionalInputSeed_le_entropy :
    conditionalInputSeedMutualInformation ≤ seedEntropy
  seedEntropy_le_bits : seedEntropy ≤ seedLength

theorem randomness_cannot_erase_footprint
    {seedLength : ℕ} (profile : PrivateRandomnessProfile seedLength)
    (footprintLower : ℝ)
    (fixedSeedFootprint : ∀ seed, footprintLower ≤ profile.fixedSeedInformation seed) :
    footprintLower - seedLength ≤ profile.traceMutualInformation := by
  have havg : footprintLower ≤
      uniformRealExpectation profile.fixedSeedInformation :=
    le_uniformRealExpectation profile.fixedSeedInformation footprintLower fixedSeedFootprint
  have hconditional : footprintLower ≤ profile.conditionalTraceMutualInformation := by
    rw [profile.conditional_eq_average]
    exact havg
  rw [profile.independent_chain_rule] at hconditional
  have hseed := profile.conditionalInputSeed_le_entropy.trans profile.seedEntropy_le_bits
  exact sub_le_iff_le_add.mpr (hconditional.trans (add_le_add_left hseed _))

/--
Private-randomness footprint bound obtained from the standard AC⁰
sign-correlation theorem for every fixed seed.
-/
theorem randomness_footprint_of_sign_correlation
    {n seedLength depthBound sizeBound : ℕ}
    {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]
    (trace : Bits seedLength → Footprint.ParityTrace n Transcript)
    (circuits : ∀ seed,
      Footprint.FiberCircuitFamily (trace seed) depthBound sizeBound)
    (profile : PrivateRandomnessProfile seedLength)
    (agrees : ∀ seed,
      profile.fixedSeedInformation seed = (trace seed).uniformMutualInformation)
    (hn : 1 ≤ n) (q : ℝ)
    (correlation : Footprint.SignParityCorrelationBound n depthBound sizeBound
      ((2 : ℝ) ^ ((3 / 2 : ℝ) - q))) :
    q - 3 / 2 - seedLength ≤ profile.traceMutualInformation := by
  apply randomness_cannot_erase_footprint profile (q - 3 / 2)
  intro seed
  rw [agrees seed]
  exact Footprint.footprint_quantitative_of_sign
    (trace seed) (circuits seed) hn q correlation

/-- The private-randomness footprint obtained directly from Tal's theorem. -/
theorem randomness_footprint_of_tal
    {n seedLength depthBound sizeBound : ℕ}
    {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]
    (tal : Tal.FourierTailTheorem)
    (trace : Bits seedLength → Footprint.ParityTrace n Transcript)
    (circuits : ∀ seed,
      Footprint.FiberCircuitFamily (trace seed) depthBound sizeBound)
    (profile : PrivateRandomnessProfile seedLength)
    (agrees : ∀ seed,
      profile.fixedSeedInformation seed = (trace seed).uniformMutualInformation)
    (hn : 1 ≤ n) (hsizeTwo : 1 < sizeBound) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound depthBound sizeBound n)) - seedLength ≤
      profile.traceMutualInformation := by
  apply randomness_cannot_erase_footprint profile
    (-Real.logb 2 (Real.sqrt (Tal.tailBound depthBound sizeBound n)))
  intro seed
  rw [agrees seed]
  exact Footprint.footprint_from_tal tal (trace seed) (circuits seed) hn hsizeTwo

theorem indicator_nonneg (b : Bool) : 0 ≤ indicator b := by
  cases b <;> simp [indicator]

theorem indicator_le_one (b : Bool) : indicator b ≤ 1 := by
  cases b <;> simp [indicator]

theorem uniformAcceptance_nonneg {n : ℕ} (monitor : Bits n → Bool) :
    0 ≤ uniformAcceptance monitor := by
  unfold uniformAcceptance
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => indicator_nonneg (monitor x)
  · positivity

theorem uniformAcceptance_le_one {n : ℕ} (monitor : Bits n → Bool) :
    uniformAcceptance monitor ≤ 1 := by
  unfold uniformAcceptance
  apply (div_le_one (by positivity : (0 : ℝ) < (2 ^ n : ℕ))).2
  calc
    (∑ x : Bits n, indicator (monitor x)) ≤ ∑ _x : Bits n, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ => indicator_le_one (monitor x)
    _ = (2 ^ n : ℕ) := by simp [Fintype.card_fun]

structure FiniteDistribution (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonnegative : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

namespace FiniteDistribution

variable {α : Type*} [Fintype α]

def probability (D : FiniteDistribution α) (event : α → Bool) : ℝ :=
  ∑ x, D.mass x * indicator (event x)

def bestConstantSuccess (D : FiniteDistribution α) (predicate : α → Bool) : ℝ :=
  max (D.probability predicate) (D.probability fun x => !(predicate x))

theorem probability_not (D : FiniteDistribution α) (predicate : α → Bool) :
    D.probability (fun x => !(predicate x)) = 1 - D.probability predicate := by
  rw [probability, probability]
  calc
    (∑ x, D.mass x * indicator (!(predicate x))) =
        ∑ x, (D.mass x - D.mass x * indicator (predicate x)) := by
          apply Finset.sum_congr rfl
          intro x _
          cases predicate x <;> simp [indicator]
    _ = (∑ x, D.mass x) - ∑ x, D.mass x * indicator (predicate x) := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ x, D.mass x * indicator (predicate x) := by rw [D.sum_one]

end FiniteDistribution

def predictionSuccess {α : Type*} [Fintype α] {seedLength traceLength : ℕ}
    (D : FiniteDistribution α) (visibleTrace : α → Bits seedLength → Bits traceLength)
    (monitor : Bits traceLength → Bool) (predicate : α → Bool) : ℝ :=
  ∑ x, D.mass x *
    (if predicate x then
      uniformAcceptance (fun seed => monitor (visibleTrace x seed))
    else
      1 - uniformAcceptance (fun seed => monitor (visibleTrace x seed)))

theorem prediction_le_prior
    {α : Type*} [Fintype α] {seedLength traceLength : ℕ}
    (D : FiniteDistribution α) (visibleTrace : α → Bits seedLength → Bits traceLength)
    (monitor : Bits traceLength → Bool) (predicate : α → Bool) (ε : ℝ)
    (pointwise : ∀ x,
      |uniformAcceptance (fun seed => monitor (visibleTrace x seed)) -
        uniformAcceptance monitor| ≤ ε) :
    predictionSuccess D visibleTrace monitor predicate ≤
      D.bestConstantSuccess predicate + ε := by
  let q := uniformAcceptance monitor
  let qx : α → ℝ := fun x =>
    uniformAcceptance (fun seed => monitor (visibleTrace x seed))
  let p := D.probability predicate
  have hterm : ∀ x,
      (if predicate x then qx x else 1 - qx x) ≤
        (if predicate x then q else 1 - q) + ε := by
    intro x
    have hx := pointwise x
    dsimp only [qx, q]
    by_cases hp : predicate x = true
    · simp [hp]
      have hupper :
          uniformAcceptance (fun seed => monitor (visibleTrace x seed)) -
            uniformAcceptance monitor ≤ ε := (abs_le.mp hx).2
      linarith
    · simp [hp]
      have hlower : -ε ≤
          uniformAcceptance (fun seed => monitor (visibleTrace x seed)) -
            uniformAcceptance monitor := (abs_le.mp hx).1
      linarith
  have hweighted : predictionSuccess D visibleTrace monitor predicate ≤
      ∑ x, D.mass x * ((if predicate x then q else 1 - q) + ε) := by
    unfold predictionSuccess
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hterm x) (D.nonnegative x)
  have hideal :
      (∑ x, D.mass x * (if predicate x then q else 1 - q)) =
        p * q + (1 - p) * (1 - q) := by
    calc
      (∑ x, D.mass x * (if predicate x then q else 1 - q)) =
          (∑ x, D.mass x * indicator (predicate x)) * q +
            (∑ x, D.mass x * indicator (!(predicate x))) * (1 - q) := by
              rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x _
              cases predicate x <;> simp [indicator]
      _ = p * q + D.probability (fun x => !(predicate x)) * (1 - q) := rfl
      _ = p * q + (1 - p) * (1 - q) := by
            rw [D.probability_not]
  have hsum :
      (∑ x, D.mass x * ((if predicate x then q else 1 - q) + ε)) =
        p * q + (1 - p) * (1 - q) + ε := by
    rw [← hideal]
    calc
      (∑ x, D.mass x * ((if predicate x then q else 1 - q) + ε)) =
          (∑ x, D.mass x * (if predicate x then q else 1 - q)) +
            (∑ x, D.mass x) * ε := by
              calc
                (∑ x, D.mass x * ((if predicate x then q else 1 - q) + ε)) =
                    ∑ x, (D.mass x * (if predicate x then q else 1 - q) +
                      D.mass x * ε) := by
                        apply Finset.sum_congr rfl
                        intro x _
                        ring
                _ = (∑ x, D.mass x * (if predicate x then q else 1 - q)) +
                    ∑ x, D.mass x * ε := Finset.sum_add_distrib
                _ = (∑ x, D.mass x * (if predicate x then q else 1 - q)) +
                    (∑ x, D.mass x) * ε := by rw [Finset.sum_mul]
      _ = (∑ x, D.mass x * (if predicate x then q else 1 - q)) + ε := by
          rw [D.sum_one, one_mul]
  have hq0 : 0 ≤ q := uniformAcceptance_nonneg monitor
  have hq1 : q ≤ 1 := uniformAcceptance_le_one monitor
  have hconvex : p * q + (1 - p) * (1 - q) ≤ max p (1 - p) := by
    by_cases hp : p ≤ 1 - p
    · rw [max_eq_right hp]
      nlinarith
    · rw [max_eq_left (le_of_not_ge hp)]
      nlinarith
  calc
    predictionSuccess D visibleTrace monitor predicate
        ≤ ∑ x, D.mass x * ((if predicate x then q else 1 - q) + ε) := hweighted
    _ = p * q + (1 - p) * (1 - q) + ε := hsum
    _ ≤ max p (1 - p) + ε := add_le_add_right hconvex ε
    _ = D.bestConstantSuccess predicate + ε := by
      rw [FiniteDistribution.bestConstantSuccess,
        FiniteDistribution.probability_not]

/-! ## The encryption theorems -/

theorem encrypted_cot_no_readability
    {α : Type*} [Fintype α] {seedLength front suffix : ℕ}
    (D : FiniteDistribution α) (plainTrace : α → Bits front)
    (generator : Bits seedLength → Bits (front + suffix))
    (fullMonitors : MonitorClass (front + suffix))
    (traceMonitors : MonitorClass front) (ε : ℝ)
    (secure : SecureAgainst generator fullMonitors ε)
    (prefixClosed : PrefixClosed fullMonitors traceMonitors)
    (xorClosed : XorClosed traceMonitors)
    (monitor : Monitor front) (hmonitor : monitor ∈ traceMonitors)
    (predicate : α → Bool) :
    predictionSuccess D
        (encryptedTrace plainTrace (prefixGenerator generator)) monitor predicate ≤
      D.bestConstantSuccess predicate + ε := by
  have prefixSecure :
      SecureAgainst (prefixGenerator generator) traceMonitors ε :=
    secure_prefix generator fullMonitors traceMonitors ε secure prefixClosed
  apply prediction_le_prior D
    (encryptedTrace plainTrace (prefixGenerator generator)) monitor predicate ε
  intro input
  have h := encryptedTrace_pointwise_secure plainTrace (prefixGenerator generator)
    traceMonitors ε prefixSecure xorClosed input monitor hmonitor
  simpa [distinguishingAdvantage, samplerAcceptance] using h

/--
The paper's general polynomial-time encryption theorem at a fixed input
length.  Runtime enters only through `front`, the plaintext trace length;
`suffix` witnesses that the PRG output is long enough.  Thus the same result
applies to near-linear traces and to the `O(N^k log N)` traces in the general
theorem.
-/
theorem encrypted_trace_no_readability_of_local_generator
    {α : Type*} [Fintype α] {seedLength front suffix locality : ℕ}
    (D : FiniteDistribution α) (plainTrace : α → Bits front)
    (generator : LocalGenerator seedLength (front + suffix) locality)
    (fullMonitors : MonitorClass (front + suffix))
    (traceMonitors : MonitorClass front) (ε : ℝ)
    (secure : SecureAgainst generator.generate fullMonitors ε)
    (prefixClosed : PrefixClosed fullMonitors traceMonitors)
    (xorClosed : XorClosed traceMonitors)
    (monitor : Monitor front) (hmonitor : monitor ∈ traceMonitors)
    (predicate : α → Bool) :
    predictionSuccess D
        (encryptedTrace plainTrace (prefixGenerator generator.generate)) monitor predicate ≤
      D.bestConstantSuccess predicate + ε :=
  encrypted_cot_no_readability D plainTrace generator.generate fullMonitors traceMonitors ε
    secure prefixClosed xorClosed monitor hmonitor predicate

/--
Exact finite version of “Transformers can encrypt reasoning”.  The first
conjunct is the information-theoretic footprint left after charging at most
one bit per private seed bit.  The second says that every admissible monitor
predicts an arbitrary input predicate no better than its best constant prior
guess, up to the PRG advantage.
-/
theorem encrypted_trace_leakage_and_security
    {α : Type*} [Fintype α] {seedLength front suffix locality : ℕ}
    (D : FiniteDistribution α) (plainTrace : α → Bits front)
    (generator : LocalGenerator seedLength (front + suffix) locality)
    (fullMonitors : MonitorClass (front + suffix))
    (traceMonitors : MonitorClass front) (ε footprintLower : ℝ)
    (secure : SecureAgainst generator.generate fullMonitors ε)
    (prefixClosed : PrefixClosed fullMonitors traceMonitors)
    (xorClosed : XorClosed traceMonitors)
    (profile : PrivateRandomnessProfile seedLength)
    (fixedSeedFootprint : ∀ seed,
      footprintLower ≤ profile.fixedSeedInformation seed)
    (monitor : Monitor front) (hmonitor : monitor ∈ traceMonitors)
    (predicate : α → Bool) :
    footprintLower - seedLength ≤ profile.traceMutualInformation ∧
      predictionSuccess D
          (encryptedTrace plainTrace (prefixGenerator generator.generate)) monitor predicate ≤
        D.bestConstantSuccess predicate + ε := by
  constructor
  · exact randomness_cannot_erase_footprint profile footprintLower fixedSeedFootprint
  · exact encrypted_cot_no_readability D plainTrace generator.generate
      fullMonitors traceMonitors ε
      secure prefixClosed xorClosed monitor hmonitor predicate

end Encryption
