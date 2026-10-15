import TaskReductions
import FiniteInformation

/-!
# Uniform full-alphabet task reductions

An alphabet with paired even/odd symbols is equivalent to a parity bit and an
independent pair label.  Holding the labels fixed restricts every one-hot
input wire to a Boolean literal.  The existing matrix compiler therefore
constructs all slice circuits with a common depth and gate bound.  Averaging
their fiber bounds proves the footprint for the full uniform alphabet.
-/

noncomputable section
open scoped BigOperators

namespace UniformTaskFootprint

open TransformerAC0 Autoregressive FiniteInformation

/-- One input wire of a fixed-prefix context for a symbolic input alphabet. -/
inductive SymbolLiteral (n : ℕ) (Alphabet : Type*)
  | constant (value : Bool)
  | equals (index : Fin n) (symbol : Alphabet)
  | test (index : Fin n) (predicate : Alphabet → Bool)

namespace SymbolLiteral

def eval [DecidableEq Alphabet] (literal : SymbolLiteral n Alphabet)
    (input : Fin n → Alphabet) : Bool :=
  match literal with
  | .constant value => value
  | .equals index symbol => decide (input index = symbol)
  | .test index predicate => predicate (input index)

/-- Every Boolean unary map is a constant, a positive literal, or a negative
literal. -/
def unaryLiteral (index : Fin n) (function : Bool → Bool) : ContextLiteral n :=
  match function false, function true with
  | false, false => .constant false
  | true, true => .constant true
  | false, true => .positive index
  | true, false => .negative index

@[simp] theorem eval_unaryLiteral (index : Fin n) (function : Bool → Bool)
    (input : Bits n) :
    (unaryLiteral index function).eval input = function (input index) := by
  cases hfalse : function false <;> cases htrue : function true <;>
    cases hinput : input index <;>
    simp [unaryLiteral, hfalse, htrue, ContextLiteral.eval, hinput]

def restrict [DecidableEq Alphabet] (pairing : Alphabet ≃ Bool × Label)
    (labels : Fin n → Label) (literal : SymbolLiteral n Alphabet) : ContextLiteral n :=
  match literal with
  | .constant value => .constant value
  | .equals index symbol => unaryLiteral index
      (fun bit => decide (pairing.symm (bit, labels index) = symbol))
  | .test index predicate => unaryLiteral index
      (fun bit => predicate (pairing.symm (bit, labels index)))

@[simp] theorem eval_restrict [DecidableEq Alphabet]
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label)
    (literal : SymbolLiteral n Alphabet) (input : Bits n) :
    (literal.restrict pairing labels).eval input =
      literal.eval (fun index => pairing.symm (input index, labels index)) := by
  cases literal with
  | constant value => rfl
  | equals index symbol =>
      exact eval_unaryLiteral index
        (fun bit => decide (pairing.symm (bit, labels index) = symbol)) input
  | test index predicate =>
      exact eval_unaryLiteral index
        (fun bit => predicate (pairing.symm (bit, labels index))) input

end SymbolLiteral

/-- Actual autoregressive execution of a matrix Transformer on a finite
symbol alphabet.  The only input operations in its context are one-hot tests
and constants, as in the paper. -/
structure SymbolGenerator (n length : ℕ) (Alphabet : Type*) where
  architecture : Architecture
  transformer : FixedPrecisionTransformer architecture
  context : (time : ℕ) → Bits time →
    Fin architecture.inputBits → SymbolLiteral n Alphabet

namespace SymbolGenerator

variable {Alphabet Label : Type*} [DecidableEq Alphabet]
variable {n length : ℕ}

def generatedToken (model : SymbolGenerator n length Alphabet)
    (input : Fin n → Alphabet) (time : ℕ) : Bool :=
  model.transformer.run (fun wire =>
    (model.context time (fun previous => model.generatedToken input previous) wire).eval input)
termination_by time

def transcript (model : SymbolGenerator n length Alphabet)
    (input : Fin n → Alphabet) : Bits length := fun time => model.generatedToken input time

def answer (model : SymbolGenerator n length Alphabet)
    (input : Fin n → Alphabet) : Bool := model.generatedToken input length

def slice (model : SymbolGenerator n length Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) :
    FixedPrecisionGenerator n length where
  architecture := model.architecture
  transformer := model.transformer
  context := fun time prefixBits wire => (model.context time prefixBits wire).restrict pairing labels

@[simp] theorem slice_generatedToken (model : SymbolGenerator n length Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label)
    (input : Bits n) (time : ℕ) :
    (model.slice pairing labels).generatedToken input time =
      model.generatedToken (fun index => pairing.symm (input index, labels index)) time := by
  induction time using Nat.strong_induction_on with
  | h time ih =>
      rw [FixedPrecisionGenerator.generatedToken, generatedToken]
      unfold FixedPrecisionGenerator.contextInput
      change model.transformer.run _ = model.transformer.run _
      congr 1
      funext wire
      simp only [slice, SymbolLiteral.eval_restrict]
      congr 2
      funext previous
      exact ih previous previous.isLt

@[simp] theorem slice_transcript (model : SymbolGenerator n length Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) (input : Bits n) :
    (model.slice pairing labels).transcript input =
      model.transcript (fun index => pairing.symm (input index, labels index)) := by
  funext time
  exact model.slice_generatedToken pairing labels input time

@[simp] theorem slice_answer (model : SymbolGenerator n length Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) (input : Bits n) :
    (model.slice pairing labels).answer input =
      model.answer (fun index => pairing.symm (input index, labels index)) :=
  model.slice_generatedToken pairing labels input length

def fiberDepth (model : SymbolGenerator n length Alphabet) : ℕ :=
  Circuit.depth model.transformer.compile + 4

def fiberSize (model : SymbolGenerator n length Alphabet) : ℕ :=
  (length + 1) * (model.architecture.inputBits +
    Circuit.gateCount model.transformer.compile + 1) + 2

/-- Coordinatewise full-alphabet pairing. -/
def wordsEquiv (pairing : Alphabet ≃ Bool × Label) :
    (Fin n → Alphabet) ≃ (Bits n × (Fin n → Label)) where
  toFun input := (fun i => (pairing (input i)).1, fun i => (pairing (input i)).2)
  invFun pair := fun i => pairing.symm (pair.1 i, pair.2 i)
  left_inv input := by funext i; simp
  right_inv pair := by
    apply Prod.ext <;> funext i <;> simp

/-- Full-uniform footprint for any alphabet whose Boolean task is the parity
of its pairing bits.  No slice circuit, probability transport, or entropy
certificate is an input to this theorem. -/
theorem uniform_footprint
    [Fintype Alphabet] [Nonempty Alphabet] [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (model : SymbolGenerator n length Alphabet)
    (pairing : Alphabet ≃ Bool × Label)
    (correct : ∀ input, model.answer input =
      Tal.parity (fun i => (pairing (input i)).1)) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (Distribution.uniform (Fin n → Alphabet)).entropy model.transcript := by
  classical
  let rate := Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)
  have hsize : 1 < model.fiberSize := by unfold fiberSize; omega
  have hpositive : 0 < rate := Real.sqrt_pos.mpr (Tal.tailBound_pos _ _ _)
  let trace : Bits n × (Fin n → Label) → Bits length := fun pair =>
    model.transcript (fun i => pairing.symm (pair.1 i, pair.2 i))
  have hsliceCorrect : ∀ labels input,
      (model.slice pairing labels).answer input = Tal.parity input := by
    intro labels input
    rw [slice_answer, correct]
    simp
  have hsliceCap : ∀ labels candidate,
      (Distribution.uniform (Bits n)).pushMass (fun input => trace (input, labels)) candidate ≤ rate := by
    intro labels candidate
    let sliced := model.slice pairing labels
    let G := sliced.parityTrace (hsliceCorrect labels)
    have h := G.transcriptProbability_le_of_correlation
      (sliced.explicitFiberCircuitFamily (hsliceCorrect labels))
      (Footprint.indicatorParityCorrelationBound_of_sign hn
        (Footprint.signParityCorrelationBound_of_tal tal hsize)) candidate
    have hrewrite : (fun input => trace (input, labels)) = sliced.transcript := by
      funext input
      exact (model.slice_transcript pairing labels input).symm
    rw [hrewrite]
    rw [Distribution.uniform_pushMass_eq_card]
    simpa only [G, rate, sliced, slice, fiberDepth, fiberSize,
      Footprint.ParityTrace.transcriptProbability, Footprint.ParityTrace.transcriptFiber,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      FixedPrecisionGenerator.explicitFiberSize, FixedPrecisionGenerator.explicitFiberDepth,
      FixedPrecisionGenerator.parityTrace] using h
  have hcap : ∀ candidate,
      (Distribution.uniform (Bits n × (Fin n → Label))).pushMass trace candidate ≤ rate := by
    intro candidate
    rw [Distribution.uniform_product_mixture]
    simp_rw [Distribution.fixedRight_pushMass]
    calc
      (∑ labels, (Distribution.uniform (Fin n → Label)).mass labels *
          (Distribution.uniform (Bits n)).pushMass (fun input => trace (input, labels)) candidate) ≤
        ∑ labels, (Distribution.uniform (Fin n → Label)).mass labels * rate := by
          apply Finset.sum_le_sum
          intro labels _
          exact mul_le_mul_of_nonneg_left (hsliceCap labels candidate)
            ((Distribution.uniform (Fin n → Label)).nonnegative labels)
      _ = rate := by rw [← Finset.sum_mul, (Distribution.uniform _).sum_one, one_mul]
  have hentropy := (Distribution.uniform (Bits n × (Fin n → Label))).neg_log_le_entropy_of_pushMass_le
    trace hpositive hcap
  have hequiv := Distribution.uniform_entropy_equiv (wordsEquiv pairing) trace
  have hcompose : (fun input => trace (wordsEquiv pairing input)) = model.transcript := by
    funext input
    simp [trace, wordsEquiv]
  rw [hcompose] at hequiv
  rw [← hequiv] at hentropy
  exact hentropy

/-- The full uniform alphabet result expressed as actual Shannon mutual
information with the complete symbolic input. -/
theorem uniform_mutualInformation_lower_bound
    [Fintype Alphabet] [Nonempty Alphabet] [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (model : SymbolGenerator n length Alphabet)
    (pairing : Alphabet ≃ Bool × Label)
    (correct : ∀ input, model.answer input =
      Tal.parity (fun i => (pairing (input i)).1)) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (Distribution.uniform (Fin n → Alphabet)).mutualInformation id model.transcript := by
  rw [Distribution.mutualInformation_id_eq_entropy]
  exact model.uniform_footprint tal pairing correct hn

theorem uniform_binary_length_lower_bound
    [Fintype Alphabet] [Nonempty Alphabet] [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (model : SymbolGenerator n length Alphabet)
    (pairing : Alphabet ≃ Bool × Label)
    (correct : ∀ input, model.answer input =
      Tal.parity (fun i => (pairing (input i)).1)) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (length : ℝ) := by
  have h := (Distribution.uniform (Fin n → Alphabet)).entropy_le_log_card model.transcript
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow] at h
  rw [Real.logb, Real.log_pow] at h
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hcap : (Distribution.uniform (Fin n → Alphabet)).entropy model.transcript ≤
      (length : ℝ) := by
    convert h using 1
    field_simp [hlog]
  exact (model.uniform_footprint tal pairing correct hn).trans hcap

end SymbolGenerator

/-- Average a uniform Boolean slice cap over all pair labels. This finite
probability argument also applies to separator-terminated trace spaces. -/
theorem paired_uniform_entropy_lower_bound
    {Alphabet Label Trace : Type*} [Fintype Alphabet] [Nonempty Alphabet]
    [DecidableEq Alphabet] [Fintype Label] [Nonempty Label]
    [Fintype Trace] [DecidableEq Trace]
    (pairing : Alphabet ≃ Bool × Label) (trace : (Fin n → Alphabet) → Trace)
    (rate : ℝ) (hpositive : 0 < rate)
    (sliceCap : ∀ (labels : Fin n → Label) (candidate : Trace),
      (Distribution.uniform (Bits n)).pushMass
        (fun input => trace (fun i => pairing.symm (input i, labels i))) candidate ≤ rate) :
    -Real.logb 2 rate ≤ (Distribution.uniform (Fin n → Alphabet)).entropy trace := by
  classical
  let pairedTrace : Bits n × (Fin n → Label) → Trace := fun pair =>
    trace (fun i => pairing.symm (pair.1 i, pair.2 i))
  have hcap : ∀ candidate,
      (Distribution.uniform (Bits n × (Fin n → Label))).pushMass pairedTrace candidate ≤ rate := by
    intro candidate
    rw [Distribution.uniform_product_mixture]
    simp_rw [Distribution.fixedRight_pushMass]
    calc
      (∑ labels, (Distribution.uniform (Fin n → Label)).mass labels *
          (Distribution.uniform (Bits n)).pushMass (fun input => pairedTrace (input, labels)) candidate) ≤
        ∑ labels, (Distribution.uniform (Fin n → Label)).mass labels * rate := by
          apply Finset.sum_le_sum
          intro labels _
          exact mul_le_mul_of_nonneg_left (sliceCap labels candidate)
            ((Distribution.uniform (Fin n → Label)).nonnegative labels)
      _ = rate := by rw [← Finset.sum_mul, (Distribution.uniform _).sum_one, one_mul]
  have hentropy := (Distribution.uniform (Bits n × (Fin n → Label))).neg_log_le_entropy_of_pushMass_le
    pairedTrace hpositive hcap
  have hequiv := Distribution.uniform_entropy_equiv (SymbolGenerator.wordsEquiv pairing) pairedTrace
  have hcompose : (fun input => pairedTrace (SymbolGenerator.wordsEquiv pairing input)) = trace := by
    funext input
    simp [pairedTrace, SymbolGenerator.wordsEquiv]
  rw [hcompose] at hequiv
  rw [← hequiv] at hentropy
  exact hentropy

open TaskReductions

/-- The paper's `S₅` lower bound with the complete 120-symbol uniform input
alphabet, with correctness stated using the actual ordered product. -/
theorem s5_uniform_footprint
    (tal : Tal.FourierTailTheorem) (model : SymbolGenerator n length S5)
    (correct : ∀ input, model.answer input =
      oddUnit (Equiv.Perm.sign (orderedProduct input))) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (Distribution.uniform (Fin n → S5)).mutualInformation id model.transcript := by
  apply model.uniform_mutualInformation_lower_bound tal s5Pairing _ hn
  intro input
  rw [correct, ← s5StateTrackingParity_eq_product_sign]
  rfl

/-- The paper's iterated-addition lower bound for all one hundred symbols. -/
theorem addition100_uniform_footprint
    (tal : Tal.FourierTailTheorem) (model : SymbolGenerator n length (Fin 100))
    (correct : ∀ input, model.answer input = additionLSB (fun i => (input i).val))
    (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (Distribution.uniform (Fin n → Fin 100)).mutualInformation id model.transcript := by
  apply model.uniform_mutualInformation_lower_bound tal additionPairing100 _ hn
  intro input
  rw [correct, additionLSB_eq_parity]
  rfl

theorem s5_uniform_binary_length_lower_bound
    (tal : Tal.FourierTailTheorem) (model : SymbolGenerator n length S5)
    (correct : ∀ input, model.answer input =
      oddUnit (Equiv.Perm.sign (orderedProduct input))) (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (length : ℝ) := by
  apply model.uniform_binary_length_lower_bound tal s5Pairing _ hn
  intro input
  rw [correct, ← s5StateTrackingParity_eq_product_sign]
  rfl

theorem addition100_uniform_binary_length_lower_bound
    (tal : Tal.FourierTailTheorem) (model : SymbolGenerator n length (Fin 100))
    (correct : ∀ input, model.answer input = additionLSB (fun i => (input i).val))
    (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (length : ℝ) := by
  apply model.uniform_binary_length_lower_bound tal additionPairing100 _ hn
  intro input
  rw [correct, additionLSB_eq_parity]
  rfl

end UniformTaskFootprint
