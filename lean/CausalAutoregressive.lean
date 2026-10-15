import CausalMatrix
import Autoregressive

/-!
# Genuine shared-matrix causal autoregression

Each generation step runs a longer prefix of the same learned matrices and
absolute position table. The input is the prompt's one-hot token wires;
candidate-prefix wires are constants. The next token is the proved greedy
matrix readout, not a supplied transition or realization certificate.
-/

noncomputable section

namespace CausalAutoregressive

open TransformerAC0 Autoregressive

structure Model (a : Architecture) (front steps : ℕ) where
  parameters : FixedPrecisionTransformer a
  vocabulary_positive : 0 < a.vocabulary
  front_positive : 0 < front
  context_bound : front + steps ≤ a.contextLength

namespace Model

variable {a : Architecture} {front steps : ℕ}

def architecture (_model : Model a front steps) : Architecture := a

def contextLiteral (_model : Model a front steps) (time : Fin (steps + 1))
    (prefixTokens : Fin time.val → Fin a.vocabulary) :
    Fin ((front + time.val) * a.vocabulary) → ContextLiteral (front * a.vocabulary) :=
  fun wire =>
    let location := finProdFinEquiv.symm wire
    Fin.addCases
      (fun position => .positive (finProdFinEquiv (position, location.2)))
      (fun position => .constant (decide (location.2 = prefixTokens position))) location.1

def contextInput (model : Model a front steps) (input : Bits (front * a.vocabulary))
    (time : Fin (steps + 1)) (prefixTokens : Fin time.val → Fin a.vocabulary) :
    Bits ((front + time.val) * a.vocabulary) :=
  fun wire => (model.contextLiteral time prefixTokens wire).eval input

def stepModel (model : Model a front steps) (time : Fin (steps + 1)) :
    FixedPrecisionTransformer (CausalMatrix.architecture a (front + time.val)) :=
  CausalMatrix.restrictContext model.parameters (front + time.val)
    (by have h := time.isLt; have hb := model.context_bound; omega)

def generatedToken (model : Model a front steps) (input : Bits (front * a.vocabulary))
    (time : Fin (steps + 1)) : Fin a.vocabulary :=
  (model.stepModel time).runToken model.vocabulary_positive
    (by have h := model.front_positive; change 0 < front + time.val; omega)
    (model.contextInput input time (fun previous =>
      model.generatedToken input ⟨previous.val, previous.isLt.trans time.isLt⟩))
termination_by time.val

def transcript (model : Model a front steps) (input : Bits (front * a.vocabulary)) :
    Fin steps → Fin a.vocabulary := fun time => model.generatedToken input time.castSucc

def answer (model : Model a front steps) (input : Bits (front * a.vocabulary)) : Bool :=
  model.parameters.outputLabel (model.generatedToken input (Fin.last steps))

def contextCircuit (model : Model a front steps) (time : Fin (steps + 1))
    (prefixTokens : Fin time.val → Fin a.vocabulary) :
    Circuit (front * a.vocabulary) ((front + time.val) * a.vocabulary) :=
  .bundle fun wire => (model.contextLiteral time prefixTokens wire).circuit

@[simp] theorem eval_contextCircuit (model : Model a front steps) (time : Fin (steps + 1))
    (prefixTokens : Fin time.val → Fin a.vocabulary) (input : Bits (front * a.vocabulary)) :
    Circuit.eval (model.contextCircuit time prefixTokens) input = model.contextInput input time prefixTokens := by
  funext wire
  simp [contextCircuit, contextInput, Circuit.eval]

theorem contextCircuit_depth (model : Model a front steps) (time : Fin (steps + 1))
    (prefixTokens : Fin time.val → Fin a.vocabulary) : Circuit.depth (model.contextCircuit time prefixTokens) ≤ 1 := by
  simp only [contextCircuit, Circuit.depth]
  exact Finset.sup_le fun wire _ => ContextLiteral.depth_circuit_le_one _

theorem contextCircuit_size (model : Model a front steps) (time : Fin (steps + 1))
    (prefixTokens : Fin time.val → Fin a.vocabulary) :
    Circuit.gateCount (model.contextCircuit time prefixTokens) ≤ (front + time.val) * a.vocabulary := by
  simp only [contextCircuit, Circuit.gateCount]
  calc
    _ ≤ ∑ _wire : Fin ((front + time.val) * a.vocabulary), 1 :=
      Finset.sum_le_sum fun wire _ => ContextLiteral.gateCount_circuit_le_one _
    _ = _ := by simp

def predictionCircuit (model : Model a front steps) (time : Fin (steps + 1))
    (prefixTokens : Fin time.val → Fin a.vocabulary) (token : Fin a.vocabulary) :
    Circuit (front * a.vocabulary) 1 :=
  .seq (model.contextCircuit time prefixTokens) ((model.stepModel time).tokenClassifier token)

@[simp] theorem eval_predictionCircuit (model : Model a front steps) (time : Fin (steps + 1))
    (prefixTokens : Fin time.val → Fin a.vocabulary) (token : Fin a.vocabulary)
    (input : Bits (front * a.vocabulary)) :
    Circuit.eval (model.predictionCircuit time prefixTokens token) input 0 =
      decide ((model.stepModel time).runToken model.vocabulary_positive
        (by have h := model.front_positive; change 0 < front + time.val; omega)
        (model.contextInput input time prefixTokens) = token) := by
  simp only [predictionCircuit, Circuit.eval, eval_contextCircuit]
  exact (model.stepModel time).eval_tokenClassifier token model.vocabulary_positive _ _

/-- Exact candidate next-token circuits have a common precision/layer depth
bound, even though the causal prefix length grows at every generation step. -/
theorem predictionCircuit_depth (model : Model a front steps) (time : Fin (steps + 1))
    (prefixTokens : Fin time.val → Fin a.vocabulary) (token : Fin a.vocabulary) :
    Circuit.depth (model.predictionCircuit time prefixTokens token) ≤
      (a.layers + 2) * TransformerDepthCost.stage model.parameters.arithmetic + 1 := by
  have hc := model.contextCircuit_depth time prefixTokens
  have hp : Circuit.depth ((model.stepModel time).tokenClassifier token) ≤
      (a.layers + 2) * TransformerDepthCost.stage model.parameters.arithmetic :=
    (model.stepModel time).tokenClassifier_depth_le token
  simp only [predictionCircuit, Circuit.depth]
  omega

theorem prefix_sizeBound (model : Model a front steps) (time : Fin (steps + 1)) :
    FixedPrecisionTransformer.sizeBound (CausalMatrix.architecture a (front + time.val)) ≤
      FixedPrecisionTransformer.sizeBound a := by
  have htime : front + time.val ≤ a.contextLength := by
    have ht := time.isLt
    have hb := model.context_bound
    omega
  simp only [FixedPrecisionTransformer.sizeBound, Architecture.localBase, CausalMatrix.architecture,
    Architecture.hiddenWidth]
  omega

/-- All prefix/token classifiers have a single polynomial budget whose
coefficient and exponent come from fixed scalar arithmetic. No circuit-size
certificate is supplied by the autoregressive model. -/
theorem predictionCircuit_polynomial_size (model : Model a front steps) :
    ∃ coefficient exponent : ℕ, ∀ (time : Fin (steps + 1))
      (prefixTokens : Fin time.val → Fin a.vocabulary) (token : Fin a.vocabulary),
      Circuit.gateCount (model.predictionCircuit time prefixTokens token) ≤
        a.inputBits + coefficient * (FixedPrecisionTransformer.sizeBound a + 1) ^ exponent := by
  obtain ⟨coefficient, exponent, hpolynomial⟩ := TransformerGateCost.total_polynomial model.parameters.arithmetic
  refine ⟨coefficient, exponent, ?_⟩
  intro time prefixTokens token
  have hcontext := model.contextCircuit_size time prefixTokens
  have hcontext' : Circuit.gateCount (model.contextCircuit time prefixTokens) ≤ a.inputBits := by
    have htime : front + time.val ≤ a.contextLength := by
      have ht := time.isLt
      have hb := model.context_bound
      omega
    exact hcontext.trans (Nat.mul_le_mul_right a.vocabulary htime)
  have hcompiled : Circuit.gateCount ((model.stepModel time).tokenClassifier token) ≤
      TransformerGateCost.total model.parameters.arithmetic
        (FixedPrecisionTransformer.sizeBound (CausalMatrix.architecture a (front + time.val))) :=
    (model.stepModel time).tokenClassifier_size_le token
  have hpolynomial' := hpolynomial (FixedPrecisionTransformer.sizeBound (CausalMatrix.architecture a (front + time.val)))
  have hpower : (FixedPrecisionTransformer.sizeBound (CausalMatrix.architecture a (front + time.val)) + 1) ^ exponent ≤
      (FixedPrecisionTransformer.sizeBound a + 1) ^ exponent :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (model.prefix_sizeBound time) 1) exponent
  have hsize := hcompiled.trans (hpolynomial'.trans (Nat.mul_le_mul_left coefficient hpower))
  simp only [predictionCircuit, Circuit.gateCount]
  exact Nat.add_le_add hcontext' hsize

end Model

end CausalAutoregressive
