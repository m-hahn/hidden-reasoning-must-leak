import TalShallowCircuit
import TalTreeNormalForm

/-!
# Ranked shared-gate networks

Gate names are retained when bottom functions are simplified. Bottom normal
forms count once as named functions; their literal terms and clauses are not
new upper gates. Every upper gate reads strictly lower-ranked named functions
or input literals/constants. This is a semantic representation with explicit
gate equations, not a Fourier-tail or switching certificate.
-/

noncomputable section
namespace TalGateNetwork
open TransformerAC0 Algebraic AC0 TalMixedSwitching

inductive Reference (n : ℕ) (G : Type)
  | constant (value : Bool)
  | literal (value : Literal n)
  | gate (index : G) (positive : Bool)

namespace Reference

def eval {n : ℕ} {G : Type} (functions : G → ScalarFunction Bool n) :
    Reference n G → ScalarFunction Bool n
  | .constant value => fun _ => value
  | .literal atom => atom.eval
  | .gate index positive => fun input => if positive then functions index input else !(functions index input)

def negate {n : ℕ} {G : Type} : Reference n G → Reference n G
  | .constant value => .constant (!value)
  | .literal atom => .literal atom.negate
  | .gate index positive => .gate index (!positive)

theorem eval_negate {n : ℕ} {G : Type} (functions : G → ScalarFunction Bool n)
    (reference : Reference n G) (input : Bits n) :
    reference.negate.eval functions input = !(reference.eval functions input) := by
  cases reference with
  | constant value => rfl
  | literal literal => exact Literal.eval_negate _ _
  | gate index positive => cases positive <;> simp [negate, eval]

def map {n : ℕ} {G H : Type} (mapping : G → H) : Reference n G → Reference n H
  | .constant value => .constant value
  | .literal atom => .literal atom
  | .gate index positive => .gate (mapping index) positive

theorem eval_map {n : ℕ} {G H : Type} (mapping : G → H)
    (functions : H → ScalarFunction Bool n) (reference : Reference n G) (input : Bits n) :
    (reference.map mapping).eval functions input = reference.eval (functions ∘ mapping) input := by
  cases reference <;> rfl

def Below {n : ℕ} {G : Type} (rank : G → ℕ) (bound : ℕ) : Reference n G → Prop
  | .constant _ => True
  | .literal _ => True
  | .gate index _ => rank index < bound

def restrict {n : ℕ} {G : Type} (rho : PartialAssignment n) : Reference n G → Reference n G
  | .constant value => .constant value
  | .literal atom => match rho atom.index with
      | none => .literal atom
      | some value => .constant (decide (value = atom.value))
  | .gate index positive => .gate index positive

theorem eval_restrict {n : ℕ} {G : Type} (rho : PartialAssignment n)
    (functions : G → ScalarFunction Bool n) (reference : Reference n G) (input : Bits n) :
    (reference.restrict rho).eval (fun index => ScalarFunction.restrict (functions index) rho) input =
      ScalarFunction.restrict (reference.eval functions) rho input := by
  cases reference with
  | constant value => rfl
  | literal literal =>
      cases h : rho literal.index <;>
        simp [restrict, eval, ScalarFunction.restrict, Literal.eval, PartialAssignment.apply, h]
  | gate index positive => cases positive <;> rfl

theorem restrict_below {n : ℕ} {G : Type} (rho : PartialAssignment n)
    (rank : G → ℕ) (bound : ℕ) (reference : Reference n G) (h : reference.Below rank bound) :
    (reference.restrict rho).Below rank bound := by
  cases reference with
  | constant value => trivial
  | literal literal => cases hvalue : rho literal.index <;> simp [restrict, Below, hvalue]
  | gate index positive => exact h

theorem negate_below {n : ℕ} {G : Type} (rank : G → ℕ) (bound : ℕ) (reference : Reference n G) :
    reference.negate.Below rank bound ↔ reference.Below rank bound := by
  cases reference <;> rfl

def substitute {n k : ℕ} {G H : Type} (inputs : Fin k → Reference n H) (gates : G → H) :
    Reference k G → Reference n H
  | .constant value => .constant value
  | .literal atom => if atom.value then inputs atom.index else (inputs atom.index).negate
  | .gate index positive => .gate (gates index) positive

theorem eval_substitute {n k : ℕ} {G H : Type}
    (inputs : Fin k → Reference n H) (gates : G → H)
    (oldFunctions : G → ScalarFunction Bool k) (newFunctions : H → ScalarFunction Bool n)
    (oldInput : Bits k) (newInput : Bits n)
    (hinputs : ∀ index, (inputs index).eval newFunctions newInput = oldInput index)
    (hgates : ∀ index, newFunctions (gates index) newInput = oldFunctions index oldInput)
    (reference : Reference k G) :
    (reference.substitute inputs gates).eval newFunctions newInput = reference.eval oldFunctions oldInput := by
  cases reference with
  | constant value => rfl
  | literal atom =>
      change _ = atom.eval oldInput
      rw [TalShallowCircuit.literal_eval_value]
      cases hvalue : atom.value <;>
        simp [substitute, eval_negate, hvalue, hinputs]
  | gate index positive => cases positive <;> simp [substitute, eval, hgates]

theorem below_substitute {n k : ℕ} {G H : Type}
    (inputs : Fin k → Reference n H) (gates : G → H) (oldRank : G → ℕ) (newRank : H → ℕ)
    (oldBound newBound : ℕ)
    (hinputs : ∀ index, (inputs index).Below newRank newBound)
    (hgates : ∀ index, oldRank index < oldBound → newRank (gates index) < newBound)
    (reference : Reference k G) (hbelow : reference.Below oldRank oldBound) :
    (reference.substitute inputs gates).Below newRank newBound := by
  cases reference with
  | constant value => trivial
  | literal atom =>
      cases hvalue : atom.value <;>
        simpa [substitute, hvalue, negate_below] using hinputs atom.index
  | gate index positive => exact hgates index hbelow

theorem below_map {n : ℕ} {G H : Type} (mapping : G → H) (oldRank : G → ℕ) (newRank : H → ℕ)
    (hmap : ∀ index, newRank (mapping index) = oldRank index) (bound : ℕ) (reference : Reference n G) :
    (reference.map mapping).Below newRank bound ↔ reference.Below oldRank bound := by
  cases reference <;> simp only [map, Below, hmap]

end Reference

def gateEval (conjunction : Bool) {arity : ℕ} (values : Fin arity → Bool) : Bool :=
  if conjunction then decide (∀ index, values index = true) else decide (∃ index, values index = true)

structure GateDescription (n : ℕ) (G : Type) where
  conjunction : Bool
  arity : ℕ
  inputs : Fin arity → Reference n G

namespace GateDescription

def eval {n : ℕ} {G : Type} (gate : GateDescription n G) (functions : G → ScalarFunction Bool n) :
    ScalarFunction Bool n := fun input => gateEval gate.conjunction (fun index => (gate.inputs index).eval functions input)

def restrict {n : ℕ} {G : Type} (gate : GateDescription n G) (rho : PartialAssignment n) : GateDescription n G :=
  ⟨gate.conjunction, gate.arity, fun index => (gate.inputs index).restrict rho⟩

theorem eval_restrict {n : ℕ} {G : Type} (gate : GateDescription n G)
    (rho : PartialAssignment n) (functions : G → ScalarFunction Bool n) :
    (gate.restrict rho).eval (fun index => ScalarFunction.restrict (functions index) rho) =
      ScalarFunction.restrict (gate.eval functions) rho := by
  funext input
  unfold eval restrict
  simp only [Reference.eval_restrict]
  rfl

def substitute {n k : ℕ} {G H : Type} (gate : GateDescription k G)
    (inputs : Fin k → Reference n H) (gates : G → H) : GateDescription n H :=
  ⟨gate.conjunction, gate.arity, fun argument => (gate.inputs argument).substitute inputs gates⟩

theorem eval_substitute {n k : ℕ} {G H : Type} (gate : GateDescription k G)
    (inputs : Fin k → Reference n H) (gates : G → H)
    (oldFunctions : G → ScalarFunction Bool k) (newFunctions : H → ScalarFunction Bool n)
    (oldInput : Bits k) (newInput : Bits n)
    (hinputs : ∀ index, (inputs index).eval newFunctions newInput = oldInput index)
    (hgates : ∀ index, newFunctions (gates index) newInput = oldFunctions index oldInput) :
    (gate.substitute inputs gates).eval newFunctions newInput = gate.eval oldFunctions oldInput := by
  unfold eval substitute
  congr 1
  funext argument
  exact Reference.eval_substitute inputs gates oldFunctions newFunctions oldInput newInput
    hinputs hgates (gate.inputs argument)

def map {n : ℕ} {G H : Type} (gate : GateDescription n G) (mapping : G → H) : GateDescription n H :=
  ⟨gate.conjunction, gate.arity, fun argument => (gate.inputs argument).map mapping⟩

theorem eval_map {n : ℕ} {G H : Type} (gate : GateDescription n G) (mapping : G → H)
    (oldFunctions : G → ScalarFunction Bool n) (newFunctions : H → ScalarFunction Bool n)
    (hmap : ∀ index, newFunctions (mapping index) = oldFunctions index) :
    (gate.map mapping).eval newFunctions = gate.eval oldFunctions := by
  have heq : newFunctions ∘ mapping = oldFunctions := funext hmap
  funext input
  simp only [eval, map, Reference.eval_map, heq]

end GateDescription

def disjoin {n arity : ℕ} (formulas : Fin arity → DNF n) : DNF n :=
  ⟨(List.ofFn fun index => (formulas index).terms).flatten⟩

theorem disjoin_eval {n arity : ℕ} (formulas : Fin arity → DNF n) (input : Bits n) :
    (disjoin formulas).eval input = decide (∃ index, (formulas index).eval input = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [DNF.eval_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨term, hterm, hsatisfied⟩
    obtain ⟨terms, hterms, hterm⟩ := List.mem_flatten.mp hterm
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hterms
    exact ⟨index, term, hterm, hsatisfied⟩
  · rintro ⟨index, term, hterm, hsatisfied⟩
    exact ⟨term, List.mem_flatten.mpr ⟨(formulas index).terms, List.mem_ofFn.mpr ⟨index, rfl⟩, hterm⟩,
      hsatisfied⟩

theorem disjoin_width {n arity : ℕ} (formulas : Fin arity → DNF n) (width : ℕ)
    (hwidth : ∀ index, (formulas index).WidthAtMost width) : (disjoin formulas).WidthAtMost width := by
  intro term hterm
  obtain ⟨terms, hterms, hterm⟩ := List.mem_flatten.mp hterm
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hterms
  exact hwidth index term hterm

def conjoin {n arity : ℕ} (formulas : Fin arity → CNF n) : CNF n :=
  (disjoin fun index => (formulas index).negate).negate

theorem conjoin_eval {n arity : ℕ} (formulas : Fin arity → CNF n) (input : Bits n) :
    (conjoin formulas).eval input = decide (∀ index, (formulas index).eval input = true) := by
  rw [conjoin, DNF.eval_negate, disjoin_eval]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, decide_eq_true_eq, not_exists,
    CNF.eval_negate, Bool.not_eq_true]
  simp

theorem conjoin_width {n arity : ℕ} (formulas : Fin arity → CNF n) (width : ℕ)
    (hwidth : ∀ index, (formulas index).WidthAtMost width) : (conjoin formulas).WidthAtMost width :=
  (disjoin_width _ width (fun index => (hwidth index).negate)).negate

/-- AND/OR of shallow functions has a bounded-width normal form of the matching polarity. -/
theorem normalForm_of_shallow_inputs {n arity : ℕ} (conjunction : Bool)
    (functions : Fin arity → ScalarFunction Bool n) (width : ℕ)
    (hdepth : ∀ index, DecisionTree.DepthAtMost (functions index) width) :
    ∃ formula : NormalForm n, formula.WidthAtMost width ∧
      ∀ input, formula.eval input = gateEval conjunction (fun index => functions index input) := by
  classical
  choose dnf cnf hdnf hcnf ednf ecnf using
    fun index => TalTreeNormalForm.normalForms_of_depthAtMost (functions index) width (hdepth index)
  cases conjunction with
  | false =>
      refine ⟨.dnf (disjoin dnf), disjoin_width dnf width hdnf, ?_⟩
      intro input
      simp only [NormalForm.eval, disjoin_eval, ednf, gateEval, Bool.false_eq_true, if_false]
  | true =>
      refine ⟨.cnf (conjoin cnf), conjoin_width cnf width hcnf, ?_⟩
      intro input
      simp only [NormalForm.eval, conjoin_eval, ecnf, gateEval, if_true]

structure Model (n : ℕ) (G : Type) (width : ℕ) where
  functions : G → ScalarFunction Bool n
  rank : G → ℕ
  bottom : ∀ index, rank index = 0 →
    ∃ formula : NormalForm n, formula.WidthAtMost width ∧ ∀ input, formula.eval input = functions index input
  upper : ∀ index, rank index ≠ 0 →
    ∃ gate : GateDescription n G,
      (∀ argument, (gate.inputs argument).Below rank (rank index)) ∧ gate.eval functions = functions index

theorem constant_depthAtMost {n : ℕ} (value : Bool) (width : ℕ) :
    DecisionTree.DepthAtMost (fun _ : Bits n => value) width := ⟨.leaf value, fun _ => rfl, Nat.zero_le _⟩

theorem literal_depthAtMost {n : ℕ} (literal : Literal n) (width : ℕ) (hwidth : 1 ≤ width) :
    DecisionTree.DepthAtMost literal.eval width := by
  refine ⟨.query literal.index (.leaf (!literal.value)) (.leaf literal.value), ?_, ?_⟩
  · intro input
    rw [TalShallowCircuit.literal_eval_value]
    cases hvalue : literal.value <;> cases hinput : input literal.index <;>
      simp [DecisionTree.eval, hvalue, hinput]
  · simpa only [DecisionTree.depth_query, DecisionTree.depth_leaf, Nat.max_self, Nat.succ_eq_add_one,
      Nat.zero_add] using hwidth

theorem reference_depthAtMost {n : ℕ} {G : Type} (functions : G → ScalarFunction Bool n)
    (rank : G → ℕ) (reference : Reference n G) (width : ℕ) (hwidth : 1 ≤ width)
    (hbelow : reference.Below rank 1)
    (hbottom : ∀ index, rank index = 0 → DecisionTree.DepthAtMost (functions index) width) :
    DecisionTree.DepthAtMost (reference.eval functions) width := by
  cases reference with
  | constant value => exact constant_depthAtMost value width
  | literal literal => exact literal_depthAtMost literal width hwidth
  | gate index positive =>
      have h := hbottom index (by change rank index < 1 at hbelow; omega)
      cases positive with
      | false => exact h.negate
      | true => exact h

theorem reference_below_pred {n : ℕ} {G : Type} (rank : G → ℕ) (bound : ℕ)
    (reference : Reference n G) (hbound : 1 < bound) (hbelow : reference.Below rank bound) :
    reference.Below (fun index => rank index - 1) (bound - 1) := by
  cases reference with
  | constant value => trivial
  | literal literal => trivial
  | gate index positive => change rank index - 1 < bound - 1; change rank index < bound at hbelow; omega

namespace Model

def reindex {n width : ℕ} {G H : Type} (model : Model n G width) (equivalence : G ≃ H) :
    Model n H width := by
  let functions := fun index => model.functions (equivalence.symm index)
  let rank := fun index => model.rank (equivalence.symm index)
  refine ⟨functions, rank, fun index => model.bottom (equivalence.symm index), ?_⟩
  intro index hrank
  obtain ⟨gate, hlower, heval⟩ := model.upper (equivalence.symm index) hrank
  refine ⟨gate.map equivalence, ?_, ?_⟩
  · intro argument
    exact (Reference.below_map equivalence model.rank rank
      (by intro source; simp only [rank, Equiv.symm_apply_apply]) _ _).mpr (hlower argument)
  · rw [GateDescription.eval_map gate equivalence model.functions functions
      (by intro source; simp only [functions, Equiv.symm_apply_apply]), heval]

def paddedFunctions {n width oldCount newCount : ℕ} (model : Model n (Fin oldCount) width)
    (index : Fin newCount) : ScalarFunction Bool n :=
  if h : index.val < oldCount then model.functions ⟨index.val, h⟩ else fun _ => true

def paddedRank {n width oldCount newCount : ℕ} (model : Model n (Fin oldCount) width)
    (index : Fin newCount) : ℕ :=
  if h : index.val < oldCount then model.rank ⟨index.val, h⟩ else 0

theorem paddedFunctions_castLE {n width oldCount newCount : ℕ} (model : Model n (Fin oldCount) width)
    (hcount : oldCount ≤ newCount) (index : Fin oldCount) :
    model.paddedFunctions (Fin.castLE hcount index) = model.functions index := by
  simp [paddedFunctions, index.isLt]

theorem paddedRank_castLE {n width oldCount newCount : ℕ} (model : Model n (Fin oldCount) width)
    (hcount : oldCount ≤ newCount) (index : Fin oldCount) :
    model.paddedRank (Fin.castLE hcount index) = model.rank index := by
  simp [paddedRank, index.isLt]

/-- Padding unused advice indices by constant functions does not add a research premise. -/
def pad {n width oldCount newCount : ℕ} (model : Model n (Fin oldCount) width)
    (hcount : oldCount ≤ newCount) : Model n (Fin newCount) width := by
  classical
  refine ⟨model.paddedFunctions, model.paddedRank, ?_, ?_⟩
  · intro index hrank
    by_cases hin : index.val < oldCount
    · simp only [paddedRank, dif_pos hin] at hrank
      simpa only [paddedFunctions, dif_pos hin] using model.bottom ⟨index.val, hin⟩ hrank
    · refine ⟨.dnf .top, ?_, ?_⟩
      · intro term hterm
        simp only [DNF.top, List.mem_singleton] at hterm
        subst term
        simpa only [LiteralSet.width_empty] using Nat.zero_le width
      · intro input
        simp [NormalForm.eval, paddedFunctions, hin]
  · intro index hrank
    have hin : index.val < oldCount := by
      by_contra h
      exact hrank (by simp [paddedRank, h])
    have hindex : Fin.castLE hcount (⟨index.val, hin⟩ : Fin oldCount) = index := rfl
    have hsourceRank : model.rank ⟨index.val, hin⟩ ≠ 0 := by
      simpa only [paddedRank, dif_pos hin] using hrank
    obtain ⟨gate, hlower, heval⟩ := model.upper ⟨index.val, hin⟩ hsourceRank
    refine ⟨gate.map (Fin.castLE hcount), ?_, ?_⟩
    · intro argument
      rw [← hindex, paddedRank_castLE]
      exact (Reference.below_map (Fin.castLE hcount) model.rank model.paddedRank
        (paddedRank_castLE model hcount) _ _).mpr (hlower argument)
    · rw [GateDescription.eval_map gate (Fin.castLE hcount) model.functions model.paddedFunctions
        (paddedFunctions_castLE model hcount), heval]
      exact (paddedFunctions_castLE model hcount ⟨index.val, hin⟩).symm

theorem pad_rank_bound {n width oldCount newCount bound : ℕ} (model : Model n (Fin oldCount) width)
    (hcount : oldCount ≤ newCount) (hbound : ∀ index, model.rank index ≤ bound) :
    ∀ index, (model.pad hcount).rank index ≤ bound := by
  intro index
  change model.paddedRank index ≤ bound
  unfold paddedRank
  split_ifs with hin
  · exact hbound _
  · exact Nat.zero_le _

/-- The actual one-rank depth reduction after every bottom function becomes shallow. -/
def lower {n : ℕ} {G : Type} {width : ℕ} (model : Model n G width)
    (rho : PartialAssignment n) (shallow : ℕ) (hshallow : 1 ≤ shallow)
    (hbottom : ∀ index, model.rank index = 0 →
      DecisionTree.DepthAtMost (ScalarFunction.restrict (model.functions index) rho) shallow) :
    Model n G shallow := by
  classical
  let functions := fun index => ScalarFunction.restrict (model.functions index) rho
  refine ⟨functions, fun index => model.rank index - 1, ?_, ?_⟩
  · intro index hrank
    change model.rank index - 1 = 0 at hrank
    have hrank' : model.rank index ≤ 1 := by omega
    by_cases hzero : model.rank index = 0
    · obtain ⟨dnf, cnf, hdnf, _, ednf, _⟩ :=
        TalTreeNormalForm.normalForms_of_depthAtMost _ shallow (hbottom index hzero)
      exact ⟨.dnf dnf, hdnf, ednf⟩
    · have hone : model.rank index = 1 := by omega
      obtain ⟨gate, hlower, heval⟩ := model.upper index hzero
      have hinputs : ∀ argument, DecisionTree.DepthAtMost
          ((gate.inputs argument).restrict rho |>.eval functions) shallow := by
        intro argument
        apply reference_depthAtMost functions model.rank _ shallow hshallow
        · apply Reference.restrict_below
          simpa only [hone] using hlower argument
        · exact hbottom
      obtain ⟨formula, hwidth, hformula⟩ := normalForm_of_shallow_inputs gate.conjunction
        (fun argument => ((gate.inputs argument).restrict rho).eval functions) shallow hinputs
      refine ⟨formula, hwidth, ?_⟩
      intro input
      have hgate := congrFun (gate.eval_restrict rho model.functions) input
      rw [heval] at hgate
      exact (hformula input).trans hgate
  · intro index hrank
    change model.rank index - 1 ≠ 0 at hrank
    have hlarge : 1 < model.rank index := by omega
    obtain ⟨gate, hlower, heval⟩ := model.upper index (by omega)
    refine ⟨gate.restrict rho, ?_, ?_⟩
    · intro argument
      exact reference_below_pred model.rank _ _ hlarge
        (Reference.restrict_below rho model.rank _ _ (hlower argument))
    · rw [GateDescription.eval_restrict, heval]

theorem lower_functions {n : ℕ} {G : Type} {width : ℕ} (model : Model n G width)
    (rho : PartialAssignment n) (shallow : ℕ) (hshallow : 1 ≤ shallow)
    (hbottom : ∀ index, model.rank index = 0 →
      DecisionTree.DepthAtMost (ScalarFunction.restrict (model.functions index) rho) shallow) :
    (model.lower rho shallow hshallow hbottom).functions =
      fun index => ScalarFunction.restrict (model.functions index) rho := rfl

theorem lower_rank {n : ℕ} {G : Type} {width : ℕ} (model : Model n G width)
    (rho : PartialAssignment n) (shallow : ℕ) (hshallow : 1 ≤ shallow)
    (hbottom : ∀ index, model.rank index = 0 →
      DecisionTree.DepthAtMost (ScalarFunction.restrict (model.functions index) rho) shallow) :
    (model.lower rho shallow hshallow hbottom).rank = fun index => model.rank index - 1 := rfl

end Model

end TalGateNetwork
