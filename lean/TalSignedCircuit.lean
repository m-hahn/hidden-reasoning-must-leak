import TransformerAC0
import Complexitylib.Algebraic.LowerBound.AC0.NormalForm
import TalDecisionTree

/-!
# Eliminating NOT gates without duplicating shared gates

Signed free wiring replaces every NOT gate. Serial composition, parallel
composition, and finite bundles retain their shared-intermediate-wire
semantics. Thus this construction does not unfold a DAG into a formula or
create a second gate for every complementary view of an output.

This is the negation-elimination part of the normalization bridge. It is not
yet the layered bottom-fan-in normalization or Tal's circuit-depth induction.
-/

namespace TalSignedCircuit
open TransformerAC0

inductive Circuit : ℕ → ℕ → Type
  | wire {n m : ℕ} (routing : Fin m → Algebraic.AC0.Literal n) : Circuit n m
  | andGate (fanin : ℕ) : Circuit fanin 1
  | orGate (fanin : ℕ) : Circuit fanin 1
  | seq {n m k : ℕ} (first : Circuit n m) (second : Circuit m k) : Circuit n k
  | parallel {n m k : ℕ} (left : Circuit n m) (right : Circuit n k) : Circuit n (m + k)
  | bundle {n m : ℕ} (branch : Fin m → Circuit n 1) : Circuit n m

namespace Circuit

def eval : {n m : ℕ} → Circuit n m → Bits n → Bits m
  | _, _, .wire routing, input => fun index => (routing index).eval input
  | _, _, .andGate _, input => fun _ => decide (∀ index, input index = true)
  | _, _, .orGate _, input => fun _ => decide (∃ index, input index = true)
  | _, _, .seq first second, input => second.eval (first.eval input)
  | _, _, .parallel left right, input => Fin.append (left.eval input) (right.eval input)
  | _, _, .bundle branch, input => fun index => (branch index).eval input 0

def depth : {n m : ℕ} → Circuit n m → ℕ
  | _, _, .wire _ => 0
  | _, _, .andGate _ => 1
  | _, _, .orGate _ => 1
  | _, _, .seq first second => first.depth + second.depth
  | _, _, .parallel left right => max left.depth right.depth
  | _, _, .bundle branch => Finset.univ.sup fun index => (branch index).depth

def gateCount : {n m : ℕ} → Circuit n m → ℕ
  | _, _, .wire _ => 0
  | _, _, .andGate _ => 1
  | _, _, .orGate _ => 1
  | _, _, .seq first second => first.gateCount + second.gateCount
  | _, _, .parallel left right => left.gateCount + right.gateCount
  | _, _, .bundle branch => ∑ index, (branch index).gateCount

end Circuit

def compile : {n m : ℕ} → TransformerAC0.Circuit n m → Circuit n m
  | _, _, .wire routing => .wire fun index => ⟨routing index, true⟩
  | _, _, .notGate => .wire fun _ => ⟨0, false⟩
  | _, _, .andGate fanin => .andGate fanin
  | _, _, .orGate fanin => .orGate fanin
  | _, _, .seq first second => .seq (compile first) (compile second)
  | _, _, .parallel left right => .parallel (compile left) (compile right)
  | _, _, .bundle branch => .bundle fun index => compile (branch index)

theorem compile_eval {n m : ℕ} (circuit : TransformerAC0.Circuit n m) (input : Bits n) :
    (compile circuit).eval input = circuit.eval input := by
  induction circuit with
  | wire routing =>
      funext index
      cases input (routing index) <;> simp [compile, Circuit.eval, TransformerAC0.Circuit.eval,
        Algebraic.AC0.Literal.eval]
  | notGate =>
      funext index
      cases input 0 <;> simp [compile, Circuit.eval, TransformerAC0.Circuit.eval,
        Algebraic.AC0.Literal.eval]
  | andGate fanin => rfl
  | orGate fanin => rfl
  | seq first second ihfirst ihsecond =>
      simp only [compile, Circuit.eval, TransformerAC0.Circuit.eval, ihfirst, ihsecond]
  | parallel left right ihleft ihright =>
      simp only [compile, Circuit.eval, TransformerAC0.Circuit.eval, ihleft, ihright]
  | bundle branch ih =>
      funext index
      exact congrFun (ih index input) 0

theorem compile_depth_le {n m : ℕ} (circuit : TransformerAC0.Circuit n m) :
    (compile circuit).depth ≤ circuit.depth := by
  induction circuit with
  | wire routing => rfl
  | notGate => decide
  | andGate fanin => rfl
  | orGate fanin => rfl
  | seq first second ihfirst ihsecond => exact Nat.add_le_add ihfirst ihsecond
  | parallel left right ihleft ihright => exact max_le_max ihleft ihright
  | bundle branch ih =>
      apply Finset.sup_le
      intro index hindex
      exact (ih index).trans (Finset.le_sup (f := fun index => (branch index).depth) hindex)

theorem compile_gateCount_le {n m : ℕ} (circuit : TransformerAC0.Circuit n m) :
    (compile circuit).gateCount ≤ circuit.gateCount := by
  induction circuit with
  | wire routing => rfl
  | notGate => decide
  | andGate fanin => rfl
  | orGate fanin => rfl
  | seq first second ihfirst ihsecond => exact Nat.add_le_add ihfirst ihsecond
  | parallel left right ihleft ihright => exact Nat.add_le_add ihleft ihright
  | bundle branch ih => exact Finset.sum_le_sum fun index _ => ih index

/-- Gate overhead is exactly zero; the bound uses the original gate budget. -/
theorem exists_signedCircuit {n m : ℕ} (circuit : TransformerAC0.Circuit n m) :
    ∃ signedCircuit : Circuit n m,
      (∀ input, signedCircuit.eval input = circuit.eval input) ∧
        signedCircuit.depth ≤ circuit.depth ∧ signedCircuit.gateCount ≤ circuit.gateCount :=
  ⟨compile circuit, compile_eval circuit, compile_depth_le circuit, compile_gateCount_le circuit⟩

def substituteLiteral {n m : ℕ} (literal : Algebraic.AC0.Literal m)
    (routing : Fin m → Algebraic.AC0.Literal n) : Algebraic.AC0.Literal n :=
  if literal.value then routing literal.index else (routing literal.index).negate

theorem substituteLiteral_eval {n m : ℕ} (literal : Algebraic.AC0.Literal m)
    (routing : Fin m → Algebraic.AC0.Literal n) (input : Bits n) :
    (substituteLiteral literal routing).eval input =
      literal.eval (fun index => (routing index).eval input) := by
  cases hvalue : literal.value <;>
    simp only [substituteLiteral, hvalue, Bool.false_eq_true, if_false, if_true,
      Algebraic.AC0.Literal.eval_negate] <;>
    cases hinput : (routing literal.index).eval input <;>
    simp_all [Algebraic.AC0.Literal.eval]

/-- Zero-depth signed circuits are free literal routing, even through serial and bundled DAGs. -/
theorem exists_routing_of_depth_zero {n m : ℕ} (circuit : Circuit n m) (hdepth : circuit.depth = 0) :
    ∃ routing : Fin m → Algebraic.AC0.Literal n,
      ∀ input, circuit.eval input = fun index => (routing index).eval input := by
  induction circuit with
  | wire routing => exact ⟨routing, fun _ => rfl⟩
  | andGate fanin => simp [Circuit.depth] at hdepth
  | orGate fanin => simp [Circuit.depth] at hdepth
  | seq first second ihfirst ihsecond =>
      obtain ⟨hfirstDepth, hsecondDepth⟩ := Nat.add_eq_zero.mp hdepth
      obtain ⟨firstRouting, hfirst⟩ := ihfirst hfirstDepth
      obtain ⟨secondRouting, hsecond⟩ := ihsecond hsecondDepth
      refine ⟨fun index => substituteLiteral (secondRouting index) firstRouting, ?_⟩
      intro input
      funext index
      simp only [Circuit.eval, hsecond, hfirst, substituteLiteral_eval]
  | parallel left right ihleft ihright =>
      have hleftDepth : left.depth = 0 := Nat.eq_zero_of_le_zero
        ((Nat.le_max_left _ _).trans (le_of_eq hdepth))
      have hrightDepth : right.depth = 0 := Nat.eq_zero_of_le_zero
        ((Nat.le_max_right _ _).trans (le_of_eq hdepth))
      obtain ⟨leftRouting, hleft⟩ := ihleft hleftDepth
      obtain ⟨rightRouting, hright⟩ := ihright hrightDepth
      refine ⟨Fin.append leftRouting rightRouting, ?_⟩
      intro input
      funext index
      refine Fin.addCases ?_ ?_ index <;> intro index <;>
        simp only [Circuit.eval, hleft, hright, Fin.append_left, Fin.append_right]
  | bundle branch ih =>
      have heach (index) : (branch index).depth = 0 := Nat.eq_zero_of_le_zero
        ((Finset.le_sup (f := fun index => (branch index).depth) (Finset.mem_univ index)).trans
          (le_of_eq hdepth))
      choose routing hrouting using fun index => ih index (heach index)
      refine ⟨fun index => routing index 0, ?_⟩
      intro input
      funext index
      exact congrFun (hrouting index input) 0

theorem literal_tailWeight_eq_zero {n : ℕ} (literal : Algebraic.AC0.Literal n) (degree : ℕ)
    (hdegree : 1 < degree) :
    Tal.tailWeight (fun input => Tal.boolSign (literal.eval input)) degree = 0 := by
  apply TalDecisionTree.tailWeight_eq_zero_of_depthAtMost _ 1 degree _ hdegree
  refine ⟨.query literal.index (.leaf (!literal.value)) (.leaf literal.value), ?_, by simp⟩
  intro input
  cases hvalue : literal.value <;> cases hinput : input literal.index <;>
    simp [Algebraic.AC0.DecisionTree.eval, Algebraic.AC0.Literal.eval, hvalue, hinput]

/-- The exact displayed Tal bound at circuit depth zero, with no Tal premise. -/
theorem zero_depth_tailBound {n : ℕ} (circuit : TransformerAC0.Circuit n 1)
    (size degree : ℕ) (hdepth : circuit.depth = 0) :
    Tal.tailWeight (Tal.circuitSign circuit) degree ≤ Tal.tailBound 0 size degree := by
  have hsignedDepth : (compile circuit).depth = 0 := Nat.eq_zero_of_le_zero
    ((compile_depth_le circuit).trans (le_of_eq hdepth))
  obtain ⟨routing, hrouting⟩ := exists_routing_of_depth_zero (compile circuit) hsignedDepth
  have heval : Tal.circuitSign circuit = fun input => Tal.boolSign ((routing 0).eval input) := by
    funext input
    unfold Tal.circuitSign
    rw [← compile_eval, hrouting]
  rw [heval]
  by_cases hdegree : 1 < degree
  · rw [literal_tailWeight_eq_zero _ degree hdegree]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  · have hbound := TalRestriction.tailWeight_le_one_of_sign (routing 0).eval degree
    interval_cases degree <;> simp [Tal.tailBound, Real.rpow_neg_one] <;> linarith

end TalSignedCircuit
