import TalSignedCircuit
import TalMixedSwitching

/-!
# The exact Tal theorem for depth at most one

This proves the shallow circuit base directly for the original shared-gate
syntax. It does not assume the general Tal theorem or a circuit-normalization
certificate. The higher-depth layer/cut reduction is a separate obligation.
-/

namespace TalMixedSwitching.NormalForm
open Algebraic AC0

def negate {n : ℕ} : NormalForm n → NormalForm n
  | .dnf formula => .cnf formula.negate
  | .cnf formula => .dnf formula.negate

theorem eval_negate {n : ℕ} (formula : NormalForm n) (input : Fin n → Bool) :
    formula.negate.eval input = !formula.eval input := by
  cases formula <;> simp [negate, eval]

theorem WidthAtMost.negate {n : ℕ} {formula : NormalForm n} {width : ℕ}
    (hwidth : formula.WidthAtMost width) : formula.negate.WidthAtMost width := by
  cases formula with
  | dnf formula => exact DNF.WidthAtMost.negate (show formula.WidthAtMost width from hwidth)
  | cnf formula => exact CNF.WidthAtMost.negate (show formula.WidthAtMost width from hwidth)

end TalMixedSwitching.NormalForm

namespace TalShallowCircuit
open TransformerAC0 Algebraic AC0 TalMixedSwitching
open TalSignedCircuit

theorem literal_eval_value {n : ℕ} (literal : Literal n) (input : Bits n) :
    literal.eval input = if literal.value then input literal.index else !(input literal.index) := by
  cases hvalue : literal.value <;> cases hbit : input literal.index <;>
    simp [Literal.eval, hvalue, hbit]

theorem singleton_eval {n : ℕ} (literal : Literal n) (input : Bits n) :
    Term.eval (LiteralSet.singleton literal) input = literal.eval input := by
  apply Bool.eq_iff_iff.mpr
  rw [Term.eval_eq_true, Literal.eval_eq_true]
  constructor
  · intro h
    exact h literal.index literal.value (PartialAssignment.fix_selected _ _)
  · intro h index value hrequired
    by_cases heq : index = literal.index
    · subst index
      have hvalue : literal.value = value := by
        simpa [LiteralSet.singleton] using hrequired
      exact h.trans hvalue
    · simp [LiteralSet.singleton, PartialAssignment.fix, heq] at hrequired

def orLiterals {n arity : ℕ} (routing : Fin arity → Literal n) : DNF n :=
  ⟨List.ofFn fun index => LiteralSet.singleton (routing index)⟩

theorem orLiterals_eval_eq_true {n arity : ℕ} (routing : Fin arity → Literal n) (input : Bits n) :
    (orLiterals routing).eval input = true ↔ ∃ index, (routing index).eval input = true := by
  rw [DNF.eval_eq_true]
  constructor
  · rintro ⟨term, hterm, hsatisfied⟩
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hterm
    exact ⟨index, (singleton_eval _ input) ▸ (Term.eval_eq_true _ input).mpr hsatisfied⟩
  · rintro ⟨index, hindex⟩
    refine ⟨LiteralSet.singleton (routing index), List.mem_ofFn.mpr ⟨index, rfl⟩, ?_⟩
    apply (Term.eval_eq_true _ input).mp
    rw [singleton_eval]
    exact hindex

theorem orLiterals_eval {n arity : ℕ} (routing : Fin arity → Literal n) (input : Bits n) :
    (orLiterals routing).eval input = decide (∃ index, (routing index).eval input = true) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using orLiterals_eval_eq_true routing input

theorem orLiterals_width {n arity : ℕ} (routing : Fin arity → Literal n) :
    (orLiterals routing).WidthAtMost 1 := by
  intro term hterm
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hterm
  simp [LiteralSet.width, LiteralSet.support, LiteralSet.singleton,
    PartialAssignment.fixedVariables_fix]

def andLiterals {n arity : ℕ} (routing : Fin arity → Literal n) : CNF n :=
  (orLiterals fun index => (routing index).negate).negate

theorem andLiterals_eval {n arity : ℕ} (routing : Fin arity → Literal n) (input : Bits n) :
    (andLiterals routing).eval input = decide (∀ index, (routing index).eval input = true) := by
  rw [andLiterals, DNF.eval_negate, orLiterals_eval]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, decide_eq_true_eq, not_exists,
    Literal.eval_negate, Bool.not_eq_true]
  simp

theorem andLiterals_width {n arity : ℕ} (routing : Fin arity → Literal n) :
    (andLiterals routing).WidthAtMost 1 := (orLiterals_width _).negate

theorem normalForm_of_depth_le_one {n m source : ℕ} (circuit : TalSignedCircuit.Circuit n m)
    (hdepth : circuit.depth ≤ 1) (routing : Fin n → Literal source) (output : Fin m) :
    ∃ formula : NormalForm source, formula.WidthAtMost 1 ∧
      ∀ input, formula.eval input = circuit.eval (fun index => (routing index).eval input) output := by
  induction circuit generalizing source with
  | wire wires =>
      let literal := substituteLiteral (wires output) routing
      refine ⟨.dnf (orLiterals (fun _ : Fin 1 => literal)), orLiterals_width _, ?_⟩
      intro input
      simp only [NormalForm.eval, orLiterals_eval]
      simp only [Fin.exists_fin_one]
      simp only [Bool.decide_eq_true]
      simpa only [literal, TalSignedCircuit.Circuit.eval] using substituteLiteral_eval (wires output) routing input
  | andGate arity => exact ⟨.cnf (andLiterals routing), andLiterals_width _, andLiterals_eval routing⟩
  | orGate arity => exact ⟨.dnf (orLiterals routing), orLiterals_width _, orLiterals_eval routing⟩
  | seq first second ihfirst ihsecond =>
      by_cases hfirstDepth : first.depth = 0
      · obtain ⟨firstRouting, hfirst⟩ := exists_routing_of_depth_zero first hfirstDepth
        let composed := fun index => substituteLiteral (firstRouting index) routing
        obtain ⟨formula, hwidth, hformula⟩ := ihsecond (by change first.depth + second.depth ≤ 1 at hdepth; omega)
          composed output
        refine ⟨formula, hwidth, ?_⟩
        intro input
        have hinputs : first.eval (fun index => (routing index).eval input) =
            fun index => (composed index).eval input := by
          rw [hfirst]
          funext index
          exact (substituteLiteral_eval _ routing input).symm
        change formula.eval input = second.eval (first.eval _) output
        rw [hinputs]
        exact hformula input
      · have hsecondDepth : second.depth = 0 := by
          change first.depth + second.depth ≤ 1 at hdepth
          omega
        obtain ⟨secondRouting, hsecond⟩ := exists_routing_of_depth_zero second hsecondDepth
        obtain ⟨formula, hwidth, hformula⟩ := ihfirst (by change first.depth + second.depth ≤ 1 at hdepth; omega)
          routing (secondRouting output).index
        cases hvalue : (secondRouting output).value with
        | false =>
            refine ⟨formula.negate, hwidth.negate, ?_⟩
            intro input
            simp only [NormalForm.eval_negate, hformula, TalSignedCircuit.Circuit.eval, hsecond]
            rw [literal_eval_value, hvalue]
            rfl
        | true =>
            refine ⟨formula, hwidth, ?_⟩
            intro input
            simp only [hformula, TalSignedCircuit.Circuit.eval, hsecond]
            rw [literal_eval_value, hvalue]
            rfl
  | parallel left right ihleft ihright =>
      have hleft : left.depth ≤ 1 := (Nat.le_max_left _ _).trans hdepth
      have hright : right.depth ≤ 1 := (Nat.le_max_right _ _).trans hdepth
      refine Fin.addCases ?_ ?_ output
      · intro index
        obtain ⟨formula, hwidth, hformula⟩ := ihleft hleft routing index
        exact ⟨formula, hwidth, fun input => by simpa only [TalSignedCircuit.Circuit.eval, Fin.append_left] using hformula input⟩
      · intro index
        obtain ⟨formula, hwidth, hformula⟩ := ihright hright routing index
        exact ⟨formula, hwidth, fun input => by simpa only [TalSignedCircuit.Circuit.eval, Fin.append_right] using hformula input⟩
  | bundle branch ih =>
      have hbranch : (branch output).depth ≤ 1 :=
        (Finset.le_sup (f := fun index => (branch index).depth) (Finset.mem_univ output)).trans hdepth
      exact ih output hbranch routing 0

/-- The depth-one circuit base in the original exact statement, with no imported Tal premise. -/
theorem shallow_tailBound {n : ℕ} (circuit : TransformerAC0.Circuit n 1) (size degree : ℕ)
    (hdepth : circuit.depth ≤ 1) :
    Tal.tailWeight (Tal.circuitSign circuit) degree ≤ Tal.tailBound 1 size degree := by
  let routing : Fin n → Literal n := fun index => ⟨index, true⟩
  obtain ⟨formula, hwidth, hformula⟩ := normalForm_of_depth_le_one (compile circuit)
    ((compile_depth_le circuit).trans hdepth) routing 0
  have hinput (input : Bits n) : (fun index => (routing index).eval input) = input := by
    funext index
    cases hbit : input index <;> simp [routing, Literal.eval, hbit]
  have heval : Tal.circuitSign circuit = fun input => Tal.boolSign (formula.eval input) := by
    funext input
    unfold Tal.circuitSign
    rw [hformula, hinput, compile_eval]
  rw [heval]
  have hraw : Tal.tailWeight (fun input => Tal.boolSign (formula.eval input)) degree ≤
      16 * (2 : ℝ) ^ (-(degree : ℝ) / 20) := by
    cases formula with
    | dnf formula => simpa only [NormalForm.eval, Nat.cast_one, mul_one] using TalSwitching.dnf_tailWeight_le formula 1 degree hwidth (by decide)
    | cnf formula => simpa only [NormalForm.eval, Nat.cast_one, mul_one] using TalSwitching.cnf_tailWeight_le formula 1 degree hwidth (by decide)
  have hexponential : (16 : ℝ) * 2 ^ (-(degree : ℝ) / 20) =
      (2 : ℝ) ^ (4 - (degree : ℝ) / 20) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    congr 1
    rw [neg_div]
  rw [hexponential] at hraw
  have h := TalNumerics.absorb_prefactor (TalRestriction.tailWeight_nonneg _ _)
    (TalRestriction.tailWeight_le_one_of_sign formula.eval degree) (by norm_num : (1 : ℝ) ≤ 4) hraw
  have hdegree : (0 : ℝ) ≤ degree := Nat.cast_nonneg degree
  calc
    _ ≤ (2 : ℝ) ^ (1 - (degree : ℝ) / 80) := by norm_num only [div_div] at h; exact h
    _ ≤ (2 : ℝ) ^ (1 - (degree : ℝ) / 216) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = Tal.tailBound 1 size degree := by
      simp only [Tal.tailBound, Nat.sub_self, pow_zero, pow_one, mul_one]
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      congr 1
      rw [neg_div]

/-- Both shallow cases of the exact theorem, including an overestimated DSL depth bound. -/
theorem tailWeight_le_of_depth_le_one {n : ℕ} (circuit : TransformerAC0.Circuit n 1)
    (depth size degree : ℕ) (hdepth : circuit.depth ≤ depth) (hshallow : depth ≤ 1) :
    Tal.tailWeight (Tal.circuitSign circuit) degree ≤ Tal.tailBound depth size degree := by
  interval_cases depth
  · exact zero_depth_tailBound circuit size degree (Nat.eq_zero_of_le_zero hdepth)
  · exact shallow_tailBound circuit size degree hdepth

end TalShallowCircuit
