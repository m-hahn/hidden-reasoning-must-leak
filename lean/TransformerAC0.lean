import Mathlib
import OrderedAddition

/-!
# Fixed-precision Transformers compile to polynomial-size AC⁰ circuits

This file formalizes the translation lemma in the paper appendix.  There are
four deliberately separate ingredients.

* `Circuit` is an explicit language of unbounded-fanin AND/OR/NOT circuits.
  Serial composition shares intermediate wires, so its gate count is
  additive rather than the size of an inlined formula.
* `Circuit.ofPredicate` constructs the depth-three truth-table circuits used
  for every fixed-arity operation: rounding, multiplication, exponentiation,
  division, and ReLU.
* `StarFree.compile` constructs the constant-depth polynomial-size circuit
  for a rounded iterated sum.  It handles union, intersection, complement,
  and concatenation explicitly and proves correctness, depth, and size.
* `FixedPrecisionTransformer.compile` connects explicit embedding,
  attention, softmax, residual-rounding, ReLU/MLP, and readout programs.
  No circuit-realization hypothesis occurs in the translation theorem.

The precision is fixed globally in the paper, so the constant number of bits
used to encode one fixed-precision scalar is absorbed in the constants of the
star-free arithmetic programs derived from the ordered rounded-add automaton.
-/

open scoped BigOperators

namespace TransformerAC0

/-! ## Unbounded-fanin Boolean circuits -/

/-- A bundle of `n` Boolean wires. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/--
An explicit circuit language with free fanout and rewiring.  `andGate` and
`orGate` have arbitrary finite fanin.  In `first ≫ second`, the output wires
of `first` are shared inputs of `second`; the syntax therefore represents
circuits (DAGs), not expanded Boolean formulas.
-/
inductive Circuit : ℕ → ℕ → Type
  | wire {n m : ℕ} (routing : Fin m → Fin n) : Circuit n m
  | notGate : Circuit 1 1
  | andGate (fanin : ℕ) : Circuit fanin 1
  | orGate (fanin : ℕ) : Circuit fanin 1
  | seq {n m k : ℕ} (first : Circuit n m) (second : Circuit m k) : Circuit n k
  | parallel {n m k : ℕ} (left : Circuit n m) (right : Circuit n k) :
      Circuit n (m + k)
  /-- A finite bundle of one-output branches.  This is a DAG-level parallel
  composition macro; it introduces no gates of its own. -/
  | bundle {n m : ℕ} (branch : Fin m → Circuit n 1) : Circuit n m

namespace Circuit

/-- The Boolean function denoted by a circuit. -/
def eval : {n m : ℕ} → Circuit n m → Bits n → Bits m
  | _, _, .wire routing, input => fun j => input (routing j)
  | _, _, .notGate, input => fun _ => !(input 0)
  | _, _, .andGate _, input => fun _ => decide (∀ i, input i = true)
  | _, _, .orGate _, input => fun _ => decide (∃ i, input i = true)
  | _, _, .seq first second, input => eval second (eval first input)
  | _, _, .parallel left right, input => Fin.append (eval left input) (eval right input)
  | _, _, .bundle branch, input => fun j => eval (branch j) input 0

/-- Circuit depth.  Rewiring is free, and parallel branches run together. -/
def depth : {n m : ℕ} → Circuit n m → ℕ
  | _, _, .wire _ => 0
  | _, _, .notGate => 1
  | _, _, .andGate _ => 1
  | _, _, .orGate _ => 1
  | _, _, .seq first second => depth first + depth second
  | _, _, .parallel left right => max (depth left) (depth right)
  | _, _, .bundle branch => Finset.univ.sup fun j => depth (branch j)

/-- Number of AND, OR, and NOT gates; wires and fanout are free. -/
def gateCount : {n m : ℕ} → Circuit n m → ℕ
  | _, _, .wire _ => 0
  | _, _, .notGate => 1
  | _, _, .andGate _ => 1
  | _, _, .orGate _ => 1
  | _, _, .seq first second => gateCount first + gateCount second
  | _, _, .parallel left right => gateCount left + gateCount right
  | _, _, .bundle branch => ∑ j, gateCount (branch j)

/-- Identity wiring. -/
def id (n : ℕ) : Circuit n n := .wire _root_.id

/-- Serially connect a list of equal-width circuits. -/
def serial {n : ℕ} : List (Circuit n n) → Circuit n n
  | [] => id n
  | circuit :: rest => .seq circuit (serial rest)

/-- Execute a list of equal-width circuits in order. -/
def runSerial {n : ℕ} (circuits : List (Circuit n n)) (input : Bits n) : Bits n :=
  circuits.foldl (fun state circuit => eval circuit state) input

@[simp] theorem eval_id {n : ℕ} (input : Bits n) : eval (id n) input = input := rfl

@[simp] theorem eval_serial {n : ℕ} (circuits : List (Circuit n n)) (input : Bits n) :
    eval (serial circuits) input = runSerial circuits input := by
  induction circuits generalizing input with
  | nil => rfl
  | cons circuit rest ih =>
      simp only [serial, eval, runSerial, List.foldl_cons]
      exact ih (eval circuit input)

@[simp] theorem depth_serial {n : ℕ} (circuits : List (Circuit n n)) :
    depth (serial circuits) = (circuits.map depth).sum := by
  induction circuits with
  | nil => rfl
  | cons circuit rest ih => simp [serial, depth, ih]

@[simp] theorem gateCount_serial {n : ℕ} (circuits : List (Circuit n n)) :
    gateCount (serial circuits) = (circuits.map gateCount).sum := by
  induction circuits with
  | nil => rfl
  | cons circuit rest ih => simp [serial, gateCount, ih]

/-! ### Derived circuit constructors -/

/-- A Boolean constant, using the empty AND for `true` and empty OR for
`false`. -/
def const (n : ℕ) (value : Bool) : Circuit n 1 :=
  .seq (.wire Fin.elim0) (if value then .andGate 0 else .orGate 0)

@[simp] theorem eval_const (n : ℕ) (value : Bool) (input : Bits n) :
    eval (const n value) input 0 = value := by
  cases value <;> simp [const, eval]

/-- Reindex the inputs of a circuit; this is only free wiring. -/
def reinput (routing : Fin n → Fin m) (circuit : Circuit n k) : Circuit m k :=
  .seq (.wire routing) circuit

@[simp] theorem eval_reinput (routing : Fin n → Fin m) (circuit : Circuit n k)
    (input : Bits m) :
    eval (reinput routing circuit) input = eval circuit (fun i => input (routing i)) := rfl

@[simp] theorem depth_reinput (routing : Fin n → Fin m) (circuit : Circuit n k) :
    depth (reinput routing circuit) = depth circuit := by simp [reinput, depth]

@[simp] theorem gateCount_reinput (routing : Fin n → Fin m) (circuit : Circuit n k) :
    gateCount (reinput routing circuit) = gateCount circuit := by simp [reinput, gateCount]

/-- Pointwise literals saying that the input equals `assignment`. -/
def literals : (n : ℕ) → Bits n → Circuit n n
  | 0, _ => .wire Fin.elim0
  | n + 1, assignment =>
      let initial : Circuit (n + 1) n :=
        .seq (.wire Fin.castSucc) (literals n (fun i => assignment i.castSucc))
      let final : Circuit (n + 1) 1 :=
        .seq (.wire (fun _ => Fin.last n))
          (if assignment (Fin.last n) then id 1 else .notGate)
      .parallel initial final

@[simp] theorem eval_literals (n : ℕ) (assignment input : Bits n) :
    eval (literals n assignment) input = fun i => (input i == assignment i) := by
  funext i
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · cases h : assignment (Fin.last n) <;> cases h' : input (Fin.last n) <;>
          simp [literals, eval, id, h, h', Fin.append_right_eq_snoc]
      · simpa [literals, eval, Fin.append_right_eq_snoc] using
          ih (fun k => assignment k.castSucc) (fun k => input k.castSucc) j

/-- A conjunction which recognizes one complete input assignment. -/
def matchInput (assignment : Bits n) : Circuit n 1 :=
  .seq (literals n assignment) (.andGate n)

theorem depth_literals_le_one (assignment : Bits n) :
    depth (literals n assignment) ≤ 1 := by
  induction n with
  | zero => simp [literals, depth]
  | succ n ih =>
      simp only [literals, depth]
      apply max_le
      · simpa using ih (fun i => assignment i.castSucc)
      · split <;> simp [id, depth]

@[simp] theorem eval_matchInput (assignment input : Bits n) :
    eval (matchInput assignment) input 0 = decide (input = assignment) := by
  simp only [matchInput, eval, eval_literals]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have hi := h i
    simpa using hi
  · intro h i
    rw [h]
    simp

private noncomputable def assignmentAt (n : ℕ)
    (i : Fin (Fintype.card (Bits n))) : Bits n :=
  (Fintype.equivFin (Bits n)).symm i

/-- The depth-three DNF circuit for a fixed finite-arity Boolean predicate.
It is used below for rounding, multiplication, exponentiation, division, and
ReLU, whose arities are constant because precision is fixed. -/
noncomputable def ofPredicate (predicate : Bits n → Bool) : Circuit n 1 :=
  .seq
    (.bundle fun i : Fin (Fintype.card (Bits n)) =>
      let assignment := assignmentAt n i
      if predicate assignment then matchInput assignment else const n false)
    (.orGate (Fintype.card (Bits n)))

@[simp] theorem eval_ofPredicate (predicate : Bits n → Bool) (input : Bits n) :
    eval (ofPredicate predicate) input 0 = predicate input := by
  simp only [ofPredicate, eval]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    split at hi
    next htrue =>
      rw [eval_matchInput] at hi
      have heq : input = assignmentAt n i := of_decide_eq_true hi
      simpa [heq] using htrue
    next hfalse => simp at hi
  · intro hinput
    let i := Fintype.equivFin (Bits n) input
    refine ⟨i, ?_⟩
    have hi : assignmentAt n i = input := by
      simp [i, assignmentAt]
    simp [hi, hinput]

/-- Compile every output bit of a fixed finite-arity map in parallel. -/
noncomputable def ofFunction (function : Bits n → Bits m) : Circuit n m :=
  .bundle fun j => ofPredicate (fun input => function input j)

@[simp] theorem eval_ofFunction (function : Bits n → Bits m) (input : Bits n) :
    eval (ofFunction function) input = function input := by
  funext j
  simp [ofFunction, eval]

/-- Every truth-table circuit has depth at most three, independently of the
number of rows in its table. -/
theorem depth_ofPredicate_le_three (predicate : Bits n → Bool) :
    depth (ofPredicate predicate) ≤ 3 := by
  simp only [ofPredicate, depth]
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro i _
  dsimp only
  split
  · simp only [matchInput, depth]
    exact Nat.add_le_add_right (depth_literals_le_one _) 1
  · simp [const, depth]

theorem depth_ofFunction_le_three (function : Bits n → Bits m) :
    depth (ofFunction function) ≤ 3 := by
  simp only [ofFunction, depth]
  exact Finset.sup_le fun _ _ => depth_ofPredicate_le_three _

theorem gateCount_literals_le (assignment : Bits n) :
    gateCount (literals n assignment) ≤ n := by
  induction n with
  | zero => simp [literals, gateCount]
  | succ n ih =>
      simp only [literals, gateCount]
      have hprefix := ih (fun i => assignment i.castSucc)
      split <;> simp [id, gateCount] <;> omega

theorem gateCount_matchInput_le (assignment : Bits n) :
    gateCount (matchInput assignment) ≤ n + 1 := by
  simpa [matchInput, gateCount] using Nat.add_le_add_right
    (gateCount_literals_le assignment) 1

theorem gateCount_const (n : ℕ) (value : Bool) :
    gateCount (const n value) = 1 := by
  cases value <;> simp [const, gateCount]

/-- Explicit size bound for a finite truth table. -/
theorem gateCount_ofPredicate_le (predicate : Bits n → Bool) :
    gateCount (ofPredicate predicate) ≤
      Fintype.card (Bits n) * (n + 1) + 1 := by
  simp only [ofPredicate, gateCount]
  apply Nat.add_le_add_right
  calc
    (∑ i : Fin (Fintype.card (Bits n)),
        gateCount (let assignment := assignmentAt n i
          if predicate assignment then matchInput assignment else const n false))
        ≤ ∑ _i : Fin (Fintype.card (Bits n)), (n + 1) := by
          apply Finset.sum_le_sum
          intro i _
          dsimp only
          split
          · exact gateCount_matchInput_le _
          · rw [gateCount_const]
            omega
    _ = Fintype.card (Bits n) * (n + 1) := by simp

/-- Explicit size bound for a vector-valued finite truth table. -/
theorem gateCount_ofFunction_le (function : Bits n → Bits m) :
    gateCount (ofFunction function) ≤
      m * (Fintype.card (Bits n) * (n + 1) + 1) := by
  simp only [ofFunction, gateCount]
  calc
    (∑ j : Fin m, gateCount (ofPredicate fun input => function input j)) ≤
        ∑ _j : Fin m, (Fintype.card (Bits n) * (n + 1) + 1) := by
          apply Finset.sum_le_sum
          intro j _
          exact gateCount_ofPredicate_le _
    _ = m * (Fintype.card (Bits n) * (n + 1) + 1) := by simp

end Circuit

/-! ## Star-free programs for rounded iterated addition

The paper's key arithmetic observation is that fixed-precision rounded
addition is an ordered finite-state fold.  Its output-bit languages are
star-free.  The syntax below is the certificate carried by the explicit
fixed-precision arithmetic, and `StarFree.compile` is the actual
AND/OR/NOT-circuit construction.  Concatenation is compiled by trying every
split point in parallel; consequently expression depth is independent of the
word length and size is polynomial in it. -/

inductive StarFree (symbolBits : ℕ)
  | empty
  | epsilon
  | letter (predicate : Bits symbolBits → Bool)
  | union (left right : StarFree symbolBits)
  | inter (left right : StarFree symbolBits)
  | compl (body : StarFree symbolBits)
  | concat (left right : StarFree symbolBits)

namespace StarFree

/-- Route the prefix selected by a concatenation split. -/
def prefixRoute {symbolBits n : ℕ} (split : Fin (n + 1)) :
    Fin (split.val * symbolBits) → Fin (n * symbolBits) := fun index =>
  let location := finProdFinEquiv.symm index
  finProdFinEquiv
    (Fin.castLE (Nat.le_of_lt_succ split.isLt) location.1, location.2)

/-- Route the complementary suffix selected by a concatenation split. -/
def suffixRoute {symbolBits n : ℕ} (split : Fin (n + 1)) :
    Fin ((n - split.val) * symbolBits) → Fin (n * symbolBits) := fun index =>
  let location := finProdFinEquiv.symm index
  finProdFinEquiv
    (⟨split.val + location.1.val, by
      have hs : split.val ≤ n := Nat.le_of_lt_succ split.isLt
      have hl := location.1.isLt
      omega⟩, location.2)

/-- Fixed-length semantics of a star-free word program. -/
def accepts : StarFree symbolBits → (n : ℕ) → Bits (n * symbolBits) → Bool
  | .empty, _, _ => false
  | .epsilon, n, _ => decide (n = 0)
  | .letter predicate, n, input =>
      if h : n = 1 then
        predicate (fun bit => input (finProdFinEquiv (⟨0, by omega⟩, bit)))
      else false
  | .union left right, n, input => left.accepts n input || right.accepts n input
  | .inter left right, n, input => left.accepts n input && right.accepts n input
  | .compl body, n, input => !(body.accepts n input)
  | .concat left right, n, input => decide (∃ split : Fin (n + 1),
      left.accepts split.val (fun i => input (prefixRoute split i)) = true ∧
      right.accepts (n - split.val) (fun i => input (suffixRoute split i)) = true)

/-- Compile a star-free word program to a pure AND/OR/NOT circuit. -/
noncomputable def compile :
    StarFree symbolBits → (n : ℕ) → Circuit (n * symbolBits) 1
  | .empty, n => Circuit.const _ false
  | .epsilon, n => Circuit.const _ (decide (n = 0))
  | .letter predicate, n =>
      if h : n = 1 then
        Circuit.reinput
          (fun bit => finProdFinEquiv (⟨0, by omega⟩, bit))
          (Circuit.ofPredicate predicate)
      else Circuit.const _ false
  | .union left right, n =>
      .seq (.parallel (left.compile n) (right.compile n)) (.orGate 2)
  | .inter left right, n =>
      .seq (.parallel (left.compile n) (right.compile n)) (.andGate 2)
  | .compl body, n => .seq (body.compile n) .notGate
  | .concat left right, n =>
      .seq
        (.bundle fun split : Fin (n + 1) =>
          .seq
            (.parallel
              (Circuit.reinput (prefixRoute split) (left.compile split.val))
              (Circuit.reinput (suffixRoute split) (right.compile (n - split.val))))
            (.andGate 2))
        (.orGate (n + 1))

private theorem eval_binary_or (left right : Circuit n 1) (input : Bits n) :
    Circuit.eval (.seq (.parallel left right) (.orGate 2)) input 0 =
      (Circuit.eval left input 0 || Circuit.eval right input 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Circuit.eval, decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (by simpa [Fin.append_left] using hi)
    · exact Or.inr (by simpa [Fin.append_right] using hi)
  · rintro (hi | hi)
    · exact ⟨0, by simpa [Fin.append_left] using hi⟩
    · exact ⟨1, by simpa [Fin.append_right] using hi⟩

private theorem eval_binary_and (left right : Circuit n 1) (input : Bits n) :
    Circuit.eval (.seq (.parallel left right) (.andGate 2)) input 0 =
      (Circuit.eval left input 0 && Circuit.eval right input 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Circuit.eval, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨by simpa [Fin.append_left] using h 0,
      by simpa [Fin.append_right] using h 1⟩
  · rintro ⟨hl, hr⟩ i
    fin_cases i
    · simpa [Fin.append_left] using hl
    · simpa [Fin.append_right] using hr

/-- Correctness of the star-free-to-circuit compiler. -/
@[simp] theorem eval_compile (expression : StarFree symbolBits) (n : ℕ)
    (input : Bits (n * symbolBits)) :
    Circuit.eval (expression.compile n) input 0 = expression.accepts n input := by
  induction expression generalizing n with
  | empty => simp [compile, accepts]
  | epsilon => simp [compile, accepts]
  | letter predicate =>
      simp only [compile, accepts]
      split <;> simp_all
  | union left right ihl ihr =>
      rw [compile, eval_binary_or, ihl, ihr]
      rfl
  | inter left right ihl ihr =>
      rw [compile, eval_binary_and, ihl, ihr]
      rfl
  | compl body ih =>
      simp [compile, accepts, Circuit.eval, ih]
  | concat left right ihl ihr =>
      simp only [compile, accepts, Circuit.eval]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨split, hsplit⟩
        have hboth :
            Circuit.eval
              (.seq
                (.parallel
                  (Circuit.reinput (prefixRoute split) (compile left split.val))
                  (Circuit.reinput (suffixRoute split) (compile right (n - split.val))))
                (.andGate 2)) input 0 = true := hsplit
        rw [eval_binary_and] at hboth
        simp only [Bool.and_eq_true, Circuit.eval_reinput, ihl, ihr] at hboth
        exact ⟨split, hboth⟩
      · rintro ⟨split, hleft, hright⟩
        refine ⟨split, ?_⟩
        apply decide_eq_true
        change ∀ i : Fin 2,
          Fin.append
            (Circuit.eval (Circuit.reinput (prefixRoute split) (left.compile split.val)) input)
            (Circuit.eval (Circuit.reinput (suffixRoute split)
              (right.compile (n - split.val))) input) i = true
        rw [Fin.forall_fin_two]
        constructor
        · rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) by rfl,
            Fin.append_left, Circuit.eval_reinput, ihl]
          exact hleft
        · rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) by rfl,
            Fin.append_right, Circuit.eval_reinput, ihr]
          exact hright

/-- A length-independent depth bound read directly from a star-free
expression. -/
def circuitDepth : StarFree symbolBits → ℕ
  | .empty | .epsilon | .letter _ => 3
  | .union left right | .inter left right =>
      max left.circuitDepth right.circuitDepth + 1
  | .compl body => body.circuitDepth + 1
  | .concat left right => max left.circuitDepth right.circuitDepth + 2

theorem depth_compile_le (expression : StarFree symbolBits) (n : ℕ) :
    Circuit.depth (expression.compile n) ≤ expression.circuitDepth := by
  induction expression generalizing n with
  | empty => simp [compile, circuitDepth, Circuit.const, Circuit.depth]
  | epsilon =>
      simp only [compile, circuitDepth, Circuit.const, Circuit.depth]
      split <;> simp [Circuit.depth]
  | letter predicate =>
      simp only [compile, circuitDepth]
      split
      · simpa using Circuit.depth_ofPredicate_le_three predicate
      · simp [Circuit.const, Circuit.depth]
  | union left right ihl ihr =>
      simp only [compile, circuitDepth, Circuit.depth]
      exact Nat.add_le_add_right (max_le_max (ihl n) (ihr n)) 1
  | inter left right ihl ihr =>
      simp only [compile, circuitDepth, Circuit.depth]
      exact Nat.add_le_add_right (max_le_max (ihl n) (ihr n)) 1
  | compl body ih =>
      simp only [compile, circuitDepth, Circuit.depth]
      exact Nat.add_le_add_right (ih n) 1
  | concat left right ihl ihr =>
      simp only [compile, circuitDepth, Circuit.depth, Circuit.depth_reinput]
      apply Nat.add_le_add_right
      apply Finset.sup_le
      intro split _
      exact Nat.add_le_add_right
        (max_le_max (ihl split.val) (ihr (n - split.val))) 1

/-- A function of the word length has a concrete polynomial upper bound. -/
def PolynomialBound (cost : ℕ → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ, ∀ n,
    cost n ≤ coefficient * (n + 1) ^ exponent

private theorem pow_le_pow_add_right (base left right : ℕ) (hbase : 1 ≤ base) :
    base ^ left ≤ base ^ (left + right) := by
  rw [pow_add]
  exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hbase)

private theorem pow_le_pow_add_left (base left right : ℕ) (hbase : 1 ≤ base) :
    base ^ right ≤ base ^ (left + right) := by
  rw [pow_add]
  exact Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hbase)

/-- Star-free compilation has polynomial gate count.  Both witnesses depend
only on the fixed expression (hence only on fixed precision), never on the
word length. -/
theorem gateCount_compile_polynomial (expression : StarFree symbolBits) :
    PolynomialBound (fun n => Circuit.gateCount (expression.compile n)) := by
  induction expression with
  | empty =>
      refine ⟨1, 0, fun n => ?_⟩
      simp [compile, Circuit.gateCount_const]
  | epsilon =>
      refine ⟨1, 0, fun n => ?_⟩
      simp [compile, Circuit.gateCount_const]
  | letter predicate =>
      let tableCost := Fintype.card (Bits symbolBits) * (symbolBits + 1) + 1
      refine ⟨max 1 tableCost, 0, fun n => ?_⟩
      simp only [compile]
      split
      · simpa [tableCost, Circuit.gateCount_reinput] using
          (Circuit.gateCount_ofPredicate_le predicate).trans
            (Nat.le_max_right 1 tableCost)
      · simp [Circuit.gateCount_const]
  | union left right ihl ihr =>
      obtain ⟨cl, el, hl⟩ := ihl
      obtain ⟨cr, er, hr⟩ := ihr
      refine ⟨cl + cr + 1, el + er, fun n => ?_⟩
      let base := n + 1
      have hb : 1 ≤ base := by simp [base]
      have hpl : base ^ el ≤ base ^ (el + er) :=
        pow_le_pow_add_right base el er hb
      have hpr : base ^ er ≤ base ^ (el + er) :=
        pow_le_pow_add_left base el er hb
      simp only [compile, Circuit.gateCount]
      calc
        Circuit.gateCount (compile left n) + Circuit.gateCount (compile right n) + 1
            ≤ cl * base ^ el + cr * base ^ er + 1 := by
              exact Nat.add_le_add_right (Nat.add_le_add (hl n) (hr n)) 1
        _ ≤ cl * base ^ (el + er) + cr * base ^ (el + er) +
              1 * base ^ (el + er) := by
              exact Nat.add_le_add
                (Nat.add_le_add (Nat.mul_le_mul_left cl hpl)
                  (Nat.mul_le_mul_left cr hpr))
                (by simpa using (Nat.one_le_pow (el + er) base hb))
        _ = (cl + cr + 1) * (n + 1) ^ (el + er) := by simp [base]; ring
  | inter left right ihl ihr =>
      obtain ⟨cl, el, hl⟩ := ihl
      obtain ⟨cr, er, hr⟩ := ihr
      refine ⟨cl + cr + 1, el + er, fun n => ?_⟩
      let base := n + 1
      have hb : 1 ≤ base := by simp [base]
      have hpl := pow_le_pow_add_right base el er hb
      have hpr := pow_le_pow_add_left base el er hb
      simp only [compile, Circuit.gateCount]
      calc
        Circuit.gateCount (compile left n) + Circuit.gateCount (compile right n) + 1
            ≤ cl * base ^ el + cr * base ^ er + 1 := by
              exact Nat.add_le_add_right (Nat.add_le_add (hl n) (hr n)) 1
        _ ≤ cl * base ^ (el + er) + cr * base ^ (el + er) +
              1 * base ^ (el + er) := by
              exact Nat.add_le_add
                (Nat.add_le_add (Nat.mul_le_mul_left cl hpl)
                  (Nat.mul_le_mul_left cr hpr))
                (by simpa using (Nat.one_le_pow (el + er) base hb))
        _ = (cl + cr + 1) * (n + 1) ^ (el + er) := by simp [base]; ring
  | compl body ih =>
      obtain ⟨coefficient, exponent, h⟩ := ih
      refine ⟨coefficient + 1, exponent, fun n => ?_⟩
      have hb : 1 ≤ (n + 1) ^ exponent := Nat.one_le_pow _ _ (by omega)
      simp only [compile, Circuit.gateCount]
      calc
        Circuit.gateCount (compile body n) + 1 ≤
            coefficient * (n + 1) ^ exponent + 1 := Nat.add_le_add_right (h n) 1
        _ ≤ coefficient * (n + 1) ^ exponent + (n + 1) ^ exponent :=
          Nat.add_le_add_left hb _
        _ = (coefficient + 1) * (n + 1) ^ exponent := by ring
  | concat left right ihl ihr =>
      obtain ⟨cl, el, hl⟩ := ihl
      obtain ⟨cr, er, hr⟩ := ihr
      refine ⟨cl + cr + 2, el + er + 1, fun n => ?_⟩
      let base := n + 1
      let power := base ^ (el + er)
      have hb : 1 ≤ base := by simp [base]
      have hp : 1 ≤ power := Nat.one_le_pow _ _ hb
      have hbranch : ∀ split : Fin (n + 1),
          Circuit.gateCount
            (.seq
              (.parallel
                (Circuit.reinput (prefixRoute split) (compile left split.val))
                (Circuit.reinput (suffixRoute split) (compile right (n - split.val))))
              (.andGate 2)) ≤ (cl + cr + 1) * power := by
        intro split
        have hleftBase : split.val + 1 ≤ base := by
          dsimp [base]
          omega
        have hrightBase : n - split.val + 1 ≤ base := by
          dsimp [base]
          omega
        have hleftPow : (split.val + 1) ^ el ≤ power := by
          exact (Nat.pow_le_pow_left hleftBase el).trans
            (pow_le_pow_add_right base el er hb)
        have hrightPow : (n - split.val + 1) ^ er ≤ power := by
          exact (Nat.pow_le_pow_left hrightBase er).trans
            (pow_le_pow_add_left base el er hb)
        simp only [Circuit.gateCount, Circuit.gateCount_reinput]
        calc
          Circuit.gateCount (compile left split.val) +
                Circuit.gateCount (compile right (n - split.val)) + 1
              ≤ cl * (split.val + 1) ^ el +
                  cr * (n - split.val + 1) ^ er + 1 := by
                exact Nat.add_le_add_right
                  (Nat.add_le_add (hl split.val) (hr (n - split.val))) 1
          _ ≤ cl * power + cr * power + 1 * power := by
                exact Nat.add_le_add
                  (Nat.add_le_add (Nat.mul_le_mul_left cl hleftPow)
                    (Nat.mul_le_mul_left cr hrightPow)) (by simpa using hp)
          _ = (cl + cr + 1) * power := by ring
      simp only [compile, Circuit.gateCount]
      have hsum :
          (∑ split : Fin (n + 1),
            Circuit.gateCount
              (.seq
                (.parallel
                  (Circuit.reinput (prefixRoute split) (compile left split.val))
                  (Circuit.reinput (suffixRoute split) (compile right (n - split.val))))
                (.andGate 2))) ≤
            (n + 1) * ((cl + cr + 1) * power) := by
        calc
          _ ≤ ∑ _split : Fin (n + 1), ((cl + cr + 1) * power) := by
            apply Finset.sum_le_sum
            intro split _
            exact hbranch split
          _ = (n + 1) * ((cl + cr + 1) * power) := by simp
      calc
        (∑ split : Fin (n + 1),
            (Circuit.reinput (prefixRoute split) (compile left split.val) |>.parallel
              (Circuit.reinput (suffixRoute split) (compile right (n - split.val))) |>.seq
              (.andGate 2) |>.gateCount)) + 1
            ≤ (n + 1) * ((cl + cr + 1) * power) + 1 :=
              Nat.add_le_add_right hsum 1
        _ ≤ (n + 1) * ((cl + cr + 1) * power) + (n + 1) * power := by
              have hbp : 1 ≤ (n + 1) * power := by
                calc
                  1 = 1 * 1 := by simp
                  _ ≤ (n + 1) * power := Nat.mul_le_mul hb hp
              exact Nat.add_le_add_left hbp _
        _ = (cl + cr + 2) * (n + 1) ^ (el + er + 1) := by
              simp only [power, base, pow_succ]
              ring

namespace PolynomialBound

theorem zero : PolynomialBound (fun _ => 0) := by
  exact ⟨0, 0, by simp⟩

theorem const (value : ℕ) : PolynomialBound (fun _ => value) := by
  exact ⟨value, 0, by simp⟩

theorem identity : PolynomialBound (fun n => n) := by
  exact ⟨1, 1, by simp⟩

theorem successor : PolynomialBound (fun n => n + 1) := by
  exact ⟨1, 1, by simp⟩

theorem add {left right : ℕ → ℕ}
    (hleft : PolynomialBound left) (hright : PolynomialBound right) :
    PolynomialBound (fun n => left n + right n) := by
  obtain ⟨cl, el, hl⟩ := hleft
  obtain ⟨cr, er, hr⟩ := hright
  refine ⟨cl + cr, el + er, fun n => ?_⟩
  let base := n + 1
  have hb : 1 ≤ base := by simp [base]
  have hpl := pow_le_pow_add_right base el er hb
  have hpr := pow_le_pow_add_left base el er hb
  calc
    left n + right n ≤ cl * base ^ el + cr * base ^ er :=
      Nat.add_le_add (hl n) (hr n)
    _ ≤ cl * base ^ (el + er) + cr * base ^ (el + er) :=
      Nat.add_le_add (Nat.mul_le_mul_left cl hpl) (Nat.mul_le_mul_left cr hpr)
    _ = (cl + cr) * (n + 1) ^ (el + er) := by simp [base]; ring

theorem mul {left right : ℕ → ℕ}
    (hleft : PolynomialBound left) (hright : PolynomialBound right) :
    PolynomialBound (fun n => left n * right n) := by
  obtain ⟨cl, el, hl⟩ := hleft
  obtain ⟨cr, er, hr⟩ := hright
  refine ⟨cl * cr, el + er, fun n => ?_⟩
  calc
    left n * right n ≤
        (cl * (n + 1) ^ el) * (cr * (n + 1) ^ er) := Nat.mul_le_mul (hl n) (hr n)
    _ = (cl * cr) * (n + 1) ^ (el + er) := by rw [pow_add]; ring

theorem finset_sum {index : Type*} [DecidableEq index]
    (indices : Finset index) (cost : index → ℕ → ℕ)
    (h : ∀ i ∈ indices, PolynomialBound (cost i)) :
    PolynomialBound (fun n => ∑ i ∈ indices, cost i n) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using zero
  | @insert item rest hnot ih =>
      have hitem := h item (by simp)
      have hrest : ∀ i ∈ rest, PolynomialBound (cost i) := by
        intro i hi
        exact h i (by simp [hi])
      simpa [Finset.sum_insert hnot] using hitem.add (ih hrest)

end PolynomialBound

end StarFree

/-! ## Ordered-word expressions and the bit-stream representation -/

namespace OrderedExpression

open OrderedAddition

/-- Decode the flat row-major circuit input into its word of scalar symbols. -/
def inputWord (symbolBits count : ℕ) (input : Bits (count * symbolBits)) :
    List (Bits symbolBits) :=
  List.ofFn fun position => fun bit => input (finProdFinEquiv (position, bit))

@[simp] theorem length_inputWord (input : Bits (count * symbolBits)) :
    (inputWord symbolBits count input).length = count := by
  simp [inputWord]

theorem inputWord_prefix (split : Fin (count + 1))
    (input : Bits (count * symbolBits)) :
    inputWord symbolBits split.val (fun index => input (StarFree.prefixRoute split index)) =
      (inputWord symbolBits count input).take split.val := by
  apply List.ext_getElem
  · have hsplit : split.val ≤ count := by omega
    simp [inputWord, Nat.min_eq_left hsplit]
  · intro index hleft hright
    simp [inputWord, StarFree.prefixRoute, List.getElem_take]

theorem inputWord_suffix (split : Fin (count + 1))
    (input : Bits (count * symbolBits)) :
    inputWord symbolBits (count - split.val)
        (fun index => input (StarFree.suffixRoute split index)) =
      (inputWord symbolBits count input).drop split.val := by
  apply List.ext_getElem
  · simp [inputWord]
  · intro index hleft hright
    simp [inputWord, StarFree.suffixRoute, List.getElem_drop]

/-- The syntax-preserving translation from the generic ordered-automaton
expressions to the bit-symbol expressions compiled above. -/
def toStarFree : OrderedAddition.Expression (Bits symbolBits) → StarFree symbolBits
  | .empty => .empty
  | .epsilon => .epsilon
  | .letter predicate => .letter predicate
  | .union left right => .union (toStarFree left) (toStarFree right)
  | .inter left right => .inter (toStarFree left) (toStarFree right)
  | .compl body => .compl (toStarFree body)
  | .concat left right => .concat (toStarFree left) (toStarFree right)

private theorem accepts_concat_iff_split
    (left right : OrderedAddition.Expression Alphabet) (word : List Alphabet) :
    (OrderedAddition.Expression.concat left right).Accepts word ↔
      ∃ split : Fin (word.length + 1),
        left.Accepts (word.take split.val) ∧
        right.Accepts (word.drop split.val) := by
  constructor
  · rintro ⟨initial, final, rfl, hinitial, hfinal⟩
    let split : Fin ((initial ++ final).length + 1) :=
      ⟨initial.length, by simp; omega⟩
    refine ⟨split, ?_, ?_⟩
    · simpa [split] using hinitial
    · simpa [split] using hfinal
  · rintro ⟨split, hinitial, hfinal⟩
    exact ⟨word.take split.val, word.drop split.val,
      (List.take_append_drop split.val word).symm, hinitial, hfinal⟩

/-- `toStarFree` preserves language semantics under the row-major encoding. -/
theorem accepts_toStarFree (expression : OrderedAddition.Expression (Bits symbolBits))
    (count : ℕ) (input : Bits (count * symbolBits)) :
    (toStarFree expression).accepts count input = true ↔
      expression.Accepts (inputWord symbolBits count input) := by
  induction expression generalizing count with
  | empty => simp [toStarFree, StarFree.accepts, OrderedAddition.Expression.Accepts]
  | epsilon => simp [toStarFree, StarFree.accepts, OrderedAddition.Expression.Accepts,
      inputWord]
  | letter predicate =>
      simp only [toStarFree, StarFree.accepts, OrderedAddition.Expression.Accepts]
      by_cases hcount : count = 1
      · subst count
        simp [inputWord]
      · have hword : (inputWord symbolBits count input).length ≠ 1 := by
          simpa using hcount
        simp only [hcount, ↓reduceDIte, Bool.false_eq_true,
          OrderedAddition.Expression.Accepts]
        constructor
        · intro hfalse
          exact hfalse.elim
        · rintro ⟨symbol, hsingle, -⟩
          apply hword
          simpa using congrArg List.length hsingle
  | union left right ihLeft ihRight =>
      simp [toStarFree, StarFree.accepts, ihLeft, ihRight,
        OrderedAddition.Expression.Accepts]
  | inter left right ihLeft ihRight =>
      simp [toStarFree, StarFree.accepts, ihLeft, ihRight,
        OrderedAddition.Expression.Accepts]
  | compl body ih =>
      simp only [toStarFree, StarFree.accepts, Bool.not_eq_true_eq_eq_false,
        OrderedAddition.Expression.Accepts]
      constructor
      · intro hfalse haccepts
        have htrue := (ih count input).2 haccepts
        exact Bool.false_ne_true (hfalse.symm.trans htrue)
      · intro hnot
        exact Bool.eq_false_of_not_eq_true (fun htrue => hnot ((ih count input).1 htrue))
  | concat left right ihLeft ihRight =>
      rw [accepts_concat_iff_split]
      simp only [toStarFree, StarFree.accepts, decide_eq_true_eq]
      constructor
      · rintro ⟨split, hleft, hright⟩
        let wordSplit : Fin ((inputWord symbolBits count input).length + 1) :=
          ⟨split.val, by simp [inputWord]⟩
        refine ⟨wordSplit, ?_, ?_⟩
        · have hdecoded := (ihLeft split.val _).1 hleft
          rw [inputWord_prefix] at hdecoded
          simpa [wordSplit] using hdecoded
        · have hdecoded := (ihRight (count - split.val) _).1 hright
          rw [inputWord_suffix] at hdecoded
          simpa [wordSplit] using hdecoded
      · rintro ⟨split, hleft, hright⟩
        let circuitSplit : Fin (count + 1) :=
          ⟨split.val, by simpa [inputWord] using split.isLt⟩
        refine ⟨circuitSplit, ?_, ?_⟩
        · apply (ihLeft circuitSplit.val _).2
          rw [inputWord_prefix]
          simpa [circuitSplit] using hleft
        · apply (ihRight (count - circuitSplit.val) _).2
          rw [inputWord_suffix]
          simpa [circuitSplit] using hright

end OrderedExpression

/-! ## The fixed-precision Transformer interface -/

/--
The architectural quantities occurring in the appendix.  The hidden width is
stored as twice `halfWidth`, making the assumption that `D` is even intrinsic
to the type.
-/
structure Architecture where
  vocabulary : ℕ
  halfWidth : ℕ
  layers : ℕ
  heads : ℕ
  contextLength : ℕ
  deriving DecidableEq, Repr

namespace Architecture

/-- The paper's even hidden dimensionality `D`. -/
def hiddenWidth (a : Architecture) : ℕ := 2 * a.halfWidth

/-- A one-hot encoding of `N` input tokens. -/
def inputBits (a : Architecture) : ℕ := a.contextLength * a.vocabulary

/--
Boolean width of the hidden sequence, suppressing the globally fixed number
of representation bits per scalar.
-/
def stateBits (a : Architecture) : ℕ := a.contextLength * a.hiddenWidth

/--
The exact parameter count from the paper:

`(3/2)|V|D + (3LH + 2L)D²`.

Since `D = 2 * halfWidth`, its first summand is the integral expression below.
Positional encodings are excluded, as in the appendix.
-/
def parameterCount (a : Architecture) : ℕ :=
  3 * a.vocabulary * a.halfWidth +
    (3 * a.layers * a.heads + 2 * a.layers) * a.hiddenWidth ^ 2

/-- Variables on which one locally compiled Transformer stage depends. -/
def localBase (a : Architecture) : ℕ :=
  a.contextLength + a.hiddenWidth + a.heads + a.vocabulary + 1

end Architecture

/-- A multi-output star-free transducer.  Every output bit is an explicit
star-free program over the input bit stream. -/
structure StarFreeTransducer (outputs : ℕ) where
  output : Fin outputs → StarFree 1

namespace StarFreeTransducer

/-- Forget the singleton bit-coordinate of a word over one-bit symbols. -/
def oneBitRoute {inputLength : ℕ} : Fin (inputLength * 1) → Fin inputLength :=
  fun index => (finProdFinEquiv.symm index).1

/-- Extensional semantics, used only after the syntax has been fixed. -/
def run (program : StarFreeTransducer outputs) (inputLength : ℕ)
    (input : Bits inputLength) : Bits outputs :=
  fun bit => (program.output bit).accepts inputLength
    (fun index => input (oneBitRoute index))

/-- Compile all output programs in parallel. -/
noncomputable def compile (program : StarFreeTransducer outputs) (inputLength : ℕ) :
    Circuit inputLength outputs :=
  .bundle fun bit => Circuit.reinput oneBitRoute
    ((program.output bit).compile inputLength)

@[simp] theorem eval_compile (program : StarFreeTransducer outputs)
    (input : Bits inputLength) :
    Circuit.eval (program.compile inputLength) input = program.run inputLength input := by
  funext bit
  simp [compile, run, Circuit.eval]

/-- The maximum depth of the finitely many output programs. -/
def depthBound (program : StarFreeTransducer outputs) : ℕ :=
  Finset.univ.sup fun bit => (program.output bit).circuitDepth

theorem depth_compile_le (program : StarFreeTransducer outputs) (inputLength : ℕ) :
    Circuit.depth (program.compile inputLength) ≤ program.depthBound := by
  simp only [compile, Circuit.depth, depthBound]
  apply Finset.sup_le
  intro bit _
  simpa using ((StarFree.depth_compile_le (program.output bit) inputLength).trans
    (Finset.le_sup (s := Finset.univ)
      (f := fun bit => (program.output bit).circuitDepth) (by simp)))

/-- Gate count is polynomial in input length, with witnesses depending only
on the fixed transducer syntax. -/
theorem gateCount_compile_polynomial (program : StarFreeTransducer outputs) :
    StarFree.PolynomialBound
    (fun inputLength => Circuit.gateCount (program.compile inputLength)) := by
  have h := StarFree.PolynomialBound.finset_sum Finset.univ
    (fun bit (_inputLength : ℕ) =>
      Circuit.gateCount (Circuit.reinput oneBitRoute
        ((program.output bit).compile _inputLength)))
    (by
      intro bit _
      simpa using StarFree.gateCount_compile_polynomial (program.output bit))
  simpa [compile, Circuit.gateCount] using h

end StarFreeTransducer

/-- The five explicitly separated components of one fixed-precision layer.
The names correspond to the appendix construction: attention scores and
weighted values, softmax (including exponentiation and division), residual
rounding, ReLU/MLP, and the final residual rounding.  Every component is
star-free syntax, not an assumed circuit. -/
structure StarFreeLayer (stateBits : ℕ) where
  attention : StarFreeTransducer stateBits
  softmax : StarFreeTransducer stateBits
  attentionRound : StarFreeTransducer stateBits
  relu : StarFreeTransducer stateBits
  feedForwardRound : StarFreeTransducer stateBits

namespace StarFreeLayer

noncomputable def circuits (layer : StarFreeLayer stateBits) :
    List (Circuit stateBits stateBits) :=
  [layer.attention.compile stateBits,
    layer.softmax.compile stateBits,
    layer.attentionRound.compile stateBits,
    layer.relu.compile stateBits,
    layer.feedForwardRound.compile stateBits]

noncomputable def compile (layer : StarFreeLayer stateBits) :
    Circuit stateBits stateBits := Circuit.serial layer.circuits

def run (layer : StarFreeLayer stateBits) (state : Bits stateBits) :
    Bits stateBits :=
  layer.feedForwardRound.run stateBits
    (layer.relu.run stateBits
      (layer.attentionRound.run stateBits
        (layer.softmax.run stateBits (layer.attention.run stateBits state))))

@[simp] theorem eval_compile (layer : StarFreeLayer stateBits)
    (state : Bits stateBits) :
    Circuit.eval layer.compile state = layer.run state := by
  simp [compile, circuits, Circuit.eval_serial, Circuit.runSerial, run]

/-- A bound for the five primitive phases of a layer. -/
def depthBound (layer : StarFreeLayer stateBits) : ℕ :=
  layer.attention.depthBound + (layer.softmax.depthBound +
    (layer.attentionRound.depthBound + (layer.relu.depthBound +
      layer.feedForwardRound.depthBound)))

theorem depth_compile_le (layer : StarFreeLayer stateBits) :
    Circuit.depth layer.compile ≤ layer.depthBound := by
  simp only [compile, circuits, Circuit.depth_serial, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, depthBound]
  exact Nat.add_le_add
    (layer.attention.depth_compile_le stateBits)
    (Nat.add_le_add (layer.softmax.depth_compile_le stateBits)
      (Nat.add_le_add (layer.attentionRound.depth_compile_le stateBits)
        (Nat.add_le_add (layer.relu.depth_compile_le stateBits)
          (layer.feedForwardRound.depth_compile_le stateBits))))

end StarFreeLayer

/--
Syntactic fixed-precision Transformer.  Embedding, every arithmetic phase of
every layer, and readout are star-free programs.  Finite-arity rounding,
multiplication, exponentiation, division, and ReLU enter as `letter`
predicates and are compiled by `Circuit.ofPredicate`; rounded iterated sums
enter through concatenation programs and are compiled by `StarFree.compile`.
-/
structure StarFreeTransformer (a : Architecture) where
  embedding : StarFreeTransducer a.stateBits
  layer : List (StarFreeLayer a.stateBits)
  layer_length : layer.length = a.layers
  readout : StarFreeTransducer 1

namespace StarFreeTransformer

/-- Run the syntactic fixed-precision semantics. -/
def run {a : Architecture} (T : StarFreeTransformer a)
    (input : Bits a.inputBits) : Bool :=
  T.readout.run a.stateBits
    (T.layer.foldl (fun state layer => layer.run state)
      (T.embedding.run a.inputBits input)) 0

/-- Construct every layer circuit from its five primitive programs. -/
noncomputable def layerCircuits {a : Architecture} (T : StarFreeTransformer a) :
    List (Circuit a.stateBits a.stateBits) := T.layer.map StarFreeLayer.compile

/-- The complete AND/OR/NOT circuit constructed from the Transformer syntax. -/
noncomputable def compile {a : Architecture} (T : StarFreeTransformer a) :
    Circuit a.inputBits 1 :=
  .seq (T.embedding.compile a.inputBits)
    (.seq (Circuit.serial T.layerCircuits) (T.readout.compile a.stateBits))

private theorem runSerial_layers {n : ℕ} (layers : List (StarFreeLayer n))
    (state : Bits n) :
    Circuit.runSerial (layers.map StarFreeLayer.compile) state =
      layers.foldl (fun current layer => layer.run current) state := by
  induction layers generalizing state with
  | nil => rfl
  | cons layer rest ih =>
      simp only [List.map_cons, Circuit.runSerial, List.foldl_cons]
      rw [layer.eval_compile]
      exact ih _

/-- The constructed circuit computes exactly the Transformer's semantics. -/
theorem compile_correct {a : Architecture} (T : StarFreeTransformer a)
    (input : Bits a.inputBits) :
    Circuit.eval T.compile input 0 = T.run input := by
  simp only [compile, Circuit.eval, StarFreeTransducer.eval_compile,
    Circuit.eval_serial, layerCircuits]
  rw [runSerial_layers]
  rfl

/-- Maximum depth of an explicitly generated local stage. -/
def localDepth {a : Architecture} (T : StarFreeTransformer a) : ℕ :=
  max T.embedding.depthBound
    (max T.readout.depthBound (T.layer.foldl (fun bound layer =>
      max bound layer.depthBound) 0))

theorem embedding_depth_le {a : Architecture} (T : StarFreeTransformer a) :
    Circuit.depth (T.embedding.compile a.inputBits) ≤ T.localDepth := by
  exact (T.embedding.depth_compile_le _).trans
    (Nat.le_max_left _ _)

theorem readout_depth_le {a : Architecture} (T : StarFreeTransformer a) :
    Circuit.depth (T.readout.compile a.stateBits) ≤ T.localDepth := by
  exact (T.readout.depth_compile_le _).trans
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))

private theorem initial_le_foldl_max {n : ℕ} (layers : List (StarFreeLayer n))
    (initial : ℕ) : initial ≤
      layers.foldl (fun bound layer => max bound layer.depthBound) initial := by
  induction layers generalizing initial with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.foldl_cons]
      exact (Nat.le_max_left _ _).trans (ih _)

private theorem layer_depth_le_fold {n : ℕ} (layers : List (StarFreeLayer n))
    {layer : StarFreeLayer n} (h : layer ∈ layers) (initial : ℕ) :
    layer.depthBound ≤
      layers.foldl (fun bound current => max bound current.depthBound) initial := by
  induction layers generalizing initial with
  | nil => simp at h
  | cons head rest ih =>
      simp only [List.mem_cons] at h
      simp only [List.foldl_cons]
      rcases h with rfl | h
      · exact (Nat.le_max_right _ _).trans (initial_le_foldl_max rest _)
      · exact ih h _

/-- Connecting all constructed stages gives depth linear in layer count. -/
theorem compile_depth_le {a : Architecture} (T : StarFreeTransformer a) :
    Circuit.depth T.compile ≤ (a.layers + 2) * T.localDepth := by
  have hlayers :
      (T.layerCircuits.map Circuit.depth).sum ≤
        a.layers * T.localDepth := by
    have hlength : T.layerCircuits.length = a.layers := by
      simp [layerCircuits, T.layer_length]
    calc
      (T.layerCircuits.map Circuit.depth).sum ≤
          T.layerCircuits.length * T.localDepth := by
        simpa [nsmul_eq_mul] using List.sum_le_card_nsmul
          (T.layerCircuits.map Circuit.depth) T.localDepth (by
          intro depth hdepth
          obtain ⟨circuit, hcircuit, rfl⟩ := List.mem_map.1 hdepth
          obtain ⟨layer, hlayer, rfl⟩ := List.mem_map.1 hcircuit
          have hlocal : layer.depthBound ≤ T.localDepth := by
            exact (layer_depth_le_fold T.layer hlayer 0).trans
              ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
          exact layer.depth_compile_le.trans hlocal)
      _ = a.layers * T.localDepth := by rw [hlength]
  simp only [compile, Circuit.depth, Circuit.depth_serial]
  calc
    Circuit.depth (T.embedding.compile a.inputBits) +
        ((T.layerCircuits.map Circuit.depth).sum +
          Circuit.depth (T.readout.compile a.stateBits)) ≤
        T.localDepth + (a.layers * T.localDepth + T.localDepth) :=
      Nat.add_le_add T.embedding_depth_le
        (Nat.add_le_add hlayers T.readout_depth_le)
    _ = (a.layers + 2) * T.localDepth := by ring

/-- Exact gate budget of all constructed local programs. -/
noncomputable def localGateBudget {a : Architecture}
    (T : StarFreeTransformer a) : ℕ :=
  Circuit.gateCount (T.embedding.compile a.inputBits) +
    (T.layerCircuits.map Circuit.gateCount).sum +
    Circuit.gateCount (T.readout.compile a.stateBits)

theorem compile_gateCount_eq_budget {a : Architecture} (T : StarFreeTransformer a) :
    Circuit.gateCount T.compile = T.localGateBudget := by
  simp [compile, localGateBudget, Circuit.gateCount, Circuit.gateCount_serial]
  ring

end StarFreeTransformer

/-! ## Matrix-level fixed-precision Transformer compiler -/

/-- The finite scalar operations used by the appendix model.  All scalar
operations are genuine finite functions.  `scalarRank` supplies the total
order on scalar encodings, while `roundedAdd_monotone` is the ordered-addition
property proved for fixed-precision rounding in the paper.  No circuit or
star-free-language witness is stored in this structure. -/
structure FixedPrecisionArithmetic (bits : ℕ) where
  zero : Bits bits
  scalarRank : Bits bits ≃ Fin (Fintype.card (Bits bits))
  round : Bits bits → Bits bits
  roundedAdd : Bits (bits + bits) → Bits bits
  roundedAdd_monotone : ∀ term : Bits bits, Monotone fun state =>
    scalarRank (roundedAdd (Fin.append (scalarRank.symm state) term))
  multiply : Bits (bits + bits) → Bits bits
  exponentiate : Bits bits → Bits bits
  divide : Bits (bits + bits) → Bits bits
  relu : Bits bits → Bits bits

namespace FixedPrecisionArithmetic

/-- Scalar comparison is the actual encoding order, rather than an arbitrary
Boolean operation supplied by the model. -/
def lessEqual (arithmetic : FixedPrecisionArithmetic bits) (pair : Bits (bits + bits)) : Bool :=
  decide (arithmetic.scalarRank (fun index => pair (Fin.castAdd bits index)) ≤
    arithmetic.scalarRank (fun index => pair (Fin.natAdd bits index)))

@[simp] theorem lessEqual_append (arithmetic : FixedPrecisionArithmetic bits) (first second : Bits bits) :
    arithmetic.lessEqual (Fin.append first second) =
      decide (arithmetic.scalarRank first ≤ arithmetic.scalarRank second) := by
  unfold lessEqual
  congr 1
  simp only [Fin.append_left, Fin.append_right]

/-- One ordered-automaton transition for addition of a scalar term. -/
def sumTransition (arithmetic : FixedPrecisionArithmetic bits) (term : Bits bits) :
    OrderedAddition.OrderedEnd (Fin (Fintype.card (Bits bits))) where
  toFun := fun state => arithmetic.scalarRank
    (arithmetic.roundedAdd (Fin.append (arithmetic.scalarRank.symm state) term))
  monotone := arithmetic.roundedAdd_monotone term

/-- The actual sequential rounded-addition semantics. -/
def roundedSumWord (arithmetic : FixedPrecisionArithmetic bits)
    (word : List (Bits bits)) : Bits bits :=
  word.foldl
    (fun accumulator term => arithmetic.roundedAdd (Fin.append accumulator term))
    arithmetic.zero

/-- The transition-monoid product acts exactly like the sequential fold. -/
theorem wordEval_sumTransition (arithmetic : FixedPrecisionArithmetic bits)
    (word : List (Bits bits)) (state : Fin (Fintype.card (Bits bits))) :
    OrderedAddition.wordEval arithmetic.sumTransition word state =
      arithmetic.scalarRank
        (word.foldl
          (fun accumulator term =>
            arithmetic.roundedAdd (Fin.append accumulator term))
          (arithmetic.scalarRank.symm state)) := by
  induction word generalizing state with
  | nil => simp [OrderedAddition.wordEval, sumTransition]
  | cons head tail ih =>
      rw [OrderedAddition.wordEval_cons, OrderedAddition.OrderedEnd.mul_apply, ih]
      simp [sumTransition]

/-- Star-free descriptions of every product in the ordered transition
monoid, obtained from the proved local-divisor construction. -/
noncomputable def sumFibers (arithmetic : FixedPrecisionArithmetic bits) :
    OrderedAddition.FiberExpressions (Bits bits)
      (OrderedAddition.OrderedEnd (Fin (Fintype.card (Bits bits))))
      arithmetic.sumTransition :=
  Classical.choice
    (OrderedAddition.exists_aperiodic_fiberExpressions arithmetic.sumTransition
      OrderedAddition.OrderedEnd.isAperiodic)

/-- The derived star-free language for one output bit of the rounded fold. -/
noncomputable def roundedSumExpression (arithmetic : FixedPrecisionArithmetic bits)
    (bit : Fin bits) : OrderedAddition.Expression (Bits bits) :=
  OrderedAddition.Expression.iUnion fun transition :
      OrderedAddition.OrderedEnd (Fin (Fintype.card (Bits bits))) =>
    if (arithmetic.scalarRank.symm
        (transition (arithmetic.scalarRank arithmetic.zero))) bit then
      (arithmetic.sumFibers.expression transition)
    else .empty

theorem roundedSumExpression_correct (arithmetic : FixedPrecisionArithmetic bits)
    (bit : Fin bits) (word : List (Bits bits)) :
    (arithmetic.roundedSumExpression bit).Accepts word ↔
      arithmetic.roundedSumWord word bit = true := by
  classical
  rw [roundedSumExpression, OrderedAddition.Expression.accepts_iUnion_iff]
  constructor
  · rintro ⟨transition, htransition⟩
    split at htransition
    next hbit =>
      have hproduct := (arithmetic.sumFibers.correct transition word).1 htransition
      have hrun := arithmetic.wordEval_sumTransition word
        (arithmetic.scalarRank arithmetic.zero)
      rw [hproduct] at hrun
      have hstate : arithmetic.scalarRank.symm
          (transition (arithmetic.scalarRank arithmetic.zero)) =
          arithmetic.roundedSumWord word := by
        rw [hrun]
        simp [roundedSumWord]
      simpa [hstate] using hbit
    next hbit => exact htransition.elim
  · intro hbit
    let transition := OrderedAddition.wordEval arithmetic.sumTransition word
    refine ⟨transition, ?_⟩
    have hrun := arithmetic.wordEval_sumTransition word
      (arithmetic.scalarRank arithmetic.zero)
    have hstate : arithmetic.scalarRank.symm
        (transition (arithmetic.scalarRank arithmetic.zero)) =
        arithmetic.roundedSumWord word := by
      dsimp [transition]
      rw [hrun]
      simp [roundedSumWord]
    simp only [hstate, hbit, if_true]
    exact (arithmetic.sumFibers.correct transition word).2 rfl

/-- The bit-level star-free expression is derived, not supplied by the model. -/
noncomputable def roundedSumBit (arithmetic : FixedPrecisionArithmetic bits)
    (bit : Fin bits) : StarFree bits :=
  OrderedExpression.toStarFree (arithmetic.roundedSumExpression bit)

/-- Semantics of an iterated rounded sum: decode the input word and execute
the actual left-to-right rounded-addition fold. -/
def roundedSum (arithmetic : FixedPrecisionArithmetic bits) (count : ℕ)
    (input : Bits (count * bits)) : Bits bits :=
  arithmetic.roundedSumWord (OrderedExpression.inputWord bits count input)

theorem roundedSumBit_accepts (arithmetic : FixedPrecisionArithmetic bits)
    (bit : Fin bits) (input : Bits (count * bits)) :
    (arithmetic.roundedSumBit bit).accepts count input =
      arithmetic.roundedSum count input bit := by
  simp only [roundedSumBit]
  apply Bool.eq_iff_iff.mpr
  rw [OrderedExpression.accepts_toStarFree,
    arithmetic.roundedSumExpression_correct]
  rfl

/-- Construct all bits of an iterated rounded-sum circuit. -/
noncomputable def sumCircuit (arithmetic : FixedPrecisionArithmetic bits) (count : ℕ) :
    Circuit (count * bits) bits :=
  .bundle fun bit => (arithmetic.roundedSumBit bit).compile count

@[simp] theorem eval_sumCircuit (arithmetic : FixedPrecisionArithmetic bits)
    (input : Bits (count * bits)) :
    Circuit.eval (arithmetic.sumCircuit count) input = arithmetic.roundedSum count input := by
  funext bit
  simp [sumCircuit, Circuit.eval, roundedSumBit_accepts]

/-- Fixed-precision iterated addition has constant depth. -/
noncomputable def sumDepth (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  Finset.univ.sup fun bit => (arithmetic.roundedSumBit bit).circuitDepth

theorem sumCircuit_depth_le (arithmetic : FixedPrecisionArithmetic bits) (count : ℕ) :
    Circuit.depth (arithmetic.sumCircuit count) ≤ arithmetic.sumDepth := by
  simp only [sumCircuit, Circuit.depth, sumDepth]
  apply Finset.sup_le
  intro bit _
  exact (StarFree.depth_compile_le _ _).trans
    (Finset.le_sup (s := Finset.univ)
      (f := fun bit => (arithmetic.roundedSumBit bit).circuitDepth) (by simp))

/-- Fixed-precision iterated addition has polynomial gate count. -/
theorem sumCircuit_gateCount_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound
      (fun count => Circuit.gateCount (arithmetic.sumCircuit count)) := by
  have h := StarFree.PolynomialBound.finset_sum Finset.univ
    (fun bit count => Circuit.gateCount ((arithmetic.roundedSumBit bit).compile count))
    (by
      intro bit _
      exact StarFree.gateCount_compile_polynomial (arithmetic.roundedSumBit bit))
  simpa [sumCircuit, Circuit.gateCount] using h

/-- Canonical coefficient selected from the proved rounded-sum polynomial. -/
noncomputable def sumCoefficient (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  Classical.choose arithmetic.sumCircuit_gateCount_polynomial

/-- Canonical exponent selected from the proved rounded-sum polynomial. -/
noncomputable def sumExponent (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  Classical.choose (Classical.choose_spec arithmetic.sumCircuit_gateCount_polynomial)

theorem sumCircuit_gateCount_le (arithmetic : FixedPrecisionArithmetic bits) (count : ℕ) :
    Circuit.gateCount (arithmetic.sumCircuit count) ≤
      arithmetic.sumCoefficient * (count + 1) ^ arithmetic.sumExponent := by
  exact Classical.choose_spec
    (Classical.choose_spec arithmetic.sumCircuit_gateCount_polynomial) count

/-- A monotone upper envelope for all rounded sums of at most `bound` terms. -/
noncomputable def sumUpper (arithmetic : FixedPrecisionArithmetic bits) (bound : ℕ) : ℕ :=
  arithmetic.sumCoefficient * (bound + 1) ^ arithmetic.sumExponent

theorem sumCircuit_gateCount_le_upper (arithmetic : FixedPrecisionArithmetic bits)
    {count bound : ℕ} (h : count ≤ bound) :
    Circuit.gateCount (arithmetic.sumCircuit count) ≤ arithmetic.sumUpper bound := by
  exact (arithmetic.sumCircuit_gateCount_le count).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) _))

end FixedPrecisionArithmetic

/-! The following small combinators are the only building blocks used by the
matrix compiler.  Thus all high-level stages below expand to the four
constructors `andGate`, `orGate`, `notGate`, and free wiring. -/

namespace ScalarCircuit

/-- Gate budget for a vector-valued unary truth table. -/
def unaryTableCost (bits : ℕ) : ℕ :=
  bits * (Fintype.card (Bits bits) * (bits + 1) + 1)

/-- Gate budget for a vector-valued binary truth table. -/
def binaryTableCost (bits : ℕ) : ℕ :=
  bits * (Fintype.card (Bits (bits + bits)) * (bits + bits + 1) + 1)

/-- A fixed scalar constant. -/
def constant (inputBits : ℕ) (value : Bits bits) : Circuit inputBits bits :=
  .bundle fun bit => Circuit.const inputBits (value bit)

/-- Select one output bit from a scalar circuit. -/
def outputBit (circuit : Circuit inputBits bits) (bit : Fin bits) :
    Circuit inputBits 1 :=
  .seq circuit (.wire fun _ => bit)

/-- Bundle a family of scalar circuits into a scalar word. -/
def bundle (term : Fin count → Circuit inputBits bits) :
    Circuit inputBits (count * bits) :=
  .bundle fun index =>
    let location := finProdFinEquiv.symm index
    outputBit (term location.1) location.2

/-- Select one scalar block from a flat word. -/
def inputBlock (block : Fin count) : Circuit (count * bits) bits :=
  .wire fun bit => finProdFinEquiv (block, bit)

/-- Compile and apply a fixed-arity unary operation. -/
noncomputable def unary (operation : Bits bits → Bits bits)
    (input : Circuit inputBits bits) : Circuit inputBits bits :=
  .seq input (Circuit.ofFunction operation)

/-- Compile and apply a fixed-arity binary operation. -/
noncomputable def binary (operation : Bits (bits + bits) → Bits bits)
    (left right : Circuit inputBits bits) : Circuit inputBits bits :=
  .seq (.parallel left right) (Circuit.ofFunction operation)

/-- Apply the explicit rounded-sum circuit to a family of scalar terms. -/
noncomputable def aggregate (arithmetic : FixedPrecisionArithmetic bits)
    (term : Fin count → Circuit inputBits bits) : Circuit inputBits bits :=
  .seq (bundle term) (arithmetic.sumCircuit count)

/-- Two scalar terms, indexed without an auxiliary list. -/
def pair (left right : Circuit inputBits bits) : Fin 2 → Circuit inputBits bits :=
  Fin.cases left (fun tail => Fin.cases right Fin.elim0 tail)

/-- Flatten scalar words in the same row-major order used by `bundle`. -/
def pack (term : Fin count → Bits bits) : Bits (count * bits) := fun index =>
  let location := finProdFinEquiv.symm index
  term location.1 location.2

@[simp] theorem eval_constant (value : Bits bits) (input : Bits inputBits) :
    Circuit.eval (constant inputBits value) input = value := by
  funext bit
  simp [constant, Circuit.eval]

@[simp] theorem eval_outputBit (circuit : Circuit inputBits bits) (bit : Fin bits)
    (input : Bits inputBits) :
    Circuit.eval (outputBit circuit bit) input 0 = Circuit.eval circuit input bit := rfl

@[simp] theorem eval_bundle (term : Fin count → Circuit inputBits bits)
    (input : Bits inputBits) :
    Circuit.eval (bundle term) input = pack (fun index => Circuit.eval (term index) input) := by
  funext index
  simp [bundle, pack, Circuit.eval]

@[simp] theorem eval_inputBlock (block : Fin count) (input : Bits (count * bits)) :
    Circuit.eval (inputBlock (bits := bits) block) input =
      fun bit => input (finProdFinEquiv (block, bit)) := rfl

@[simp] theorem eval_unary (operation : Bits bits → Bits bits)
    (circuit : Circuit inputBits bits) (input : Bits inputBits) :
    Circuit.eval (unary operation circuit) input = operation (Circuit.eval circuit input) := by
  simp [unary, Circuit.eval]

@[simp] theorem eval_binary (operation : Bits (bits + bits) → Bits bits)
    (left right : Circuit inputBits bits) (input : Bits inputBits) :
    Circuit.eval (binary operation left right) input =
      operation (Fin.append (Circuit.eval left input) (Circuit.eval right input)) := by
  simp [binary, Circuit.eval]

@[simp] theorem eval_aggregate (arithmetic : FixedPrecisionArithmetic bits)
    (term : Fin count → Circuit inputBits bits) (input : Bits inputBits) :
    Circuit.eval (aggregate arithmetic term) input =
      arithmetic.roundedSum count
        (pack (fun index => Circuit.eval (term index) input)) := by
  simp [aggregate, Circuit.eval]

theorem depth_constant_le_one (inputBits : ℕ) (value : Bits bits) :
    Circuit.depth (constant inputBits value) ≤ 1 := by
  simp only [constant, Circuit.depth]
  apply Finset.sup_le
  intro bit _
  simp only [Circuit.const, Circuit.depth]
  split <;> simp [Circuit.depth]

@[simp] theorem depth_outputBit (circuit : Circuit inputBits bits) (bit : Fin bits) :
    Circuit.depth (outputBit circuit bit) = Circuit.depth circuit := by
  simp [outputBit, Circuit.depth]

theorem depth_bundle_le (term : Fin count → Circuit inputBits bits) (bound : ℕ)
    (hterm : ∀ index, Circuit.depth (term index) ≤ bound) :
    Circuit.depth (bundle term) ≤ bound := by
  simp only [bundle, Circuit.depth, depth_outputBit]
  apply Finset.sup_le
  intro index _
  exact hterm _

theorem depth_unary_le (operation : Bits bits → Bits bits)
    (input : Circuit inputBits bits) (bound : ℕ)
    (hinput : Circuit.depth input ≤ bound) :
    Circuit.depth (unary operation input) ≤ bound + 3 := by
  simp only [unary, Circuit.depth]
  exact Nat.add_le_add hinput (Circuit.depth_ofFunction_le_three operation)

theorem depth_binary_le (operation : Bits (bits + bits) → Bits bits)
    (left right : Circuit inputBits bits) (leftBound rightBound : ℕ)
    (hleft : Circuit.depth left ≤ leftBound) (hright : Circuit.depth right ≤ rightBound) :
    Circuit.depth (binary operation left right) ≤ max leftBound rightBound + 3 := by
  simp only [binary, Circuit.depth]
  exact Nat.add_le_add (max_le_max hleft hright)
    (Circuit.depth_ofFunction_le_three operation)

theorem depth_aggregate_le (arithmetic : FixedPrecisionArithmetic bits)
    (term : Fin count → Circuit inputBits bits) (termBound : ℕ)
    (hterm : ∀ index, Circuit.depth (term index) ≤ termBound) :
    Circuit.depth (aggregate arithmetic term) ≤ termBound + arithmetic.sumDepth := by
  simp only [aggregate, Circuit.depth]
  exact Nat.add_le_add (depth_bundle_le term termBound hterm)
    (arithmetic.sumCircuit_depth_le count)

@[simp] theorem gateCount_constant (inputBits : ℕ) (value : Bits bits) :
    Circuit.gateCount (constant inputBits value) = bits := by
  simp [constant, Circuit.gateCount, Circuit.gateCount_const]

@[simp] theorem gateCount_outputBit (circuit : Circuit inputBits bits) (bit : Fin bits) :
    Circuit.gateCount (outputBit circuit bit) = Circuit.gateCount circuit := by
  simp [outputBit, Circuit.gateCount]

theorem gateCount_bundle_le (term : Fin count → Circuit inputBits bits)
    (bound : ℕ) (hterm : ∀ index, Circuit.gateCount (term index) ≤ bound) :
    Circuit.gateCount (bundle term) ≤ (count * bits) * bound := by
  simp only [bundle, Circuit.gateCount, gateCount_outputBit]
  calc
    (∑ index : Fin (count * bits),
      Circuit.gateCount (term (finProdFinEquiv.symm index).1)) ≤
        ∑ _index : Fin (count * bits), bound := by
          apply Finset.sum_le_sum
          intro index _
          exact hterm _
    _ = (count * bits) * bound := by simp

theorem gateCount_unary_le (operation : Bits bits → Bits bits)
    (input : Circuit inputBits bits) :
    Circuit.gateCount (unary operation input) ≤
      Circuit.gateCount input + unaryTableCost bits := by
  simp only [unary, Circuit.gateCount, unaryTableCost]
  exact Nat.add_le_add_left (Circuit.gateCount_ofFunction_le operation) _

theorem gateCount_binary_le (operation : Bits (bits + bits) → Bits bits)
    (left right : Circuit inputBits bits) :
    Circuit.gateCount (binary operation left right) ≤
      Circuit.gateCount left + Circuit.gateCount right + binaryTableCost bits := by
  simp only [binary, Circuit.gateCount, binaryTableCost]
  exact Nat.add_le_add_left (Circuit.gateCount_ofFunction_le operation) _

theorem gateCount_aggregate_le (arithmetic : FixedPrecisionArithmetic bits)
    (term : Fin count → Circuit inputBits bits) (termBound sizeBound : ℕ)
    (hcount : count ≤ sizeBound)
    (hterm : ∀ index, Circuit.gateCount (term index) ≤ termBound) :
    Circuit.gateCount (aggregate arithmetic term) ≤
      (sizeBound * bits) * termBound + arithmetic.sumUpper sizeBound := by
  simp only [aggregate, Circuit.gateCount]
  exact Nat.add_le_add
    ((gateCount_bundle_le term termBound hterm).trans
      (Nat.mul_le_mul_right termBound (Nat.mul_le_mul_right bits hcount)))
    (arithmetic.sumCircuit_gateCount_le_upper hcount)

end ScalarCircuit

/-- Q/K/V and MLP parameters of one paper Transformer layer. -/
structure TransformerLayerParameters (a : Architecture) (bits : ℕ) where
  query : Fin a.heads → Fin a.hiddenWidth → Fin a.hiddenWidth → Bits bits
  key : Fin a.heads → Fin a.hiddenWidth → Fin a.hiddenWidth → Bits bits
  value : Fin a.heads → Fin a.hiddenWidth → Fin a.hiddenWidth → Bits bits
  mlpIn : Fin a.hiddenWidth → Fin a.hiddenWidth → Bits bits
  mlpOut : Fin a.hiddenWidth → Fin a.hiddenWidth → Bits bits

/--
The paper's matrix-level fixed-precision Transformer.  This structure stores
parameters and finite scalar operations only.  In particular it contains no
Boolean circuit, no layer function, and no realization certificate.
-/
structure FixedPrecisionTransformer (a : Architecture) where
  scalarBits : ℕ
  arithmetic : FixedPrecisionArithmetic scalarBits
  position : Fin a.contextLength → Fin a.halfWidth → Bits scalarBits
  tokenEmbedding : Fin a.vocabulary → Fin a.halfWidth → Bits scalarBits
  layer : Fin a.layers → TransformerLayerParameters a scalarBits
  readoutWeight : Fin a.vocabulary → Fin a.hiddenWidth → Bits scalarBits
  outputLabel : Fin a.vocabulary → Bool

/-! A gate-count recurrence mirroring the matrix compiler.  Its argument is
an upper bound for `N,D,H,|V|` and the constant arity two. -/
namespace TransformerGateCost

def constant (bits : ℕ) : ℕ := bits

def unary (bits inputCost : ℕ) : ℕ :=
  inputCost + ScalarCircuit.unaryTableCost bits

def binary (bits leftCost rightCost : ℕ) : ℕ :=
  leftCost + rightCost + ScalarCircuit.binaryTableCost bits

noncomputable def aggregate (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound termCost : ℕ) : ℕ :=
  (sizeBound * bits) * termCost + arithmetic.sumUpper sizeBound

noncomputable def linear (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound sourceCost : ℕ) : ℕ :=
  aggregate arithmetic sizeBound (binary bits (constant bits) sourceCost)

noncomputable def projected (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ := linear arithmetic sizeBound 0

noncomputable def score (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  aggregate arithmetic sizeBound
    (binary bits (projected arithmetic sizeBound) (projected arithmetic sizeBound))

noncomputable def expScore (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ := unary bits (score arithmetic sizeBound)

noncomputable def denominator (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  aggregate arithmetic sizeBound (expScore arithmetic sizeBound)

noncomputable def softmax (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  binary bits (expScore arithmetic sizeBound) (denominator arithmetic sizeBound)

noncomputable def headOutput (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  aggregate arithmetic sizeBound
    (binary bits (softmax arithmetic sizeBound) (projected arithmetic sizeBound))

noncomputable def attention (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  aggregate arithmetic sizeBound (headOutput arithmetic sizeBound)

noncomputable def attentionResidual (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  unary bits (aggregate arithmetic sizeBound (attention arithmetic sizeBound))

noncomputable def mlpHidden (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  unary bits (linear arithmetic sizeBound (attentionResidual arithmetic sizeBound))

noncomputable def mlpOutput (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  linear arithmetic sizeBound (mlpHidden arithmetic sizeBound)

noncomputable def layerScalar (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  unary bits (aggregate arithmetic sizeBound
    (attentionResidual arithmetic sizeBound + mlpOutput arithmetic sizeBound))

noncomputable def layer (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  (sizeBound * sizeBound * bits) * layerScalar arithmetic sizeBound

noncomputable def embedding (bits sizeBound : ℕ) : ℕ :=
  (sizeBound * sizeBound * bits) * (bits * (sizeBound + 1))

def predicateTableCost (bits : ℕ) : ℕ :=
  Fintype.card (Bits bits) * (bits + 1) + 1

noncomputable def readoutComparison (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  2 * linear arithmetic sizeBound 0 + predicateTableCost (bits + bits) + 1

noncomputable def readoutWinner (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  sizeBound * readoutComparison arithmetic sizeBound + 1

noncomputable def readout (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  sizeBound * (readoutWinner arithmetic sizeBound + 1) + 2

noncomputable def total (arithmetic : FixedPrecisionArithmetic bits)
    (sizeBound : ℕ) : ℕ :=
  embedding bits sizeBound + sizeBound * layer arithmetic sizeBound +
    readout arithmetic sizeBound

private theorem constant_polynomial (bits : ℕ) :
    StarFree.PolynomialBound (fun _ => constant bits) := by
  simpa [constant] using StarFree.PolynomialBound.const bits

private theorem unary_polynomial (bits : ℕ) {inputCost : ℕ → ℕ}
    (hinput : StarFree.PolynomialBound inputCost) :
    StarFree.PolynomialBound (fun n => unary bits (inputCost n)) := by
  simpa [unary] using hinput.add
    (StarFree.PolynomialBound.const (ScalarCircuit.unaryTableCost bits))

private theorem binary_polynomial (bits : ℕ) {leftCost rightCost : ℕ → ℕ}
    (hleft : StarFree.PolynomialBound leftCost)
    (hright : StarFree.PolynomialBound rightCost) :
    StarFree.PolynomialBound
      (fun n => binary bits (leftCost n) (rightCost n)) := by
  simpa [binary] using (hleft.add hright).add
    (StarFree.PolynomialBound.const (ScalarCircuit.binaryTableCost bits))

private theorem sumUpper_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound arithmetic.sumUpper := by
  exact ⟨arithmetic.sumCoefficient, arithmetic.sumExponent, fun _ => le_rfl⟩

private theorem aggregate_polynomial (arithmetic : FixedPrecisionArithmetic bits)
    {termCost : ℕ → ℕ} (hterm : StarFree.PolynomialBound termCost) :
    StarFree.PolynomialBound
      (fun n => aggregate arithmetic n (termCost n)) := by
  have hfactor : StarFree.PolynomialBound (fun n => n * bits) :=
    StarFree.PolynomialBound.identity.mul (StarFree.PolynomialBound.const bits)
  simpa [aggregate] using (hfactor.mul hterm).add (sumUpper_polynomial arithmetic)

private theorem linear_polynomial (arithmetic : FixedPrecisionArithmetic bits)
    {sourceCost : ℕ → ℕ} (hsource : StarFree.PolynomialBound sourceCost) :
    StarFree.PolynomialBound
      (fun n => linear arithmetic n (sourceCost n)) := by
  apply aggregate_polynomial
  exact binary_polynomial bits (constant_polynomial bits) hsource

private theorem projected_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (projected arithmetic) := by
  simpa [projected] using linear_polynomial arithmetic StarFree.PolynomialBound.zero

private theorem score_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (score arithmetic) := by
  apply aggregate_polynomial
  exact binary_polynomial bits (projected_polynomial arithmetic)
    (projected_polynomial arithmetic)

private theorem expScore_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (expScore arithmetic) := by
  exact unary_polynomial bits (score_polynomial arithmetic)

private theorem denominator_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (denominator arithmetic) := by
  exact aggregate_polynomial arithmetic (expScore_polynomial arithmetic)

private theorem softmax_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (softmax arithmetic) := by
  exact binary_polynomial bits (expScore_polynomial arithmetic)
    (denominator_polynomial arithmetic)

private theorem headOutput_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (headOutput arithmetic) := by
  apply aggregate_polynomial
  exact binary_polynomial bits (softmax_polynomial arithmetic)
    (projected_polynomial arithmetic)

private theorem attention_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (attention arithmetic) := by
  exact aggregate_polynomial arithmetic (headOutput_polynomial arithmetic)

private theorem attentionResidual_polynomial
    (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (attentionResidual arithmetic) := by
  apply unary_polynomial
  exact aggregate_polynomial arithmetic (attention_polynomial arithmetic)

private theorem mlpHidden_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (mlpHidden arithmetic) := by
  apply unary_polynomial
  exact linear_polynomial arithmetic (attentionResidual_polynomial arithmetic)

private theorem mlpOutput_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (mlpOutput arithmetic) := by
  exact linear_polynomial arithmetic (mlpHidden_polynomial arithmetic)

private theorem layerScalar_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (layerScalar arithmetic) := by
  apply unary_polynomial
  apply aggregate_polynomial
  exact (attentionResidual_polynomial arithmetic).add (mlpOutput_polynomial arithmetic)

private theorem layer_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (layer arithmetic) := by
  have hfactor : StarFree.PolynomialBound (fun n => n * n * bits) :=
    (StarFree.PolynomialBound.identity.mul StarFree.PolynomialBound.identity).mul
      (StarFree.PolynomialBound.const bits)
  exact hfactor.mul (layerScalar_polynomial arithmetic)

private theorem embedding_polynomial (bits : ℕ) :
    StarFree.PolynomialBound (embedding bits) := by
  have hleft : StarFree.PolynomialBound (fun n => n * n * bits) :=
    (StarFree.PolynomialBound.identity.mul StarFree.PolynomialBound.identity).mul
      (StarFree.PolynomialBound.const bits)
  have hright : StarFree.PolynomialBound (fun n => bits * (n + 1)) :=
    (StarFree.PolynomialBound.const bits).mul StarFree.PolynomialBound.successor
  exact hleft.mul hright

private theorem readout_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (readout arithmetic) := by
  have hlinear := linear_polynomial arithmetic StarFree.PolynomialBound.zero
  have hcomparison : StarFree.PolynomialBound (readoutComparison arithmetic) := by
    change StarFree.PolynomialBound (fun n =>
      2 * linear arithmetic n 0 + predicateTableCost (bits + bits) + 1)
    simpa [readoutComparison, two_mul] using
      ((hlinear.add hlinear).add
        (StarFree.PolynomialBound.const (predicateTableCost (bits + bits)))).add
        (StarFree.PolynomialBound.const 1)
  have hwinner : StarFree.PolynomialBound (readoutWinner arithmetic) := by
    simpa [readoutWinner] using
      (StarFree.PolynomialBound.identity.mul hcomparison).add
        (StarFree.PolynomialBound.const 1)
  simpa [readout] using
    (StarFree.PolynomialBound.identity.mul
      (hwinner.add (StarFree.PolynomialBound.const 1))).add
      (StarFree.PolynomialBound.const 2)

/-- The architecture recurrence is genuinely polynomial; its witnesses depend
only on the fixed scalar precision and rounded-sum programs. -/
theorem total_polynomial (arithmetic : FixedPrecisionArithmetic bits) :
    StarFree.PolynomialBound (total arithmetic) := by
  have hlayers : StarFree.PolynomialBound
      (fun n => n * layer arithmetic n) :=
    StarFree.PolynomialBound.identity.mul (layer_polynomial arithmetic)
  simpa [total] using
    (embedding_polynomial bits).add hlayers |>.add (readout_polynomial arithmetic)

end TransformerGateCost

/-! The corresponding recurrence for depth has no architecture-size
argument: fanin changes width and gate count, but never adds depth. -/
namespace TransformerDepthCost

def constant : ℕ := 1
def unary (inputDepth : ℕ) : ℕ := inputDepth + 3
def binary (leftDepth rightDepth : ℕ) : ℕ := max leftDepth rightDepth + 3
noncomputable def aggregate (arithmetic : FixedPrecisionArithmetic bits) (termDepth : ℕ) : ℕ :=
  termDepth + arithmetic.sumDepth
noncomputable def linear (arithmetic : FixedPrecisionArithmetic bits) (sourceDepth : ℕ) : ℕ :=
  aggregate arithmetic (binary constant sourceDepth)
noncomputable def projected (arithmetic : FixedPrecisionArithmetic bits) : ℕ := linear arithmetic 0
noncomputable def score (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  aggregate arithmetic (binary (projected arithmetic) (projected arithmetic))
noncomputable def expScore (arithmetic : FixedPrecisionArithmetic bits) : ℕ := unary (score arithmetic)
noncomputable def denominator (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  aggregate arithmetic (expScore arithmetic)
noncomputable def softmax (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  binary (expScore arithmetic) (denominator arithmetic)
noncomputable def headOutput (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  aggregate arithmetic (binary (softmax arithmetic) (projected arithmetic))
noncomputable def attention (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  aggregate arithmetic (headOutput arithmetic)
noncomputable def attentionResidual (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  unary (aggregate arithmetic (max 0 (attention arithmetic)))
noncomputable def mlpHidden (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  unary (linear arithmetic (attentionResidual arithmetic))
noncomputable def mlpOutput (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  linear arithmetic (mlpHidden arithmetic)
noncomputable def layerScalar (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  unary (aggregate arithmetic
    (max (attentionResidual arithmetic) (mlpOutput arithmetic)))
noncomputable def layer (arithmetic : FixedPrecisionArithmetic bits) : ℕ := layerScalar arithmetic
def embedding : ℕ := 2
noncomputable def readout (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  linear arithmetic 0 + 6
noncomputable def stage (arithmetic : FixedPrecisionArithmetic bits) : ℕ :=
  max embedding (max (readout arithmetic) (layer arithmetic))

end TransformerDepthCost

namespace FixedPrecisionTransformer

/-- Number of Boolean wires in the sequence of hidden scalars. -/
def stateBitWidth (T : FixedPrecisionTransformer a) : ℕ :=
  a.stateBits * T.scalarBits

def inputIndex {a : Architecture} (position : Fin a.contextLength)
    (token : Fin a.vocabulary) :
    Fin a.inputBits := finProdFinEquiv (position, token)

def stateBlock {a : Architecture} (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) : Fin a.stateBits :=
  finProdFinEquiv (position, coordinate)

def hiddenSplit {a : Architecture} (coordinate : Fin a.hiddenWidth) :
    Fin a.halfWidth ⊕ Fin a.halfWidth :=
  finSumFinEquiv.symm
    (Fin.cast (by simp [Architecture.hiddenWidth]; omega) coordinate)

/-- Select one hidden scalar from the layer input. -/
def stateInput (T : FixedPrecisionTransformer a) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) : Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.inputBlock (stateBlock position coordinate)

/-- Token-table lookup from one-hot input bits. -/
noncomputable def tokenScalarCircuit (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (coordinate : Fin a.halfWidth) :
    Circuit a.inputBits T.scalarBits :=
  .bundle fun bit =>
    .seq
      (.bundle fun token : Fin a.vocabulary =>
        if T.tokenEmbedding token coordinate bit then
          .wire fun _ => inputIndex position token
        else Circuit.const a.inputBits false)
      (.orGate a.vocabulary)

/-- One concatenated token/position embedding scalar. -/
noncomputable def embeddingScalarCircuit (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit a.inputBits T.scalarBits :=
  match hiddenSplit coordinate with
  | .inl tokenCoordinate => T.tokenScalarCircuit position tokenCoordinate
  | .inr positionCoordinate =>
      ScalarCircuit.constant a.inputBits (T.position position positionCoordinate)

/-- Construct the complete embedding circuit. -/
noncomputable def embeddingCircuit (T : FixedPrecisionTransformer a) :
    Circuit a.inputBits T.stateBitWidth :=
  .bundle fun index =>
    let bitLocation := finProdFinEquiv.symm index
    let stateLocation := finProdFinEquiv.symm bitLocation.1
    ScalarCircuit.outputBit
      (T.embeddingScalarCircuit stateLocation.1 stateLocation.2) bitLocation.2

/-- A rounded matrix-vector coordinate. -/
noncomputable def linearCircuit (T : FixedPrecisionTransformer a)
    (matrix : Fin a.hiddenWidth → Fin a.hiddenWidth → Bits T.scalarBits)
    (source : Fin a.hiddenWidth → Circuit T.stateBitWidth T.scalarBits)
    (output : Fin a.hiddenWidth) : Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.aggregate T.arithmetic fun input =>
    ScalarCircuit.binary T.arithmetic.multiply
      (ScalarCircuit.constant T.stateBitWidth (matrix output input)) (source input)

/-- Query projection for one head and position. -/
noncomputable def queryCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  T.linearCircuit (parameters.query head) (T.stateInput position) coordinate

/-- Key projection for one head and position. -/
noncomputable def keyCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  T.linearCircuit (parameters.key head) (T.stateInput position) coordinate

/-- Value projection for one head and position. -/
noncomputable def valueCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  T.linearCircuit (parameters.value head) (T.stateInput position) coordinate

/-- Rounded query/key inner product. -/
noncomputable def scoreCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.aggregate T.arithmetic fun coordinate =>
    ScalarCircuit.binary T.arithmetic.multiply
      (T.queryCircuit parameters head queryPosition coordinate)
      (T.keyCircuit parameters head keyPosition coordinate)

/-- Fixed-precision exponentiation of an attention score. -/
noncomputable def expScoreCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.unary T.arithmetic.exponentiate
    (T.scoreCircuit parameters head queryPosition keyPosition)

private def causalPosition {a : Architecture} (position : Fin a.contextLength)
    (index : Fin (position.val + 1)) : Fin a.contextLength :=
  Fin.castLE (Nat.succ_le_iff.mpr position.isLt) index

/-- Softmax denominator over the causal prefix. -/
noncomputable def denominatorCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) : Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.aggregate T.arithmetic fun index =>
    T.expScoreCircuit parameters head position (causalPosition position index)

/-- One fixed-precision softmax weight (exp, rounded sum, division). -/
noncomputable def softmaxCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.binary T.arithmetic.divide
    (T.expScoreCircuit parameters head queryPosition keyPosition)
    (T.denominatorCircuit parameters head queryPosition)

/-- Weighted value sum for one attention head. -/
noncomputable def headOutputCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.aggregate T.arithmetic fun index =>
    let keyPosition := causalPosition position index
    ScalarCircuit.binary T.arithmetic.multiply
      (T.softmaxCircuit parameters head position keyPosition)
      (T.valueCircuit parameters head keyPosition coordinate)

/-- Rounded aggregation over all heads. -/
noncomputable def attentionCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.aggregate T.arithmetic fun head =>
    T.headOutputCircuit parameters head position coordinate

/-- First residual addition and rounding. -/
noncomputable def attentionResidualCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.unary T.arithmetic.round
    (ScalarCircuit.aggregate T.arithmetic
      (ScalarCircuit.pair (T.stateInput position coordinate)
        (T.attentionCircuit parameters position coordinate)))

/-- Input affine map and ReLU of the MLP. -/
noncomputable def mlpHiddenCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.unary T.arithmetic.relu
    (T.linearCircuit parameters.mlpIn
      (T.attentionResidualCircuit parameters position) coordinate)

/-- Output affine map of the MLP. -/
noncomputable def mlpOutputCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  T.linearCircuit parameters.mlpOut (T.mlpHiddenCircuit parameters position) coordinate

/-- Second residual addition and rounding. -/
noncomputable def layerOutputScalarCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.unary T.arithmetic.round
    (ScalarCircuit.aggregate T.arithmetic
      (ScalarCircuit.pair (T.attentionResidualCircuit parameters position coordinate)
        (T.mlpOutputCircuit parameters position coordinate)))

/-- Construct one complete multihead-attention/MLP layer. -/
noncomputable def layerCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) :
    Circuit T.stateBitWidth T.stateBitWidth :=
  .bundle fun index =>
    let bitLocation := finProdFinEquiv.symm index
    let stateLocation := finProdFinEquiv.symm bitLocation.1
    ScalarCircuit.outputBit
      (T.layerOutputScalarCircuit parameters stateLocation.1 stateLocation.2)
      bitLocation.2

/-- Final-position unembedding inner product. -/
noncomputable def readoutScalarCircuit (T : FixedPrecisionTransformer a)
    (token : Fin a.vocabulary) (position : Fin a.contextLength) :
    Circuit T.stateBitWidth T.scalarBits :=
  ScalarCircuit.aggregate T.arithmetic fun coordinate =>
    ScalarCircuit.binary T.arithmetic.multiply
      (ScalarCircuit.constant T.stateBitWidth (T.readoutWeight token coordinate))
      (T.stateInput position coordinate)

/-- Compare one candidate logit with one challenger.  Earlier indices win
ties, giving a deterministic greedy readout. -/
noncomputable def readoutComparisonCircuit (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (candidate challenger : Fin a.vocabulary) :
    Circuit T.stateBitWidth 1 :=
  if _h : candidate = challenger then Circuit.const T.stateBitWidth true
  else if challenger.val < candidate.val then
    .seq
      (.parallel (T.readoutScalarCircuit candidate position)
        (T.readoutScalarCircuit challenger position))
      (.seq (Circuit.ofPredicate T.arithmetic.lessEqual) .notGate)
  else
    .seq
      (.parallel (T.readoutScalarCircuit challenger position)
        (T.readoutScalarCircuit candidate position))
      (Circuit.ofPredicate T.arithmetic.lessEqual)

/-- The candidate is the least-indexed maximizer of all output logits. -/
noncomputable def readoutWinnerCircuit (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (candidate : Fin a.vocabulary) :
    Circuit T.stateBitWidth 1 :=
  .seq (.bundle fun challenger =>
    T.readoutComparisonCircuit position candidate challenger)
    (.andGate a.vocabulary)

/-- Construct all unembedding logits, greedy selection, and Boolean label
readout. -/
noncomputable def readoutCircuit (T : FixedPrecisionTransformer a) :
    Circuit T.stateBitWidth 1 :=
  if h : 0 < a.contextLength then
    let finalPosition : Fin a.contextLength := ⟨a.contextLength - 1, by omega⟩
    .seq
      (.bundle fun token =>
        if T.outputLabel token then T.readoutWinnerCircuit finalPosition token
        else Circuit.const T.stateBitWidth false)
      (.orGate a.vocabulary)
  else Circuit.const T.stateBitWidth false

/-! ### Independent matrix semantics -/

/-- Read one fixed-precision scalar from a flattened hidden state. -/
def stateValue (T : FixedPrecisionTransformer a) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Bits T.scalarBits := fun bit =>
  state (finProdFinEquiv (stateBlock position coordinate, bit))

/-- Semantics of a finite family of fixed-precision summands. -/
def aggregateValues (T : FixedPrecisionTransformer a)
    (term : Fin count → Bits T.scalarBits) : Bits T.scalarBits :=
  T.arithmetic.roundedSum count (ScalarCircuit.pack term)

/-- Semantics of a binary fixed-precision operation. -/
def binaryValue (operation : Bits (bits + bits) → Bits bits)
    (left right : Bits bits) : Bits bits := operation (Fin.append left right)

def pairValues (left right : α) : Fin 2 → α :=
  Fin.cases left (fun tail => Fin.cases right Fin.elim0 tail)

@[simp] theorem eval_circuitPair (left right : Circuit inputBits bits)
    (input : Bits inputBits) :
    (fun index => Circuit.eval (ScalarCircuit.pair left right index) input) =
      pairValues (Circuit.eval left input) (Circuit.eval right input) := by
  funext index
  fin_cases index <;> rfl

/-- Token lookup semantics, defined for every Boolean input (not only valid
one-hot words). -/
def tokenScalarValue (T : FixedPrecisionTransformer a)
    (input : Bits a.inputBits) (position : Fin a.contextLength)
    (coordinate : Fin a.halfWidth) : Bits T.scalarBits := fun bit =>
  decide (∃ token : Fin a.vocabulary,
    T.tokenEmbedding token coordinate bit = true ∧ input (inputIndex position token) = true)

/-- Semantics of one concatenated token/position embedding scalar. -/
def embeddingScalarValue (T : FixedPrecisionTransformer a)
    (input : Bits a.inputBits) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) : Bits T.scalarBits :=
  match hiddenSplit coordinate with
  | .inl tokenCoordinate => T.tokenScalarValue input position tokenCoordinate
  | .inr positionCoordinate => T.position position positionCoordinate

/-- Independent semantics of the complete embedding table lookup. -/
def embeddingValue (T : FixedPrecisionTransformer a)
    (input : Bits a.inputBits) : Bits T.stateBitWidth := fun index =>
  let bitLocation := finProdFinEquiv.symm index
  let stateLocation := finProdFinEquiv.symm bitLocation.1
  T.embeddingScalarValue input stateLocation.1 stateLocation.2 bitLocation.2

/-- Semantics of a rounded matrix-vector coordinate. -/
def linearValue (T : FixedPrecisionTransformer a)
    (matrix : Fin a.hiddenWidth → Fin a.hiddenWidth → Bits T.scalarBits)
    (source : Fin a.hiddenWidth → Bits T.scalarBits)
    (output : Fin a.hiddenWidth) : Bits T.scalarBits :=
  T.aggregateValues fun input =>
    binaryValue T.arithmetic.multiply (matrix output input) (source input)

def queryValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) : Bits T.scalarBits :=
  T.linearValue (parameters.query head) (T.stateValue state position) coordinate

def keyValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) : Bits T.scalarBits :=
  T.linearValue (parameters.key head) (T.stateValue state position) coordinate

def valueValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) : Bits T.scalarBits :=
  T.linearValue (parameters.value head) (T.stateValue state position) coordinate

def scoreValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (queryPosition keyPosition : Fin a.contextLength) :
    Bits T.scalarBits :=
  T.aggregateValues fun coordinate => binaryValue T.arithmetic.multiply
    (T.queryValue parameters state head queryPosition coordinate)
    (T.keyValue parameters state head keyPosition coordinate)

def expScoreValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (queryPosition keyPosition : Fin a.contextLength) :
    Bits T.scalarBits :=
  T.arithmetic.exponentiate
    (T.scoreValue parameters state head queryPosition keyPosition)

def denominatorValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength) : Bits T.scalarBits :=
  T.aggregateValues fun index =>
    T.expScoreValue parameters state head position (causalPosition position index)

def softmaxValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (queryPosition keyPosition : Fin a.contextLength) :
    Bits T.scalarBits :=
  binaryValue T.arithmetic.divide
    (T.expScoreValue parameters state head queryPosition keyPosition)
    (T.denominatorValue parameters state head queryPosition)

def headOutputValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) : Bits T.scalarBits :=
  T.aggregateValues fun index =>
    let keyPosition := causalPosition position index
    binaryValue T.arithmetic.multiply
      (T.softmaxValue parameters state head position keyPosition)
      (T.valueValue parameters state head keyPosition coordinate)

def attentionValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Bits T.scalarBits :=
  T.aggregateValues fun head =>
    T.headOutputValue parameters state head position coordinate

def attentionResidualValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Bits T.scalarBits :=
  T.arithmetic.round (T.aggregateValues (pairValues
    (T.stateValue state position coordinate)
    (T.attentionValue parameters state position coordinate)))

def mlpHiddenValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Bits T.scalarBits :=
  T.arithmetic.relu (T.linearValue parameters.mlpIn
    (T.attentionResidualValue parameters state position) coordinate)

def mlpOutputValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Bits T.scalarBits :=
  T.linearValue parameters.mlpOut (T.mlpHiddenValue parameters state position) coordinate

def layerOutputScalarValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Bits T.scalarBits :=
  T.arithmetic.round (T.aggregateValues (pairValues
    (T.attentionResidualValue parameters state position coordinate)
    (T.mlpOutputValue parameters state position coordinate)))

/-- Independent semantics of one full multihead-attention/MLP layer. -/
def layerValue (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (state : Bits T.stateBitWidth) : Bits T.stateBitWidth := fun index =>
  let bitLocation := finProdFinEquiv.symm index
  let stateLocation := finProdFinEquiv.symm bitLocation.1
  T.layerOutputScalarValue parameters state stateLocation.1 stateLocation.2 bitLocation.2

def readoutScalarValue (T : FixedPrecisionTransformer a)
    (state : Bits T.stateBitWidth) (position : Fin a.contextLength)
    (token : Fin a.vocabulary) : Bits T.scalarBits :=
  T.aggregateValues fun coordinate => binaryValue T.arithmetic.multiply
    (T.readoutWeight token coordinate) (T.stateValue state position coordinate)

def readoutComparisonValue (T : FixedPrecisionTransformer a)
    (state : Bits T.stateBitWidth) (position : Fin a.contextLength)
    (candidate challenger : Fin a.vocabulary) : Bool :=
  if candidate = challenger then true
  else if challenger.val < candidate.val then
    !(T.arithmetic.lessEqual (Fin.append
      (T.readoutScalarValue state position candidate)
      (T.readoutScalarValue state position challenger)))
  else T.arithmetic.lessEqual (Fin.append
    (T.readoutScalarValue state position challenger)
    (T.readoutScalarValue state position candidate))

def readoutWinnerValue (T : FixedPrecisionTransformer a)
    (state : Bits T.stateBitWidth) (position : Fin a.contextLength)
    (candidate : Fin a.vocabulary) : Bool :=
  decide (∀ challenger : Fin a.vocabulary,
    T.readoutComparisonValue state position candidate challenger = true)

def readoutValue (T : FixedPrecisionTransformer a) (state : Bits T.stateBitWidth) : Bool :=
  if h : 0 < a.contextLength then
    let finalPosition : Fin a.contextLength := ⟨a.contextLength - 1, by omega⟩
    decide (∃ token : Fin a.vocabulary,
      T.outputLabel token = true ∧ T.readoutWinnerValue state finalPosition token = true)
  else false

/-- Construct the `L` layer circuits from the parameter array. -/
noncomputable def layerCircuits (T : FixedPrecisionTransformer a) :
    List (Circuit T.stateBitWidth T.stateBitWidth) :=
  List.ofFn fun layer => T.layerCircuit (T.layer layer)

/-- Full matrix-level compilation to the AND/OR/NOT basis. -/
noncomputable def compile (T : FixedPrecisionTransformer a) : Circuit a.inputBits 1 :=
  .seq T.embeddingCircuit (.seq (Circuit.serial T.layerCircuits) T.readoutCircuit)

/-- Independent matrix/arithmetic semantics of the Transformer. -/
def run (T : FixedPrecisionTransformer a) (input : Bits a.inputBits) : Bool :=
  T.readoutValue
    ((List.ofFn T.layer).foldl (fun state parameters => T.layerValue parameters state)
      (T.embeddingValue input))

/-! ### Correctness of every generated stage -/

@[simp] theorem eval_stateInput (T : FixedPrecisionTransformer a)
    (state : Bits T.stateBitWidth) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.stateInput position coordinate) state =
      T.stateValue state position coordinate := rfl

@[simp] theorem eval_tokenScalarCircuit (T : FixedPrecisionTransformer a)
    (input : Bits a.inputBits) (position : Fin a.contextLength)
    (coordinate : Fin a.halfWidth) :
    Circuit.eval (T.tokenScalarCircuit position coordinate) input =
      T.tokenScalarValue input position coordinate := by
  funext bit
  simp only [tokenScalarCircuit, tokenScalarValue, Circuit.eval]
  congr 1
  apply propext
  constructor
  · rintro ⟨token, htoken⟩
    by_cases hbit : T.tokenEmbedding token coordinate bit = true
    · exact ⟨token, hbit, by simpa [hbit, Circuit.eval] using htoken⟩
    · simp [hbit, Circuit.eval] at htoken
  · rintro ⟨token, hbit, hinput⟩
    exact ⟨token, by simp [hbit, hinput, Circuit.eval]⟩

@[simp] theorem eval_embeddingScalarCircuit (T : FixedPrecisionTransformer a)
    (input : Bits a.inputBits) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.embeddingScalarCircuit position coordinate) input =
      T.embeddingScalarValue input position coordinate := by
  simp only [embeddingScalarCircuit, embeddingScalarValue]
  split <;> simp

@[simp] theorem eval_embeddingCircuit (T : FixedPrecisionTransformer a)
    (input : Bits a.inputBits) :
    Circuit.eval T.embeddingCircuit input = T.embeddingValue input := by
  funext index
  simp [embeddingCircuit, embeddingValue, Circuit.eval]

@[simp] theorem eval_linearCircuit (T : FixedPrecisionTransformer a)
    (matrix : Fin a.hiddenWidth → Fin a.hiddenWidth → Bits T.scalarBits)
    (source : Fin a.hiddenWidth → Circuit T.stateBitWidth T.scalarBits)
    (output : Fin a.hiddenWidth) (state : Bits T.stateBitWidth) :
    Circuit.eval (T.linearCircuit matrix source output) state =
      T.linearValue matrix (fun input => Circuit.eval (source input) state) output := by
  simp [linearCircuit, linearValue, aggregateValues, binaryValue]

@[simp] theorem eval_queryCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.queryCircuit parameters head position coordinate) state =
      T.queryValue parameters state head position coordinate := by
  simp [queryCircuit, queryValue]

@[simp] theorem eval_keyCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.keyCircuit parameters head position coordinate) state =
      T.keyValue parameters state head position coordinate := by
  simp [keyCircuit, keyValue]

@[simp] theorem eval_valueCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.valueCircuit parameters head position coordinate) state =
      T.valueValue parameters state head position coordinate := by
  simp [valueCircuit, valueValue]

@[simp] theorem eval_scoreCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.eval (T.scoreCircuit parameters head queryPosition keyPosition) state =
      T.scoreValue parameters state head queryPosition keyPosition := by
  simp [scoreCircuit, scoreValue, aggregateValues, binaryValue]

@[simp] theorem eval_expScoreCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.eval (T.expScoreCircuit parameters head queryPosition keyPosition) state =
      T.expScoreValue parameters state head queryPosition keyPosition := by
  simp [expScoreCircuit, expScoreValue]

@[simp] theorem eval_denominatorCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength) :
    Circuit.eval (T.denominatorCircuit parameters head position) state =
      T.denominatorValue parameters state head position := by
  simp [denominatorCircuit, denominatorValue, aggregateValues]

@[simp] theorem eval_softmaxCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.eval (T.softmaxCircuit parameters head queryPosition keyPosition) state =
      T.softmaxValue parameters state head queryPosition keyPosition := by
  simp [softmaxCircuit, softmaxValue, binaryValue]

@[simp] theorem eval_headOutputCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (head : Fin a.heads) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.headOutputCircuit parameters head position coordinate) state =
      T.headOutputValue parameters state head position coordinate := by
  simp [headOutputCircuit, headOutputValue, aggregateValues, binaryValue]

@[simp] theorem eval_attentionCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.attentionCircuit parameters position coordinate) state =
      T.attentionValue parameters state position coordinate := by
  simp [attentionCircuit, attentionValue, aggregateValues]

@[simp] theorem eval_attentionResidualCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.attentionResidualCircuit parameters position coordinate) state =
      T.attentionResidualValue parameters state position coordinate := by
  simp [attentionResidualCircuit, attentionResidualValue, aggregateValues]

@[simp] theorem eval_mlpHiddenCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.mlpHiddenCircuit parameters position coordinate) state =
      T.mlpHiddenValue parameters state position coordinate := by
  simp [mlpHiddenCircuit, mlpHiddenValue]

@[simp] theorem eval_mlpOutputCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.mlpOutputCircuit parameters position coordinate) state =
      T.mlpOutputValue parameters state position coordinate := by
  simp [mlpOutputCircuit, mlpOutputValue]

@[simp] theorem eval_layerOutputScalarCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.eval (T.layerOutputScalarCircuit parameters position coordinate) state =
      T.layerOutputScalarValue parameters state position coordinate := by
  simp [layerOutputScalarCircuit, layerOutputScalarValue, aggregateValues]

@[simp] theorem eval_layerCircuit (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (state : Bits T.stateBitWidth) :
    Circuit.eval (T.layerCircuit parameters) state = T.layerValue parameters state := by
  funext index
  simp [layerCircuit, layerValue, Circuit.eval]

@[simp] theorem eval_readoutScalarCircuit (T : FixedPrecisionTransformer a)
    (state : Bits T.stateBitWidth) (position : Fin a.contextLength)
    (token : Fin a.vocabulary) :
    Circuit.eval (T.readoutScalarCircuit token position) state =
      T.readoutScalarValue state position token := by
  simp [readoutScalarCircuit, readoutScalarValue, aggregateValues, binaryValue]

@[simp] theorem eval_readoutComparisonCircuit (T : FixedPrecisionTransformer a)
    (state : Bits T.stateBitWidth) (position : Fin a.contextLength)
    (candidate challenger : Fin a.vocabulary) :
    Circuit.eval (T.readoutComparisonCircuit position candidate challenger) state 0 =
      T.readoutComparisonValue state position candidate challenger := by
  rw [readoutComparisonCircuit, readoutComparisonValue]
  by_cases heq : candidate = challenger
  · simp [heq, Circuit.eval]
  · simp only [heq, ↓reduceIte]
    by_cases horder : challenger.val < candidate.val
    · simp [horder, Circuit.eval]
    · simp [horder, Circuit.eval]

@[simp] theorem eval_readoutWinnerCircuit (T : FixedPrecisionTransformer a)
    (state : Bits T.stateBitWidth) (position : Fin a.contextLength)
    (candidate : Fin a.vocabulary) :
    Circuit.eval (T.readoutWinnerCircuit position candidate) state 0 =
      T.readoutWinnerValue state position candidate := by
  simp [readoutWinnerCircuit, readoutWinnerValue, Circuit.eval]

@[simp] theorem eval_readoutCircuit (T : FixedPrecisionTransformer a)
    (state : Bits T.stateBitWidth) :
    Circuit.eval T.readoutCircuit state 0 = T.readoutValue state := by
  simp only [readoutCircuit, readoutValue]
  split
  · simp only [Circuit.eval]
    congr 1
    apply propext
    constructor
    · rintro ⟨token, htoken⟩
      by_cases hlabel : T.outputLabel token = true
      · exact ⟨token, hlabel, by simpa [hlabel, Circuit.eval] using htoken⟩
      · simp [hlabel, Circuit.eval] at htoken
    · rintro ⟨token, hlabel, hwinner⟩
      exact ⟨token, by simp [hlabel, hwinner, Circuit.eval]⟩
  · simp [Circuit.eval]

private theorem runSerial_layerCircuits (T : FixedPrecisionTransformer a)
    (parameters : List (TransformerLayerParameters a T.scalarBits))
    (state : Bits T.stateBitWidth) :
    Circuit.runSerial (parameters.map T.layerCircuit) state =
      parameters.foldl (fun current layer => T.layerValue layer current) state := by
  induction parameters generalizing state with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, Circuit.runSerial, List.foldl_cons]
      rw [T.eval_layerCircuit]
      exact ih _

/-- The generated circuit computes the independently defined matrix
semantics, for every Boolean input. -/
@[simp] theorem compile_correct (T : FixedPrecisionTransformer a)
    (input : Bits a.inputBits) : Circuit.eval T.compile input 0 = T.run input := by
  simp only [compile, Circuit.eval, T.eval_embeddingCircuit, Circuit.eval_serial,
    layerCircuits, run, T.eval_readoutCircuit]
  apply congrArg T.readoutValue
  simpa [List.map_ofFn] using
    (T.runSerial_layerCircuits (List.ofFn T.layer) (T.embeddingValue input))

/-! ### Architecture-independent depth bounds -/

private theorem linearCircuit_depth_le (T : FixedPrecisionTransformer a)
    (matrix : Fin a.hiddenWidth → Fin a.hiddenWidth → Bits T.scalarBits)
    (source : Fin a.hiddenWidth → Circuit T.stateBitWidth T.scalarBits)
    (sourceDepth : ℕ) (hsource : ∀ coordinate, Circuit.depth (source coordinate) ≤ sourceDepth)
    (output : Fin a.hiddenWidth) :
    Circuit.depth (T.linearCircuit matrix source output) ≤
      TransformerDepthCost.linear T.arithmetic sourceDepth := by
  apply ScalarCircuit.depth_aggregate_le
  intro input
  apply ScalarCircuit.depth_binary_le _ _ _ TransformerDepthCost.constant sourceDepth
  · exact ScalarCircuit.depth_constant_le_one _ _
  · exact hsource input

private theorem projected_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.queryCircuit parameters head position coordinate) ≤
      TransformerDepthCost.projected T.arithmetic := by
  apply T.linearCircuit_depth_le _ _ 0
  intro input
  simp [stateInput, ScalarCircuit.inputBlock, Circuit.depth]

private theorem key_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.keyCircuit parameters head position coordinate) ≤
      TransformerDepthCost.projected T.arithmetic := by
  apply T.linearCircuit_depth_le _ _ 0
  intro input
  simp [stateInput, ScalarCircuit.inputBlock, Circuit.depth]

private theorem value_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.valueCircuit parameters head position coordinate) ≤
      TransformerDepthCost.projected T.arithmetic := by
  apply T.linearCircuit_depth_le _ _ 0
  intro input
  simp [stateInput, ScalarCircuit.inputBlock, Circuit.depth]

private theorem score_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.depth (T.scoreCircuit parameters head queryPosition keyPosition) ≤
      TransformerDepthCost.score T.arithmetic := by
  apply ScalarCircuit.depth_aggregate_le
  intro coordinate
  apply ScalarCircuit.depth_binary_le
  · exact T.projected_depth_le parameters head queryPosition coordinate
  · exact T.key_depth_le parameters head keyPosition coordinate

private theorem expScore_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.depth (T.expScoreCircuit parameters head queryPosition keyPosition) ≤
      TransformerDepthCost.expScore T.arithmetic := by
  apply ScalarCircuit.depth_unary_le
  exact T.score_depth_le parameters head queryPosition keyPosition

private theorem denominator_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) :
    Circuit.depth (T.denominatorCircuit parameters head position) ≤
      TransformerDepthCost.denominator T.arithmetic := by
  apply ScalarCircuit.depth_aggregate_le
  intro index
  exact T.expScore_depth_le parameters head position (causalPosition position index)

private theorem softmax_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.depth (T.softmaxCircuit parameters head queryPosition keyPosition) ≤
      TransformerDepthCost.softmax T.arithmetic := by
  apply ScalarCircuit.depth_binary_le
  · exact T.expScore_depth_le parameters head queryPosition keyPosition
  · exact T.denominator_depth_le parameters head queryPosition

private theorem headOutput_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.headOutputCircuit parameters head position coordinate) ≤
      TransformerDepthCost.headOutput T.arithmetic := by
  apply ScalarCircuit.depth_aggregate_le
  intro index
  apply ScalarCircuit.depth_binary_le
  · exact T.softmax_depth_le parameters head position (causalPosition position index)
  · exact T.value_depth_le parameters head (causalPosition position index) coordinate

private theorem attention_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.attentionCircuit parameters position coordinate) ≤
      TransformerDepthCost.attention T.arithmetic := by
  apply ScalarCircuit.depth_aggregate_le
  intro head
  exact T.headOutput_depth_le parameters head position coordinate

private theorem attentionResidual_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.attentionResidualCircuit parameters position coordinate) ≤
      TransformerDepthCost.attentionResidual T.arithmetic := by
  apply ScalarCircuit.depth_unary_le
  apply ScalarCircuit.depth_aggregate_le
  intro index
  fin_cases index
  · simp [ScalarCircuit.pair, stateInput, ScalarCircuit.inputBlock, Circuit.depth]
  · exact (T.attention_depth_le parameters position coordinate).trans
      (Nat.le_max_right _ _)

private theorem mlpHidden_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.mlpHiddenCircuit parameters position coordinate) ≤
      TransformerDepthCost.mlpHidden T.arithmetic := by
  apply ScalarCircuit.depth_unary_le
  apply T.linearCircuit_depth_le
  intro input
  exact T.attentionResidual_depth_le parameters position input

private theorem mlpOutput_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.mlpOutputCircuit parameters position coordinate) ≤
      TransformerDepthCost.mlpOutput T.arithmetic := by
  apply T.linearCircuit_depth_le
  intro input
  exact T.mlpHidden_depth_le parameters position input

private theorem layerOutputScalar_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.layerOutputScalarCircuit parameters position coordinate) ≤
      TransformerDepthCost.layerScalar T.arithmetic := by
  apply ScalarCircuit.depth_unary_le
  apply ScalarCircuit.depth_aggregate_le
  intro index
  fin_cases index
  · exact (T.attentionResidual_depth_le parameters position coordinate).trans
      (Nat.le_max_left _ _)
  · exact (T.mlpOutput_depth_le parameters position coordinate).trans
      (Nat.le_max_right _ _)

private theorem layerCircuit_depth_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) :
    Circuit.depth (T.layerCircuit parameters) ≤
      TransformerDepthCost.layer T.arithmetic := by
  apply Finset.sup_le
  intro index _
  simpa [layerCircuit, Circuit.depth] using
    T.layerOutputScalar_depth_le parameters
      (finProdFinEquiv.symm (finProdFinEquiv.symm index).1).1
      (finProdFinEquiv.symm (finProdFinEquiv.symm index).1).2

private theorem tokenScalarCircuit_depth_le (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (coordinate : Fin a.halfWidth) :
    Circuit.depth (T.tokenScalarCircuit position coordinate) ≤
      TransformerDepthCost.embedding := by
  simp only [tokenScalarCircuit, Circuit.depth, TransformerDepthCost.embedding]
  apply Finset.sup_le
  intro bit _
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro token _
  split
  · simp [Circuit.depth]
  · simp [Circuit.const, Circuit.depth]

private theorem embeddingScalarCircuit_depth_le (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.depth (T.embeddingScalarCircuit position coordinate) ≤
      TransformerDepthCost.embedding := by
  simp only [embeddingScalarCircuit]
  split
  · exact T.tokenScalarCircuit_depth_le position _
  · exact (ScalarCircuit.depth_constant_le_one _ _).trans (by decide)

private theorem embeddingCircuit_depth_le (T : FixedPrecisionTransformer a) :
    Circuit.depth T.embeddingCircuit ≤ TransformerDepthCost.embedding := by
  simp only [embeddingCircuit, Circuit.depth, ScalarCircuit.depth_outputBit]
  apply Finset.sup_le
  intro index _
  exact T.embeddingScalarCircuit_depth_le _ _

private theorem readoutScalarCircuit_depth_le (T : FixedPrecisionTransformer a)
    (token : Fin a.vocabulary) (position : Fin a.contextLength) :
    Circuit.depth (T.readoutScalarCircuit token position) ≤
      TransformerDepthCost.linear T.arithmetic 0 := by
  apply ScalarCircuit.depth_aggregate_le
  intro coordinate
  apply ScalarCircuit.depth_binary_le
  · exact ScalarCircuit.depth_constant_le_one _ _
  · simp [stateInput, ScalarCircuit.inputBlock, Circuit.depth]

private theorem readoutComparisonCircuit_depth_le (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (candidate challenger : Fin a.vocabulary) :
    Circuit.depth (T.readoutComparisonCircuit position candidate challenger) ≤
      TransformerDepthCost.linear T.arithmetic 0 + 4 := by
  rw [readoutComparisonCircuit]
  split_ifs with heq horder
  · have hconst : Circuit.depth (Circuit.const T.stateBitWidth true) ≤ 1 := by
      simp [Circuit.const, Circuit.depth]
    omega
  · simp only [Circuit.depth]
    apply Nat.add_le_add
    · exact max_le (T.readoutScalarCircuit_depth_le candidate position)
        (T.readoutScalarCircuit_depth_le challenger position)
    · have hpredicate := Circuit.depth_ofPredicate_le_three T.arithmetic.lessEqual
      omega
  · simp only [Circuit.depth]
    have hpairs := max_le (T.readoutScalarCircuit_depth_le challenger position)
      (T.readoutScalarCircuit_depth_le candidate position)
    have hpredicate := Circuit.depth_ofPredicate_le_three T.arithmetic.lessEqual
    omega

private theorem readoutWinnerCircuit_depth_le (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (candidate : Fin a.vocabulary) :
    Circuit.depth (T.readoutWinnerCircuit position candidate) ≤
      TransformerDepthCost.linear T.arithmetic 0 + 5 := by
  simp only [readoutWinnerCircuit, Circuit.depth]
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro challenger _
  exact T.readoutComparisonCircuit_depth_le position candidate challenger

private theorem readoutCircuit_depth_le (T : FixedPrecisionTransformer a) :
    Circuit.depth T.readoutCircuit ≤ TransformerDepthCost.readout T.arithmetic := by
  rw [readoutCircuit]
  split_ifs with h
  · dsimp only
    simp only [Circuit.depth, TransformerDepthCost.readout]
    apply Nat.add_le_add_right
    apply Finset.sup_le
    intro token _
    split
    · exact T.readoutWinnerCircuit_depth_le _ token
    · have hconst : Circuit.depth (Circuit.const T.stateBitWidth false) ≤ 1 := by
        simp [Circuit.const, Circuit.depth]
      omega
  · have hconst : Circuit.depth (Circuit.const T.stateBitWidth false) ≤ 1 := by
      simp [Circuit.const, Circuit.depth]
    simp only [TransformerDepthCost.readout]
    omega

/-! ### Gate bounds for every generated stage -/

def sizeBound (a : Architecture) : ℕ := a.localBase + a.layers + 2

private theorem contextLength_le_sizeBound (a : Architecture) :
    a.contextLength ≤ sizeBound a := by
  simp [sizeBound, Architecture.localBase]
  omega

private theorem hiddenWidth_le_sizeBound (a : Architecture) :
    a.hiddenWidth ≤ sizeBound a := by
  simp [sizeBound, Architecture.localBase]
  omega

private theorem heads_le_sizeBound (a : Architecture) :
    a.heads ≤ sizeBound a := by
  simp [sizeBound, Architecture.localBase]
  omega

private theorem vocabulary_le_sizeBound (a : Architecture) :
    a.vocabulary ≤ sizeBound a := by
  simp [sizeBound, Architecture.localBase]
  omega

private theorem layers_le_sizeBound (a : Architecture) :
    a.layers ≤ sizeBound a := by
  simp [sizeBound, Architecture.localBase]
  omega

private theorem two_le_sizeBound (a : Architecture) : 2 ≤ sizeBound a := by
  simp [sizeBound, Architecture.localBase]

private theorem stateBits_le_square_sizeBound (a : Architecture) :
    a.stateBits ≤ sizeBound a * sizeBound a := by
  exact Nat.mul_le_mul (contextLength_le_sizeBound a) (hiddenWidth_le_sizeBound a)

private theorem linearCircuit_gateCount_le (T : FixedPrecisionTransformer a)
    (matrix : Fin a.hiddenWidth → Fin a.hiddenWidth → Bits T.scalarBits)
    (source : Fin a.hiddenWidth → Circuit T.stateBitWidth T.scalarBits)
    (sourceCost : ℕ)
    (hsource : ∀ coordinate, Circuit.gateCount (source coordinate) ≤ sourceCost)
    (output : Fin a.hiddenWidth) :
    Circuit.gateCount (T.linearCircuit matrix source output) ≤
      TransformerGateCost.linear T.arithmetic (sizeBound a) sourceCost := by
  apply ScalarCircuit.gateCount_aggregate_le T.arithmetic _
    (TransformerGateCost.binary T.scalarBits
      (TransformerGateCost.constant T.scalarBits) sourceCost) (sizeBound a)
    (hiddenWidth_le_sizeBound a)
  intro input
  apply (ScalarCircuit.gateCount_binary_le T.arithmetic.multiply _ _).trans
  simp only [ScalarCircuit.gateCount_constant, TransformerGateCost.binary,
    TransformerGateCost.constant]
  exact Nat.add_le_add_right (Nat.add_le_add_left (hsource input) _) _

private theorem projected_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.queryCircuit parameters head position coordinate) ≤
      TransformerGateCost.projected T.arithmetic (sizeBound a) := by
  apply T.linearCircuit_gateCount_le _ _ 0
  intro input
  simp [stateInput, ScalarCircuit.inputBlock, Circuit.gateCount]

private theorem key_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.keyCircuit parameters head position coordinate) ≤
      TransformerGateCost.projected T.arithmetic (sizeBound a) := by
  apply T.linearCircuit_gateCount_le _ _ 0
  intro input
  simp [stateInput, ScalarCircuit.inputBlock, Circuit.gateCount]

private theorem value_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.valueCircuit parameters head position coordinate) ≤
      TransformerGateCost.projected T.arithmetic (sizeBound a) := by
  apply T.linearCircuit_gateCount_le _ _ 0
  intro input
  simp [stateInput, ScalarCircuit.inputBlock, Circuit.gateCount]

private theorem score_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.gateCount (T.scoreCircuit parameters head queryPosition keyPosition) ≤
      TransformerGateCost.score T.arithmetic (sizeBound a) := by
  apply ScalarCircuit.gateCount_aggregate_le T.arithmetic _
    (TransformerGateCost.binary T.scalarBits
      (TransformerGateCost.projected T.arithmetic (sizeBound a))
      (TransformerGateCost.projected T.arithmetic (sizeBound a)))
    (sizeBound a) (hiddenWidth_le_sizeBound a)
  intro coordinate
  exact (ScalarCircuit.gateCount_binary_le T.arithmetic.multiply _ _).trans
    (Nat.add_le_add
      (Nat.add_le_add (T.projected_gateCount_le parameters head queryPosition coordinate)
        (T.key_gateCount_le parameters head keyPosition coordinate))
      (Nat.le_refl _))

private theorem expScore_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.gateCount (T.expScoreCircuit parameters head queryPosition keyPosition) ≤
      TransformerGateCost.expScore T.arithmetic (sizeBound a) := by
  exact (ScalarCircuit.gateCount_unary_le T.arithmetic.exponentiate _).trans
    (Nat.add_le_add_right
      (T.score_gateCount_le parameters head queryPosition keyPosition) _)

private theorem denominator_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) :
    Circuit.gateCount (T.denominatorCircuit parameters head position) ≤
      TransformerGateCost.denominator T.arithmetic (sizeBound a) := by
  apply ScalarCircuit.gateCount_aggregate_le T.arithmetic _
    (TransformerGateCost.expScore T.arithmetic (sizeBound a)) (sizeBound a)
  · exact (Nat.succ_le_iff.mpr position.isLt).trans
      (contextLength_le_sizeBound a)
  · intro index
    exact T.expScore_gateCount_le parameters head position (causalPosition position index)

private theorem softmax_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (queryPosition keyPosition : Fin a.contextLength) :
    Circuit.gateCount (T.softmaxCircuit parameters head queryPosition keyPosition) ≤
      TransformerGateCost.softmax T.arithmetic (sizeBound a) := by
  exact (ScalarCircuit.gateCount_binary_le T.arithmetic.divide _ _).trans
    (Nat.add_le_add
      (Nat.add_le_add
        (T.expScore_gateCount_le parameters head queryPosition keyPosition)
        (T.denominator_gateCount_le parameters head queryPosition))
      (Nat.le_refl _))

private theorem headOutput_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) (head : Fin a.heads)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.headOutputCircuit parameters head position coordinate) ≤
      TransformerGateCost.headOutput T.arithmetic (sizeBound a) := by
  apply ScalarCircuit.gateCount_aggregate_le T.arithmetic _
    (TransformerGateCost.binary T.scalarBits
      (TransformerGateCost.softmax T.arithmetic (sizeBound a))
      (TransformerGateCost.projected T.arithmetic (sizeBound a)))
    (sizeBound a)
  · exact (Nat.succ_le_iff.mpr position.isLt).trans
      (contextLength_le_sizeBound a)
  · intro index
    exact (ScalarCircuit.gateCount_binary_le T.arithmetic.multiply _ _).trans
      (Nat.add_le_add
        (Nat.add_le_add
          (T.softmax_gateCount_le parameters head position (causalPosition position index))
          (T.value_gateCount_le parameters head (causalPosition position index) coordinate))
        (Nat.le_refl _))

private theorem attention_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.attentionCircuit parameters position coordinate) ≤
      TransformerGateCost.attention T.arithmetic (sizeBound a) := by
  apply ScalarCircuit.gateCount_aggregate_le T.arithmetic _
    (TransformerGateCost.headOutput T.arithmetic (sizeBound a))
    (sizeBound a) (heads_le_sizeBound a)
  intro head
  exact T.headOutput_gateCount_le parameters head position coordinate

private theorem attentionResidual_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.attentionResidualCircuit parameters position coordinate) ≤
      TransformerGateCost.attentionResidual T.arithmetic (sizeBound a) := by
  apply (ScalarCircuit.gateCount_unary_le T.arithmetic.round _).trans
  apply Nat.add_le_add_right
  apply ScalarCircuit.gateCount_aggregate_le T.arithmetic _
    (TransformerGateCost.attention T.arithmetic (sizeBound a))
    (sizeBound a) (two_le_sizeBound a)
  intro index
  fin_cases index
  · simp [ScalarCircuit.pair, stateInput, ScalarCircuit.inputBlock, Circuit.gateCount]
  · exact T.attention_gateCount_le parameters position coordinate

private theorem mlpHidden_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.mlpHiddenCircuit parameters position coordinate) ≤
      TransformerGateCost.mlpHidden T.arithmetic (sizeBound a) := by
  apply (ScalarCircuit.gateCount_unary_le T.arithmetic.relu _).trans
  apply Nat.add_le_add_right
  apply T.linearCircuit_gateCount_le _ _
    (TransformerGateCost.attentionResidual T.arithmetic (sizeBound a))
  intro input
  exact T.attentionResidual_gateCount_le parameters position input

private theorem mlpOutput_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.mlpOutputCircuit parameters position coordinate) ≤
      TransformerGateCost.mlpOutput T.arithmetic (sizeBound a) := by
  apply T.linearCircuit_gateCount_le _ _
    (TransformerGateCost.mlpHidden T.arithmetic (sizeBound a))
  intro input
  exact T.mlpHidden_gateCount_le parameters position input

private theorem layerOutputScalar_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits)
    (position : Fin a.contextLength) (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.layerOutputScalarCircuit parameters position coordinate) ≤
      TransformerGateCost.layerScalar T.arithmetic (sizeBound a) := by
  apply (ScalarCircuit.gateCount_unary_le T.arithmetic.round _).trans
  apply Nat.add_le_add_right
  apply ScalarCircuit.gateCount_aggregate_le T.arithmetic _
    (TransformerGateCost.attentionResidual T.arithmetic (sizeBound a) +
      TransformerGateCost.mlpOutput T.arithmetic (sizeBound a))
    (sizeBound a) (two_le_sizeBound a)
  intro index
  fin_cases index
  · exact (T.attentionResidual_gateCount_le parameters position coordinate).trans
      (Nat.le_add_right _ _)
  · exact (T.mlpOutput_gateCount_le parameters position coordinate).trans
      (Nat.le_add_left _ _)

private theorem layerCircuit_gateCount_le (T : FixedPrecisionTransformer a)
    (parameters : TransformerLayerParameters a T.scalarBits) :
    Circuit.gateCount (T.layerCircuit parameters) ≤
      TransformerGateCost.layer T.arithmetic (sizeBound a) := by
  simp only [layerCircuit, Circuit.gateCount, ScalarCircuit.gateCount_outputBit]
  calc
    (∑ index : Fin T.stateBitWidth,
        Circuit.gateCount
          (T.layerOutputScalarCircuit parameters
            (finProdFinEquiv.symm (finProdFinEquiv.symm index).1).1
            (finProdFinEquiv.symm (finProdFinEquiv.symm index).1).2)) ≤
        ∑ _index : Fin T.stateBitWidth,
          TransformerGateCost.layerScalar T.arithmetic (sizeBound a) := by
            apply Finset.sum_le_sum
            intro index _
            exact T.layerOutputScalar_gateCount_le parameters _ _
    _ = T.stateBitWidth *
          TransformerGateCost.layerScalar T.arithmetic (sizeBound a) := by simp
    _ ≤ (sizeBound a * sizeBound a * T.scalarBits) *
          TransformerGateCost.layerScalar T.arithmetic (sizeBound a) := by
            apply Nat.mul_le_mul_right
            simp only [stateBitWidth]
            exact Nat.mul_le_mul_right T.scalarBits
              (stateBits_le_square_sizeBound a)
    _ = TransformerGateCost.layer T.arithmetic (sizeBound a) := rfl

private theorem tokenScalarCircuit_gateCount_le (T : FixedPrecisionTransformer a)
    (position : Fin a.contextLength) (coordinate : Fin a.halfWidth) :
    Circuit.gateCount (T.tokenScalarCircuit position coordinate) ≤
      T.scalarBits * (sizeBound a + 1) := by
  simp only [tokenScalarCircuit, Circuit.gateCount]
  calc
    (∑ bit : Fin T.scalarBits,
        ((∑ token : Fin a.vocabulary,
          Circuit.gateCount
            (if T.tokenEmbedding token coordinate bit then
              .wire fun _ => inputIndex position token
            else Circuit.const a.inputBits false)) + 1)) ≤
        ∑ _bit : Fin T.scalarBits, (sizeBound a + 1) := by
          apply Finset.sum_le_sum
          intro bit _
          apply Nat.add_le_add_right
          calc
            (∑ token : Fin a.vocabulary,
                Circuit.gateCount
                  (if T.tokenEmbedding token coordinate bit then
                    .wire fun _ => inputIndex position token
                  else Circuit.const a.inputBits false)) ≤
                ∑ _token : Fin a.vocabulary, 1 := by
                  apply Finset.sum_le_sum
                  intro token _
                  split <;> simp [Circuit.gateCount, Circuit.gateCount_const]
            _ = a.vocabulary := by simp
            _ ≤ sizeBound a := vocabulary_le_sizeBound a
    _ = T.scalarBits * (sizeBound a + 1) := by simp

private theorem embeddingScalarCircuit_gateCount_le
    (T : FixedPrecisionTransformer a) (position : Fin a.contextLength)
    (coordinate : Fin a.hiddenWidth) :
    Circuit.gateCount (T.embeddingScalarCircuit position coordinate) ≤
      T.scalarBits * (sizeBound a + 1) := by
  simp only [embeddingScalarCircuit]
  split
  · exact T.tokenScalarCircuit_gateCount_le position _
  · rw [ScalarCircuit.gateCount_constant]
    exact Nat.le_mul_of_pos_right _ (by omega)

private theorem embeddingCircuit_gateCount_le (T : FixedPrecisionTransformer a) :
    Circuit.gateCount T.embeddingCircuit ≤
      TransformerGateCost.embedding T.scalarBits (sizeBound a) := by
  simp only [embeddingCircuit, Circuit.gateCount, ScalarCircuit.gateCount_outputBit]
  calc
    (∑ index : Fin T.stateBitWidth,
        Circuit.gateCount
          (T.embeddingScalarCircuit
            (finProdFinEquiv.symm (finProdFinEquiv.symm index).1).1
            (finProdFinEquiv.symm (finProdFinEquiv.symm index).1).2)) ≤
        ∑ _index : Fin T.stateBitWidth,
          (T.scalarBits * (sizeBound a + 1)) := by
            apply Finset.sum_le_sum
            intro index _
            exact T.embeddingScalarCircuit_gateCount_le _ _
    _ = T.stateBitWidth * (T.scalarBits * (sizeBound a + 1)) := by simp
    _ ≤ (sizeBound a * sizeBound a * T.scalarBits) *
          (T.scalarBits * (sizeBound a + 1)) := by
            apply Nat.mul_le_mul_right
            simp only [stateBitWidth]
            exact Nat.mul_le_mul_right T.scalarBits
              (stateBits_le_square_sizeBound a)
    _ = TransformerGateCost.embedding T.scalarBits (sizeBound a) := rfl

private theorem readoutScalarCircuit_gateCount_le
    (T : FixedPrecisionTransformer a) (token : Fin a.vocabulary)
    (position : Fin a.contextLength) :
    Circuit.gateCount (T.readoutScalarCircuit token position) ≤
      TransformerGateCost.linear T.arithmetic (sizeBound a) 0 := by
  apply ScalarCircuit.gateCount_aggregate_le T.arithmetic _
    (TransformerGateCost.binary T.scalarBits
      (TransformerGateCost.constant T.scalarBits) 0)
    (sizeBound a) (hiddenWidth_le_sizeBound a)
  intro coordinate
  apply (ScalarCircuit.gateCount_binary_le T.arithmetic.multiply _ _).trans
  simp [TransformerGateCost.binary, TransformerGateCost.constant, stateInput,
    ScalarCircuit.inputBlock, Circuit.gateCount]

private theorem readoutComparisonCircuit_gateCount_le
    (T : FixedPrecisionTransformer a) (position : Fin a.contextLength)
    (candidate challenger : Fin a.vocabulary) :
    Circuit.gateCount (T.readoutComparisonCircuit position candidate challenger) ≤
      TransformerGateCost.readoutComparison T.arithmetic (sizeBound a) := by
  rw [readoutComparisonCircuit]
  split_ifs with heq horder
  · rw [Circuit.gateCount_const]
    simp [TransformerGateCost.readoutComparison]
  · simp only [Circuit.gateCount]
    have hpairs := Nat.add_le_add
      (T.readoutScalarCircuit_gateCount_le candidate position)
      (T.readoutScalarCircuit_gateCount_le challenger position)
    have hpredicate := Circuit.gateCount_ofPredicate_le T.arithmetic.lessEqual
    simp only [TransformerGateCost.readoutComparison,
      TransformerGateCost.predicateTableCost]
    omega
  · simp only [Circuit.gateCount]
    have hpairs := Nat.add_le_add
      (T.readoutScalarCircuit_gateCount_le challenger position)
      (T.readoutScalarCircuit_gateCount_le candidate position)
    have hpredicate := Circuit.gateCount_ofPredicate_le T.arithmetic.lessEqual
    simp only [TransformerGateCost.readoutComparison,
      TransformerGateCost.predicateTableCost]
    omega

private theorem readoutWinnerCircuit_gateCount_le
    (T : FixedPrecisionTransformer a) (position : Fin a.contextLength)
    (candidate : Fin a.vocabulary) :
    Circuit.gateCount (T.readoutWinnerCircuit position candidate) ≤
      TransformerGateCost.readoutWinner T.arithmetic (sizeBound a) := by
  simp only [readoutWinnerCircuit, Circuit.gateCount]
  apply Nat.add_le_add_right
  calc
    (∑ challenger : Fin a.vocabulary,
        Circuit.gateCount (T.readoutComparisonCircuit position candidate challenger)) ≤
        ∑ _challenger : Fin a.vocabulary,
          TransformerGateCost.readoutComparison T.arithmetic (sizeBound a) := by
            apply Finset.sum_le_sum
            intro challenger _
            exact T.readoutComparisonCircuit_gateCount_le position candidate challenger
    _ = a.vocabulary *
          TransformerGateCost.readoutComparison T.arithmetic (sizeBound a) := by simp
    _ ≤ sizeBound a *
          TransformerGateCost.readoutComparison T.arithmetic (sizeBound a) :=
      Nat.mul_le_mul_right _ (vocabulary_le_sizeBound a)

private theorem readoutCircuit_gateCount_le (T : FixedPrecisionTransformer a) :
    Circuit.gateCount T.readoutCircuit ≤
      TransformerGateCost.readout T.arithmetic (sizeBound a) := by
  rw [readoutCircuit]
  split_ifs with h
  · dsimp only
    simp only [Circuit.gateCount]
    have hsum : (∑ token : Fin a.vocabulary,
          Circuit.gateCount
            (if T.outputLabel token then
              T.readoutWinnerCircuit ⟨a.contextLength - 1, by omega⟩ token
             else Circuit.const T.stateBitWidth false)) ≤
        sizeBound a *
          (TransformerGateCost.readoutWinner T.arithmetic (sizeBound a) + 1) := by
      calc
        (∑ token : Fin a.vocabulary,
            Circuit.gateCount
              (if T.outputLabel token then
                T.readoutWinnerCircuit ⟨a.contextLength - 1, by omega⟩ token
               else Circuit.const T.stateBitWidth false)) ≤
            ∑ _token : Fin a.vocabulary,
              (TransformerGateCost.readoutWinner T.arithmetic (sizeBound a) + 1) := by
              apply Finset.sum_le_sum
              intro token _
              split
              · exact (T.readoutWinnerCircuit_gateCount_le _ token).trans
                  (Nat.le_add_right _ _)
              · rw [Circuit.gateCount_const]
                omega
        _ = a.vocabulary *
            (TransformerGateCost.readoutWinner T.arithmetic (sizeBound a) + 1) := by simp
        _ ≤ sizeBound a *
            (TransformerGateCost.readoutWinner T.arithmetic (sizeBound a) + 1) :=
          Nat.mul_le_mul_right _ (vocabulary_le_sizeBound a)
    calc
      (∑ token : Fin a.vocabulary,
          Circuit.gateCount
            (if T.outputLabel token then
              T.readoutWinnerCircuit ⟨a.contextLength - 1, by omega⟩ token
             else Circuit.const T.stateBitWidth false)) + 1 ≤
          sizeBound a *
            (TransformerGateCost.readoutWinner T.arithmetic (sizeBound a) + 1) + 1 :=
        Nat.add_le_add_right hsum 1
      _ ≤ TransformerGateCost.readout T.arithmetic (sizeBound a) := by
        simp [TransformerGateCost.readout]
  · rw [Circuit.gateCount_const]
    simp [TransformerGateCost.readout]

/-- Maximum generated stage depth, computed rather than assumed. -/
noncomputable def localDepth (T : FixedPrecisionTransformer a) : ℕ :=
  max (Circuit.depth T.embeddingCircuit)
    (max (Circuit.depth T.readoutCircuit)
      (T.layerCircuits.foldl (fun bound circuit => max bound circuit.depth) 0))

private theorem initial_le_foldl_circuitDepth
    (circuits : List (Circuit n n)) (initial : ℕ) :
    initial ≤ circuits.foldl (fun bound circuit => max bound circuit.depth) initial := by
  induction circuits generalizing initial with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.foldl_cons]
      exact (Nat.le_max_left _ _).trans (ih _)

private theorem circuit_depth_le_fold {circuits : List (Circuit n n)}
    {circuit : Circuit n n} (h : circuit ∈ circuits) (initial : ℕ) :
    circuit.depth ≤ circuits.foldl (fun bound current => max bound current.depth) initial := by
  induction circuits generalizing initial with
  | nil => simp at h
  | cons head rest ih =>
      simp only [List.mem_cons] at h
      simp only [List.foldl_cons]
      rcases h with rfl | h
      · exact (Nat.le_max_right _ _).trans (initial_le_foldl_circuitDepth rest _)
      · exact ih h _

private theorem foldl_circuitDepth_le (circuits : List (Circuit n n))
    (initial bound : ℕ) (hinitial : initial ≤ bound)
    (hcircuits : ∀ circuit ∈ circuits, Circuit.depth circuit ≤ bound) :
    circuits.foldl (fun current circuit => max current circuit.depth) initial ≤ bound := by
  induction circuits generalizing initial with
  | nil => exact hinitial
  | cons head tail ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact max_le hinitial (hcircuits head (by simp))
      · intro circuit hcircuit
        exact hcircuits circuit (by simp [hcircuit])

/-- The computed local depth is bounded by a number depending only on the
fixed scalar arithmetic, not on context length, width, heads, vocabulary, or
matrix entries. -/
theorem localDepth_le_fixed (T : FixedPrecisionTransformer a) :
    T.localDepth ≤ TransformerDepthCost.stage T.arithmetic := by
  simp only [localDepth]
  apply max_le
  · exact T.embeddingCircuit_depth_le.trans (Nat.le_max_left _ _)
  · apply max_le
    · exact T.readoutCircuit_depth_le.trans
        ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
    · apply foldl_circuitDepth_le _ 0
      · simp
      · intro circuit hcircuit
        obtain ⟨layer, hlayer, rfl⟩ := List.mem_ofFn.1
          (by simpa [layerCircuits] using hcircuit)
        exact (T.layerCircuit_depth_le (T.layer layer)).trans
          ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

private theorem list_sum_le_length_mul {xs : List ℕ} {bound : ℕ}
    (h : ∀ x ∈ xs, x ≤ bound) : xs.sum ≤ xs.length * bound := by
  simpa [nsmul_eq_mul] using List.sum_le_card_nsmul xs bound h

/-- Serial composition gives depth at most `(L+2)` times the generated local
depth. -/
theorem compile_depth_le (T : FixedPrecisionTransformer a) :
    Circuit.depth T.compile ≤ (a.layers + 2) * T.localDepth := by
  have hembedding : Circuit.depth T.embeddingCircuit ≤ T.localDepth :=
    Nat.le_max_left _ _
  have hreadout : Circuit.depth T.readoutCircuit ≤ T.localDepth :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hlayers : (T.layerCircuits.map Circuit.depth).sum ≤
      a.layers * T.localDepth := by
    calc
      (T.layerCircuits.map Circuit.depth).sum ≤
          T.layerCircuits.length * T.localDepth := by
        simpa using (list_sum_le_length_mul (xs := T.layerCircuits.map Circuit.depth)
          (bound := T.localDepth) (by
            intro depth hdepth
            obtain ⟨circuit, hcircuit, rfl⟩ := List.mem_map.1 hdepth
            exact (circuit_depth_le_fold hcircuit 0).trans
              ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
      _ = a.layers * T.localDepth := by simp [layerCircuits]
  simp only [compile, Circuit.depth, Circuit.depth_serial]
  calc
    Circuit.depth T.embeddingCircuit +
        ((T.layerCircuits.map Circuit.depth).sum + Circuit.depth T.readoutCircuit) ≤
        T.localDepth + (a.layers * T.localDepth + T.localDepth) :=
      Nat.add_le_add hembedding (Nat.add_le_add hlayers hreadout)
    _ = (a.layers + 2) * T.localDepth := by ring

/-- Uniform fixed-precision depth bound. -/
theorem compile_depth_le_fixed (T : FixedPrecisionTransformer a) :
    Circuit.depth T.compile ≤
      (a.layers + 2) * TransformerDepthCost.stage T.arithmetic := by
  exact T.compile_depth_le.trans
    (Nat.mul_le_mul_left (a.layers + 2) T.localDepth_le_fixed)

/-- Exact gate count of the generated embedding, layers, and readout. -/
noncomputable def localGateBudget (T : FixedPrecisionTransformer a) : ℕ :=
  Circuit.gateCount T.embeddingCircuit +
    (T.layerCircuits.map Circuit.gateCount).sum + Circuit.gateCount T.readoutCircuit

theorem compile_gateCount_eq_budget (T : FixedPrecisionTransformer a) :
    Circuit.gateCount T.compile = T.localGateBudget := by
  simp [compile, localGateBudget, Circuit.gateCount, Circuit.gateCount_serial]
  ring

/-- The exact generated budget is bounded by the architecture recurrence. -/
theorem localGateBudget_le_total (T : FixedPrecisionTransformer a) :
    T.localGateBudget ≤ TransformerGateCost.total T.arithmetic (sizeBound a) := by
  rw [localGateBudget]
  have hlayers : (T.layerCircuits.map Circuit.gateCount).sum ≤
      sizeBound a * TransformerGateCost.layer T.arithmetic (sizeBound a) := by
    calc
      (T.layerCircuits.map Circuit.gateCount).sum ≤
          T.layerCircuits.length *
            TransformerGateCost.layer T.arithmetic (sizeBound a) := by
              simpa using (list_sum_le_length_mul
                (xs := T.layerCircuits.map Circuit.gateCount)
                (bound := TransformerGateCost.layer T.arithmetic (sizeBound a)) (by
                  intro count hcount
                  obtain ⟨circuit, hcircuit, rfl⟩ := List.mem_map.1 hcount
                  obtain ⟨layer, hlayer, rfl⟩ := List.mem_ofFn.1
                    (by simpa [layerCircuits] using hcircuit)
                  exact T.layerCircuit_gateCount_le (T.layer layer)))
      _ = a.layers * TransformerGateCost.layer T.arithmetic (sizeBound a) := by
            simp [layerCircuits]
      _ ≤ sizeBound a * TransformerGateCost.layer T.arithmetic (sizeBound a) :=
            Nat.mul_le_mul_right _ (layers_le_sizeBound a)
  exact Nat.add_le_add
    (Nat.add_le_add T.embeddingCircuit_gateCount_le hlayers)
    T.readoutCircuit_gateCount_le

theorem compile_gateCount_le_total (T : FixedPrecisionTransformer a) :
    Circuit.gateCount T.compile ≤
      TransformerGateCost.total T.arithmetic (sizeBound a) := by
  rw [T.compile_gateCount_eq_budget]
  exact T.localGateBudget_le_total

end FixedPrecisionTransformer

/-! ## Replacing architectural quantities by the parameter count -/

namespace Architecture

variable (a : Architecture)

private theorem vocabulary_le_firstSummand
    (_hv : 1 ≤ a.vocabulary) (hd : 1 ≤ a.halfWidth) :
    a.vocabulary ≤ 3 * a.vocabulary * a.halfWidth := by
  have h₁ : a.vocabulary ≤ 3 * a.vocabulary := by omega
  exact h₁.trans (Nat.le_mul_of_pos_right (3 * a.vocabulary) hd)

/-- Vocabulary size is bounded by the paper's parameter count. -/
theorem vocabulary_le_parameterCount
    (hv : 1 ≤ a.vocabulary) (hd : 1 ≤ a.halfWidth) :
    a.vocabulary ≤ a.parameterCount := by
  exact (vocabulary_le_firstSummand a hv hd).trans (Nat.le_add_right _ _)

/-- Hidden width is bounded by the embedding/unembedding parameter count. -/
theorem hiddenWidth_le_parameterCount
    (hv : 1 ≤ a.vocabulary) (_hd : 1 ≤ a.halfWidth) :
    a.hiddenWidth ≤ a.parameterCount := by
  have h : 2 * a.halfWidth ≤ 3 * a.vocabulary * a.halfWidth := by
    calc
      2 * a.halfWidth ≤ (3 * a.vocabulary) * a.halfWidth := by
        apply Nat.mul_le_mul_right
        omega
      _ = 3 * a.vocabulary * a.halfWidth := by omega
  exact h.trans (Nat.le_add_right _ _)

/-- Layer count is bounded by the attention/MLP parameter count. -/
theorem layers_le_parameterCount (hd : 1 ≤ a.halfWidth) :
    a.layers ≤ a.parameterCount := by
  have hwidth : 1 ≤ a.hiddenWidth ^ 2 := by
    apply Nat.one_le_pow
    simp only [hiddenWidth]
    omega
  have hfactor : a.layers ≤ 3 * a.layers * a.heads + 2 * a.layers := by
    have hdouble : a.layers ≤ 2 * a.layers := by omega
    exact hdouble.trans (Nat.le_add_left _ _)
  have hproduct : a.layers ≤
      (3 * a.layers * a.heads + 2 * a.layers) * a.hiddenWidth ^ 2 :=
    hfactor.trans (Nat.le_mul_of_pos_right _ hwidth)
  exact hproduct.trans (Nat.le_add_left _ _)

/-- Head count is bounded by the parameter count when there is a layer. -/
theorem heads_le_parameterCount
    (hl : 1 ≤ a.layers) (hd : 1 ≤ a.halfWidth) :
    a.heads ≤ a.parameterCount := by
  have hwidth : 1 ≤ a.hiddenWidth ^ 2 := by
    apply Nat.one_le_pow
    simp only [hiddenWidth]
    omega
  have hhead : a.heads ≤ 3 * a.layers * a.heads := by
    calc
      a.heads ≤ a.layers * a.heads := Nat.le_mul_of_pos_left _ hl
      _ ≤ 3 * (a.layers * a.heads) := Nat.le_mul_of_pos_left _ (by omega)
      _ = 3 * a.layers * a.heads := by simp [mul_assoc]
  have hfactor : a.heads ≤ 3 * a.layers * a.heads + 2 * a.layers :=
    hhead.trans (Nat.le_add_right _ _)
  have hproduct : a.heads ≤
      (3 * a.layers * a.heads + 2 * a.layers) * a.hiddenWidth ^ 2 :=
    hfactor.trans (Nat.le_mul_of_pos_right _ hwidth)
  exact hproduct.trans (Nat.le_add_left _ _)

/-- The local polynomial's base is at most `3(M+N+1)`. -/
theorem localBase_le_three_mul_parameterBase
    (hv : 1 ≤ a.vocabulary) (hd : 1 ≤ a.halfWidth) (hl : 1 ≤ a.layers) :
    a.localBase ≤ 3 * (a.parameterCount + a.contextLength + 1) := by
  have hV := a.vocabulary_le_parameterCount hv hd
  have hD := a.hiddenWidth_le_parameterCount hv hd
  have hH := a.heads_le_parameterCount hl hd
  simp only [localBase]
  omega

/-- The single variable used in the generated gate recurrence is controlled
by the paper's `M+N` base. -/
theorem sizeBound_le_six_mul_parameterBase
    (hv : 1 ≤ a.vocabulary) (hd : 1 ≤ a.halfWidth) (hl : 1 ≤ a.layers) :
    FixedPrecisionTransformer.sizeBound a ≤
      6 * (a.parameterCount + a.contextLength + 1) := by
  have hlocal := a.localBase_le_three_mul_parameterBase hv hd hl
  have hlayers := a.layers_le_parameterCount hd
  simp only [FixedPrecisionTransformer.sizeBound]
  omega

/-- The `L+2` sequential stages cost at most twice the parameter/input base. -/
theorem layers_add_two_le_two_mul_parameterBase
    (hd : 1 ≤ a.halfWidth) :
    a.layers + 2 ≤ 2 * (a.parameterCount + a.contextLength + 1) := by
  have hL := a.layers_le_parameterCount hd
  omega

end Architecture

/-- In the nonempty case, embedding and readout are absorbed into `cL`. -/
theorem FixedPrecisionTransformer.compile_depth_linear {a : Architecture}
    (T : FixedPrecisionTransformer a) (hl : 1 ≤ a.layers) :
    Circuit.depth T.compile ≤
      (3 * TransformerDepthCost.stage T.arithmetic) * a.layers := by
  refine T.compile_depth_le_fixed.trans ?_
  have hstages : a.layers + 2 ≤ 3 * a.layers := by omega
  calc
    (a.layers + 2) * TransformerDepthCost.stage T.arithmetic ≤
        (3 * a.layers) * TransformerDepthCost.stage T.arithmetic :=
      Nat.mul_le_mul_right _ hstages
    _ = (3 * TransformerDepthCost.stage T.arithmetic) * a.layers := by ring

/--
Unconditional polynomial-size translation.  The coefficient and exponent
come from the proved star-free rounded-sum compiler and fixed scalar truth
tables, never from a circuit-realization hypothesis.
-/
theorem polynomial_size_translation {a : Architecture}
    (T : FixedPrecisionTransformer a)
    (hv : 1 ≤ a.vocabulary) (hd : 1 ≤ a.halfWidth) (hl : 1 ≤ a.layers) :
    ∃ coefficient exponent : ℕ,
      Circuit.gateCount T.compile ≤ coefficient *
        (a.parameterCount + a.contextLength + 1) ^ exponent := by
  obtain ⟨coefficient, exponent, hpolynomial⟩ :=
    TransformerGateCost.total_polynomial T.arithmetic
  let base := a.parameterCount + a.contextLength + 1
  have hsize : FixedPrecisionTransformer.sizeBound a + 1 ≤ 7 * base := by
    have h := a.sizeBound_le_six_mul_parameterBase hv hd hl
    dsimp only [base] at h ⊢
    omega
  refine ⟨coefficient * 7 ^ exponent, exponent, ?_⟩
  calc
    Circuit.gateCount T.compile ≤
        TransformerGateCost.total T.arithmetic
          (FixedPrecisionTransformer.sizeBound a) := T.compile_gateCount_le_total
    _ ≤ coefficient * (FixedPrecisionTransformer.sizeBound a + 1) ^ exponent :=
      hpolynomial _
    _ ≤ coefficient * (7 * base) ^ exponent :=
      Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left hsize exponent)
    _ = (coefficient * 7 ^ exponent) * base ^ exponent := by
      rw [mul_pow]
      ring

/--
The appendix lemma in existential form: there is an unbounded-fanin
AND/OR/NOT circuit that computes the Transformer, has depth `cL` (here the
universal constant is explicitly `3 * localDepth`), and has size polynomial
in the parameter count and input length.
-/
theorem fpt_to_ac0 {a : Architecture} (T : FixedPrecisionTransformer a)
    (hv : 1 ≤ a.vocabulary) (hd : 1 ≤ a.halfWidth) (hl : 1 ≤ a.layers) :
    ∃ coefficient exponent : ℕ, ∃ circuit : Circuit a.inputBits 1,
      (∀ input, Circuit.eval circuit input 0 = T.run input) ∧
      Circuit.depth circuit ≤
        (3 * TransformerDepthCost.stage T.arithmetic) * a.layers ∧
      Circuit.gateCount circuit ≤
        coefficient * (a.parameterCount + a.contextLength + 1) ^ exponent := by
  obtain ⟨coefficient, exponent, hsize⟩ :=
    polynomial_size_translation T hv hd hl
  exact ⟨coefficient, exponent, T.compile, T.compile_correct,
    T.compile_depth_linear hl, hsize⟩

end TransformerAC0
