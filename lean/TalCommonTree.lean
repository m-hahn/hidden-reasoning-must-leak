import Complexitylib.Algebraic.LowerBound.AC0.CanonicalDecisionTree

/-!
# Common partial decision trees

This is the actual shared-tree notion needed by multi-switching: every leaf
restriction makes every function in the family computable by a shallow tree.
It is not the weaker union-bound notion of separate trees for each function.
-/

namespace TalCommonTree
open Algebraic AC0

/-- A shared adaptive query tree. Leaves do not themselves output a Boolean. -/
inductive Tree (n : ℕ)
  | leaf
  | query (coordinate : Fin n) (zero one : Tree n)

namespace Tree

def depth {n : ℕ} : Tree n → ℕ
  | .leaf => 0
  | .query _ zero one => max zero.depth one.depth + 1

def LeafBound {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (shallow : ℕ) : Tree n → PartialAssignment n → Prop
  | .leaf, rho => ∀ index, DecisionTree.DepthAtMost
      (ScalarFunction.restrict (family index) rho) shallow
  | .query coordinate zero one, rho =>
      zero.LeafBound family shallow (rho.refine (PartialAssignment.fix coordinate false)) ∧
      one.LeafBound family shallow (rho.refine (PartialAssignment.fix coordinate true))

end Tree

def fullQueryTree {n : ℕ} : List (Fin n) → Tree n
  | [] => .leaf
  | coordinate :: rest => .query coordinate (fullQueryTree rest) (fullQueryTree rest)

theorem depth_fullQueryTree {n : ℕ} (indices : List (Fin n)) :
    (fullQueryTree indices).depth = indices.length := by
  induction indices with
  | nil => rfl
  | cons coordinate rest ih => simp [fullQueryTree, Tree.depth, ih]

/-- Querying all still-unfixed coordinates leaves every function constant. -/
theorem fullQueryTree_leafBound {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (shallow : ℕ) (indices : List (Fin n)) (rho : PartialAssignment n)
    (hfixed : ∀ coordinate, coordinate ∉ indices → rho coordinate ≠ none) :
    (fullQueryTree indices).LeafBound family shallow rho := by
  induction indices generalizing rho with
  | nil =>
      intro index
      have hequal (input : Fin n → Bool) : rho.apply input = rho.apply (fun _ => false) := by
        funext coordinate
        have h := hfixed coordinate (by simp)
        cases hrho : rho coordinate with
        | none => exact False.elim (h hrho)
        | some value => simp [PartialAssignment.apply, hrho]
      refine ⟨.leaf (family index (rho.apply fun _ => false)), ?_, Nat.zero_le _⟩
      intro input
      simp only [DecisionTree.eval_leaf, ScalarFunction.restrict_apply]
      exact (congrArg (family index) (hequal input)).symm
  | cons coordinate rest ih =>
      have htail (value : Bool) : ∀ current, current ∉ rest →
          (rho.refine (PartialAssignment.fix coordinate value)) current ≠ none := by
        intro current habsent
        by_cases heq : current = coordinate
        · subst current
          cases hrho : rho coordinate <;>
            simp [PartialAssignment.refine, PartialAssignment.fix, hrho]
        · have h := hfixed current (by simp [heq, habsent])
          cases hrho : rho current with
          | none => exact False.elim (h hrho)
          | some bit => simp [PartialAssignment.refine, hrho]
      exact ⟨ih _ (htail false), ih _ (htail true)⟩

/-- A common partial tree of query depth at most `bound`, with leaf depth `shallow`. -/
def HasCommonTree {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (rho : PartialAssignment n) (shallow bound : ℕ) : Prop :=
  ∃ tree : Tree n, tree.LeafBound family shallow rho ∧ tree.depth ≤ bound

/-- Common-tree depth is always finite; there is no existence premise. -/
theorem hasCommonTree_inputCount {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (rho : PartialAssignment n) (shallow : ℕ) :
    HasCommonTree family rho shallow n := by
  refine ⟨fullQueryTree (List.finRange n), fullQueryTree_leafBound family shallow
    (List.finRange n) rho (by intro coordinate habsent; simp at habsent), ?_⟩
  simp [depth_fullQueryTree]

theorem hasCommonTree_mono {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (rho : PartialAssignment n) (shallow : ℕ) {small large : ℕ}
    (h : HasCommonTree family rho shallow small) (hbound : small ≤ large) :
    HasCommonTree family rho shallow large := by
  obtain ⟨tree, hleaf, htree⟩ := h
  exact ⟨tree, hleaf, htree.trans hbound⟩

theorem hasCommonTree_zero_iff {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (rho : PartialAssignment n) (shallow : ℕ) :
    HasCommonTree family rho shallow 0 ↔
      ∀ index, DecisionTree.DepthAtMost (ScalarFunction.restrict (family index) rho) shallow := by
  constructor
  · rintro ⟨tree, hleaf, hdepth⟩
    cases tree with
    | leaf => exact hleaf
    | query coordinate zero one => simp [Tree.depth] at hdepth
  · intro h
    exact ⟨.leaf, h, le_rfl⟩

theorem hasCommonTree_query {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (rho : PartialAssignment n) (shallow bound : ℕ) (coordinate : Fin n)
    (hzero : HasCommonTree family (rho.refine (PartialAssignment.fix coordinate false)) shallow bound)
    (hone : HasCommonTree family (rho.refine (PartialAssignment.fix coordinate true)) shallow bound) :
    HasCommonTree family rho shallow (bound + 1) := by
  obtain ⟨zero, hzero, hzdepth⟩ := hzero
  obtain ⟨one, hone, hodepth⟩ := hone
  refine ⟨.query coordinate zero one, ⟨hzero, hone⟩, ?_⟩
  dsimp [Tree.depth]
  omega

/-- Failure of a common depth-`D+1` tree survives on at least one query branch. -/
theorem exists_bad_branch {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (rho : PartialAssignment n) (shallow bound : ℕ) (coordinate : Fin n)
    (hbad : ¬HasCommonTree family rho shallow (bound + 1)) :
    ∃ value : Bool, ¬HasCommonTree family
      (rho.refine (PartialAssignment.fix coordinate value)) shallow bound := by
  classical
  by_contra h
  have hall : ∀ value : Bool, HasCommonTree family
      (rho.refine (PartialAssignment.fix coordinate value)) shallow bound := by
    simpa only [not_exists, not_not] using h
  exact hbad (hasCommonTree_query family rho shallow bound coordinate (hall false) (hall true))

/-- Even for a prescribed list of queries, there is a global answer string
that consumes at most one unit of common-tree hardness per query. This is the
adversarial-answer step used between the phases of a multi-switching witness.
-/
theorem exists_bad_transcript {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (rho : PartialAssignment n) (shallow bound : ℕ) (indices : List (Fin n))
    (hbad : ¬HasCommonTree family rho shallow (bound + indices.length)) :
    ∃ steps : List (DecisionTree.PathStep n),
      DecisionTree.PathStep.indices steps = indices ∧
      ¬HasCommonTree family (rho.refine (DecisionTree.PathStep.assignment steps)) shallow bound := by
  induction indices generalizing rho with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      simpa only [DecisionTree.PathStep.assignment_nil, PartialAssignment.refine_empty,
        List.length_nil, Nat.add_zero] using hbad
  | cons coordinate rest ih =>
      have hbad' : ¬HasCommonTree family rho shallow ((bound + rest.length) + 1) := by
        simpa only [List.length_cons, Nat.add_assoc] using hbad
      obtain ⟨value, hbranch⟩ := exists_bad_branch family rho shallow
        (bound + rest.length) coordinate hbad'
      obtain ⟨steps, hindices, htail⟩ := ih
        (rho.refine (PartialAssignment.fix coordinate value)) hbranch
      refine ⟨⟨coordinate, value⟩ :: steps, ?_, ?_⟩
      · simp only [DecisionTree.PathStep.indices, List.map_cons] at hindices ⊢
        rw [hindices]
      · simpa only [DecisionTree.PathStep.assignment_cons, PartialAssignment.refine_assoc] using htail

/-- At a genuinely bad state, some family member fails the leaf depth bound. -/
theorem exists_deep_member {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (rho : PartialAssignment n) (shallow bound : ℕ)
    (hbad : ¬HasCommonTree family rho shallow bound) :
    ∃ index : Fin m, DecisionTree.DepthAtLeast
      (ScalarFunction.restrict (family index) rho) (shallow + 1) := by
  classical
  have hzero : ¬HasCommonTree family rho shallow 0 := fun h =>
    hbad (hasCommonTree_mono family rho shallow h (Nat.zero_le bound))
  rw [hasCommonTree_zero_iff] at hzero
  obtain ⟨index, hindex⟩ := not_forall.mp hzero
  exact ⟨index, (DecisionTree.depthAtLeast_succ_iff_not_depthAtMost _ shallow).mpr hindex⟩

/-- A bad DNF-family state yields an actual deep canonical path source. -/
theorem exists_deep_canonical_member {n m : ℕ} (family : Fin m → DNF n)
    (rho : PartialAssignment n) (shallow bound : ℕ)
    (hbad : ¬HasCommonTree (fun index => (family index).eval) rho shallow bound) :
    ∃ index : Fin m, (family index).CanonicalDepthAtLeast rho (shallow + 1) := by
  obtain ⟨index, hindex⟩ := exists_deep_member
    (fun index => (family index).eval) rho shallow bound hbad
  have heval : ScalarFunction.restrict (family index).eval rho =
      ((family index).restrict rho).eval := by
    funext input
    exact ((family index).restrict_sound rho input).symm
  rw [heval] at hindex
  exact ⟨index, (family index).canonicalDepthAtLeast_of_depthAtLeast rho _ hindex⟩

end TalCommonTree
