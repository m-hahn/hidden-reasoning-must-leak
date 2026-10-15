import TalGateNetwork

/-!
# Exact shared-gate graph realization of the signed circuit language

Every original AND/OR gate has one name. Serial composition substitutes free
signed references; it does not copy the first circuit's gates into its consumers.
The strict height ordering makes the semantic gate equations acyclic.
-/

noncomputable section
namespace TalSharedCircuit
open TransformerAC0 Algebraic AC0 TalGateNetwork TalSignedCircuit

structure Graph (n : ℕ) (G : Type) where
  functions : G → ScalarFunction Bool n
  height : G → ℕ
  positive : ∀ index, 0 < height index
  gates : G → GateDescription n G
  lower : ∀ index argument, ((gates index).inputs argument).Below height (height index)
  correct : ∀ index, (gates index).eval functions = functions index

structure Realization (n m : ℕ) (G : Type) where
  graph : Graph n G
  outputs : Fin m → Reference n G
  bound : ℕ
  heights_bound : ∀ index, graph.height index ≤ bound
  outputs_below : ∀ index, (outputs index).Below graph.height (bound + 1)

namespace Graph

def toModel {n : ℕ} {G : Type} (graph : Graph n G) : Model n G 1 := by
  refine ⟨graph.functions, fun index => graph.height index - 1, ?_, ?_⟩
  · intro index hrank
    change graph.height index - 1 = 0 at hrank
    have hheight : graph.height index = 1 := by have h := graph.positive index; omega
    have hinputs : ∀ argument, DecisionTree.DepthAtMost
        (((graph.gates index).inputs argument).eval graph.functions) 1 := by
      intro argument
      apply reference_depthAtMost graph.functions graph.height _ 1 le_rfl
      · simpa only [hheight] using graph.lower index argument
      · intro source hzero
        have h := graph.positive source
        omega
    obtain ⟨formula, hwidth, hformula⟩ := normalForm_of_shallow_inputs (graph.gates index).conjunction
      (fun argument => ((graph.gates index).inputs argument).eval graph.functions) 1 hinputs
    exact ⟨formula, hwidth, fun input => (hformula input).trans (congrFun (graph.correct index) input)⟩
  · intro index hrank
    change graph.height index - 1 ≠ 0 at hrank
    refine ⟨graph.gates index, ?_, graph.correct index⟩
    intro argument
    exact reference_below_pred graph.height _ _ (by omega) (graph.lower index argument)

end Graph

def inputReferences {n : ℕ} {G : Type} : Fin n → Reference n G := fun index => .literal ⟨index, true⟩

theorem inputReferences_eval {n : ℕ} {G : Type} (functions : G → ScalarFunction Bool n)
    (input : Bits n) (index : Fin n) : (inputReferences index).eval functions input = input index := by
  cases h : input index <;> simp [inputReferences, Reference.eval, Literal.eval, h]

namespace Realization

def combine {n k m l : ℕ} {G H : Type} (first : Realization n l G) (second : Realization k m H)
    (inputs : Fin k → Reference n G) (offset : ℕ)
    (hinputs : ∀ index, (inputs index).Below first.graph.height (offset + 1)) :
    Realization n m (G ⊕ H) := by
  let functions : G ⊕ H → ScalarFunction Bool n := Sum.elim first.graph.functions
    (fun index input => second.graph.functions index (fun argument => (inputs argument).eval first.graph.functions input))
  let height : G ⊕ H → ℕ := Sum.elim first.graph.height (fun index => second.graph.height index + offset)
  let mappedInputs : Fin k → Reference n (G ⊕ H) := fun index => (inputs index).map Sum.inl
  let gates : G ⊕ H → GateDescription n (G ⊕ H) := Sum.elim
    (fun index => (first.graph.gates index).substitute inputReferences Sum.inl)
    (fun index => (second.graph.gates index).substitute mappedInputs Sum.inr)
  have hfirstInput (input : Bits n) (index : Fin n) :
      (inputReferences (G := G ⊕ H) index).eval functions input = input index := inputReferences_eval _ _ _
  have hmapInput (input : Bits n) (index : Fin k) :
      (mappedInputs index).eval functions input = (inputs index).eval first.graph.functions input :=
    Reference.eval_map _ _ _ _
  have hinputBelow (bound : ℕ) (hbound : offset < bound) (index : Fin k) :
      (mappedInputs index).Below height bound := by
    change ((inputs index).map (H := G ⊕ H) Sum.inl).Below height bound
    cases href : inputs index with
    | constant value => trivial
    | literal atom => trivial
    | gate source positive =>
        have h := hinputs index
        rw [href] at h
        change first.graph.height source < offset + 1 at h
        change first.graph.height source < bound
        omega
  refine ⟨⟨functions, height, ?_, gates, ?_, ?_⟩,
    fun index => (second.outputs index).substitute mappedInputs Sum.inr,
    max first.bound (offset + second.bound), ?_, ?_⟩
  · intro index
    cases index with
    | inl index => exact first.graph.positive index
    | inr index => have h := second.graph.positive index; change 0 < second.graph.height index + offset; omega
  · intro index argument
    cases index with
    | inl index =>
        apply Reference.below_substitute inputReferences Sum.inl first.graph.height height
          (first.graph.height index) (first.graph.height index)
        · intro source; trivial
        · intro source h; exact h
        · exact first.graph.lower index argument
    | inr index =>
        apply Reference.below_substitute mappedInputs Sum.inr second.graph.height height
          (second.graph.height index) (second.graph.height index + offset)
        · intro source
          apply hinputBelow
          have h := second.graph.positive index
          omega
        · intro source h
          exact Nat.add_lt_add_right h offset
        · exact second.graph.lower index argument
  · intro index
    funext input
    cases index with
    | inl index =>
        exact (GateDescription.eval_substitute _ inputReferences Sum.inl first.graph.functions functions input input
          (hfirstInput input) (fun _ => rfl)).trans (congrFun (first.graph.correct index) input)
    | inr index =>
        exact (GateDescription.eval_substitute _ mappedInputs Sum.inr second.graph.functions functions
          (fun argument => (inputs argument).eval first.graph.functions input) input
          (hmapInput input) (fun _ => rfl)).trans (congrFun (second.graph.correct index) _)
  · intro index
    cases index with
    | inl index => exact (first.heights_bound index).trans (Nat.le_max_left _ _)
    | inr index =>
        exact (Nat.add_le_add_right (second.heights_bound index) offset).trans
          (by simpa only [Nat.add_comm] using Nat.le_max_right first.bound (offset + second.bound))
  · intro index
    apply Reference.below_substitute mappedInputs Sum.inr second.graph.height height
      (second.bound + 1) (max first.bound (offset + second.bound) + 1)
    · intro source
      apply hinputBelow
      have h := Nat.le_max_right first.bound (offset + second.bound)
      omega
    · intro source h
      change second.graph.height source + offset < max first.bound (offset + second.bound) + 1
      have hmax := Nat.le_max_right first.bound (offset + second.bound)
      omega
    · exact second.outputs_below index

theorem combine_outputs {n k m l : ℕ} {G H : Type} (first : Realization n l G)
    (second : Realization k m H) (inputs : Fin k → Reference n G) (offset : ℕ)
    (hinputs : ∀ index, (inputs index).Below first.graph.height (offset + 1)) (input : Bits n) (index : Fin m) :
    ((first.combine second inputs offset hinputs).outputs index).eval
        (first.combine second inputs offset hinputs).graph.functions input =
      (second.outputs index).eval second.graph.functions
        (fun argument => (inputs argument).eval first.graph.functions input) := by
  dsimp only [combine]
  apply Reference.eval_substitute
  · intro argument
    exact Reference.eval_map _ _ _ _
  · intro gate
    rfl

def parallel {n m k : ℕ} {G H : Type} (left : Realization n m G) (right : Realization n k H) :
    Realization n (m + k) (G ⊕ H) := by
  let combined := left.combine right inputReferences 0 (fun _ => trivial)
  refine ⟨combined.graph, Fin.append (fun index => (left.outputs index).map Sum.inl) combined.outputs,
    combined.bound, combined.heights_bound, ?_⟩
  intro index
  refine Fin.addCases ?_ ?_ index
  · intro index
    rw [Fin.append_left]
    cases href : left.outputs index with
    | constant value => trivial
    | literal atom => trivial
    | gate source positive =>
        change left.graph.height source < max left.bound (0 + right.bound) + 1
        have h := left.heights_bound source
        have hmax := Nat.le_max_left left.bound (0 + right.bound)
        omega
  · intro index
    rw [Fin.append_right]
    exact combined.outputs_below index

def bundle {n m : ℕ} {G : Fin m → Type} (branches : ∀ index, Realization n 1 (G index)) :
    Realization n m (Σ index, G index) := by
  let functions := fun index : Σ index, G index => (branches index.1).graph.functions index.2
  let height := fun index : Σ index, G index => (branches index.1).graph.height index.2
  let gates : (Σ index, G index) → GateDescription n (Σ index, G index) := fun index =>
    ((branches index.1).graph.gates index.2).substitute inputReferences (fun gate => ⟨index.1, gate⟩)
  refine ⟨⟨functions, height, ?_, gates, ?_, ?_⟩,
    fun index => ((branches index).outputs 0).map (fun gate => ⟨index, gate⟩),
    Finset.univ.sup (fun index => (branches index).bound), ?_, ?_⟩
  · intro index
    exact (branches index.1).graph.positive index.2
  · intro index argument
    apply Reference.below_substitute inputReferences (fun gate => ⟨index.1, gate⟩)
      (branches index.1).graph.height height
      ((branches index.1).graph.height index.2) ((branches index.1).graph.height index.2)
    · intro source; trivial
    · intro source h; exact h
    · exact (branches index.1).graph.lower index.2 argument
  · intro index
    funext input
    exact (GateDescription.eval_substitute _ inputReferences (fun gate => ⟨index.1, gate⟩)
      (branches index.1).graph.functions functions input input (inputReferences_eval _ input)
      (fun _ => rfl)).trans (congrFun ((branches index.1).graph.correct index.2) input)
  · intro index
    exact ((branches index.1).heights_bound index.2).trans
      (Finset.le_sup (f := fun index => (branches index).bound) (Finset.mem_univ index.1))
  · intro index
    change (((branches index).outputs 0).map (H := Σ index, G index) (fun gate => ⟨index, gate⟩)).Below
      height ((Finset.univ.sup fun index => (branches index).bound) + 1)
    cases href : (branches index).outputs 0 with
    | constant value => trivial
    | literal atom => trivial
    | gate source positive =>
        change (branches index).graph.height source < (Finset.univ.sup fun index => (branches index).bound) + 1
        have h := ((branches index).heights_bound source).trans
          (Finset.le_sup (f := fun index => (branches index).bound) (Finset.mem_univ index))
        omega

end Realization

def GateType : {n m : ℕ} → TalSignedCircuit.Circuit n m → Type
  | _, _, .wire _ => Empty
  | _, _, .andGate _ => Unit
  | _, _, .orGate _ => Unit
  | _, _, .seq first second => GateType first ⊕ GateType second
  | _, _, .parallel left right => GateType left ⊕ GateType right
  | _, _, .bundle branch => Σ index, GateType (branch index)

instance gateTypeFintype : {n m : ℕ} → (circuit : TalSignedCircuit.Circuit n m) → Fintype (GateType circuit)
  | _, _, .wire _ => by change Fintype Empty; infer_instance
  | _, _, .andGate _ => by change Fintype Unit; infer_instance
  | _, _, .orGate _ => by change Fintype Unit; infer_instance
  | _, _, .seq first second => by
      letI := gateTypeFintype first
      letI := gateTypeFintype second
      change Fintype (GateType first ⊕ GateType second)
      infer_instance
  | _, _, .parallel left right => by
      letI := gateTypeFintype left
      letI := gateTypeFintype right
      change Fintype (GateType left ⊕ GateType right)
      infer_instance
  | _, _, .bundle branch => by
      letI := fun index => gateTypeFintype (branch index)
      change Fintype (Σ index, GateType (branch index))
      infer_instance

theorem card_gateType {n m : ℕ} (circuit : TalSignedCircuit.Circuit n m) :
    Nat.card (GateType circuit) = circuit.gateCount := by
  induction circuit with
  | wire routing => simp [GateType, TalSignedCircuit.Circuit.gateCount]
  | andGate arity => simp [GateType, TalSignedCircuit.Circuit.gateCount]
  | orGate arity => simp [GateType, TalSignedCircuit.Circuit.gateCount]
  | seq first second ihfirst ihsecond =>
      simp only [GateType, TalSignedCircuit.Circuit.gateCount, Nat.card_sum, ihfirst, ihsecond]
  | parallel left right ihleft ihright =>
      simp only [GateType, TalSignedCircuit.Circuit.gateCount, Nat.card_sum, ihleft, ihright]
  | bundle branch ih => simp only [GateType, TalSignedCircuit.Circuit.gateCount, Nat.card_sigma, ih]

def primitive (n : ℕ) (conjunction : Bool) : Realization n 1 Unit := by
  let functions := fun _ : Unit => fun input : Bits n => gateEval conjunction input
  let gates : Unit → GateDescription n Unit := fun _ => ⟨conjunction, n, inputReferences⟩
  refine ⟨⟨functions, fun _ => 1, fun _ => by norm_num, gates, fun _ _ => trivial, ?_⟩,
    fun _ => .gate () true, 1, fun _ => le_rfl, fun _ => by norm_num [Reference.Below]⟩
  intro index
  funext input
  unfold GateDescription.eval
  simp only [gates, inputReferences_eval, functions]

def realize : {n m : ℕ} → (circuit : TalSignedCircuit.Circuit n m) → Realization n m (GateType circuit)
  | _, _, .wire routing =>
      ⟨⟨Empty.elim, Empty.elim, fun index => Empty.elim index,
        Empty.elim, fun index => Empty.elim index, fun index => Empty.elim index⟩,
        fun index => .literal (routing index), 0, fun index => Empty.elim index, fun _ => trivial⟩
  | _, _, .andGate arity => primitive arity true
  | _, _, .orGate arity => primitive arity false
  | _, _, .seq first second =>
      (realize first).combine (realize second) (realize first).outputs (realize first).bound (realize first).outputs_below
  | _, _, .parallel left right => (realize left).parallel (realize right)
  | _, _, .bundle branch => Realization.bundle fun index => realize (branch index)

theorem realize_bound {n m : ℕ} (circuit : TalSignedCircuit.Circuit n m) :
    (realize circuit).bound = circuit.depth := by
  induction circuit with
  | wire routing => rfl
  | andGate arity => rfl
  | orGate arity => rfl
  | seq first second ihfirst ihsecond =>
      change max (realize first).bound ((realize first).bound + (realize second).bound) = first.depth + second.depth
      rw [ihfirst, ihsecond, Nat.max_eq_right (Nat.le_add_right _ _)]
  | parallel left right ihleft ihright =>
      change max (realize left).bound (0 + (realize right).bound) = max left.depth right.depth
      rw [ihleft, ihright, Nat.zero_add]
  | bundle branch ih =>
      change (Finset.univ.sup fun index => (realize (branch index)).bound) = _
      simp only [ih, TalSignedCircuit.Circuit.depth]

theorem realize_eval {n m : ℕ} (circuit : TalSignedCircuit.Circuit n m) (input : Bits n) (index : Fin m) :
    ((realize circuit).outputs index).eval (realize circuit).graph.functions input = circuit.eval input index := by
  induction circuit with
  | wire routing => rfl
  | andGate arity => rfl
  | orGate arity => rfl
  | seq first second ihfirst ihsecond =>
      rw [realize, Realization.combine_outputs]
      simp only [ihfirst]
      exact ihsecond _ index
  | parallel left right ihleft ihright =>
      refine Fin.addCases ?_ ?_ index
      · intro output
        simp only [realize, Realization.parallel, Fin.append_left, TalSignedCircuit.Circuit.eval]
        rw [Reference.eval_map]
        exact ihleft input output
      · intro output
        simp only [realize, Realization.parallel, Fin.append_right, TalSignedCircuit.Circuit.eval]
        rw [Realization.combine_outputs]
        have hinput : (fun index => (inputReferences index).eval (realize left).graph.functions input) = input :=
          funext (inputReferences_eval _ _)
        rw [hinput]
        exact ihright input output
  | bundle branch ih =>
      change (((realize (branch index)).outputs 0).map (H := Σ index, GateType (branch index))
        (fun gate => ⟨index, gate⟩)).eval _ input = _
      rw [Reference.eval_map]
      exact ih index input 0

/-- A bounded original circuit has a ranked model using precisely its supplied gate budget. -/
theorem exists_model {n : ℕ} (circuit : TransformerAC0.Circuit n 1) (depth size : ℕ)
    (hdepth : circuit.depth ≤ depth) (hsize : circuit.gateCount ≤ size) :
    ∃ model : Model n (Fin size) 1, ∃ output : Reference n (Fin size),
      (∀ index, model.rank index ≤ depth - 1) ∧
        ∀ input, output.eval model.functions input = circuit.eval input 0 := by
  classical
  let signed := TalSignedCircuit.compile circuit
  let representation := realize signed
  let graphModel := representation.graph.toModel
  let equivalence := Fintype.equivFin (GateType signed)
  let indexedModel := graphModel.reindex equivalence
  have hcard : Fintype.card (GateType signed) ≤ size := by
    rw [← Nat.card_eq_fintype_card, card_gateType]
    exact (TalSignedCircuit.compile_gateCount_le circuit).trans hsize
  let model := indexedModel.pad hcard
  let output := ((representation.outputs 0).map equivalence).map (Fin.castLE hcard)
  refine ⟨model, output, ?_, ?_⟩
  · apply Model.pad_rank_bound
    intro index
    have hbound : representation.bound ≤ circuit.depth := by
      rw [realize_bound]
      exact TalSignedCircuit.compile_depth_le circuit
    have h := (representation.heights_bound (equivalence.symm index)).trans
      (hbound.trans hdepth)
    exact Nat.sub_le_sub_right h 1
  · intro input
    change (((representation.outputs 0).map equivalence).map (Fin.castLE hcard)).eval model.functions input = _
    rw [Reference.eval_map]
    have hpad : model.functions ∘ Fin.castLE hcard = indexedModel.functions :=
      funext (Model.paddedFunctions_castLE indexedModel hcard)
    rw [hpad, Reference.eval_map]
    have hreindex : indexedModel.functions ∘ equivalence = representation.graph.functions := by
      funext index
      simp only [indexedModel, graphModel, Model.reindex, Graph.toModel, Function.comp_apply, Equiv.symm_apply_apply]
    rw [hreindex, realize_eval]
    exact congrFun (TalSignedCircuit.compile_eval circuit input) 0

end TalSharedCircuit
