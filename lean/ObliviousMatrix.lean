import ObliviousProgram
import RoutedAutoregressive
import RoutedLocalMap

/-!
# Fixed-address programs executed by shared numerical matrices

There are two causal heads: preceding control and last cell write. The
prompt contains the constant initial control and initial cell contents at
the fixed visited addresses. Opcodes are finite control/symbol update maps,
so their alphabet, token alphabet, precision and head count do not grow with
the address space or execution horizon.
-/

noncomputable section
namespace ObliviousMatrix
open TransformerAC0 ObliviousProgram ObliviousSimulation

variable {Input Address Control Symbol : Type*}
variable [DecidableEq Address] [Fintype Control] [Fintype Symbol] [Inhabited Control] [Inhabited Symbol]

abbrev Token (Control Symbol : Type*) := Control ⊕ (Symbol ⊕ (Control × Symbol))
abbrev Opcode (Control Symbol : Type*) := Control × Symbol → Control × Symbol

noncomputable instance opcodeFintype (Control Symbol : Type*) [Fintype Control] [Fintype Symbol] :
    Fintype (Opcode Control Symbol) := Fintype.ofFinite _

def vocabulary (Control Symbol : Type*) [Fintype Control] [Fintype Symbol] : ℕ := Fintype.card (Token Control Symbol)
def opcodes (Control Symbol : Type*) [Fintype Control] [Fintype Symbol] : ℕ := Fintype.card (Opcode Control Symbol)

def tokenCode : Token Control Symbol ≃ Fin (vocabulary Control Symbol) := Fintype.equivFin _
def opcodeCode : Opcode Control Symbol ≃ Fin (opcodes Control Symbol) := Fintype.equivFin _

theorem vocabulary_positive : 0 < vocabulary Control Symbol := Fintype.card_pos
theorem opcodes_positive : 0 < opcodes Control Symbol := Fintype.card_pos

def controlOf : Token Control Symbol → Control
  | .inl control => control
  | .inr (.inl _) => default
  | .inr (.inr value) => value.1

def symbolOf : Token Control Symbol → Symbol
  | .inl _ => default
  | .inr (.inl symbol) => symbol
  | .inr (.inr value) => value.2

def traceEncoding (token : StepToken Unit Control Symbol) : Fin (vocabulary Control Symbol) :=
  tokenCode (.inr (.inr (token.state, token.write ())))

def update (instruction : Instruction Address Control Symbol) : Opcode Control Symbol := fun value =>
  (instruction.nextControl value.1 value.2, instruction.nextSymbol value.1 value.2)

def transition (opcode : Fin (opcodes Control Symbol))
    (selected : Fin 2 → Fin (vocabulary Control Symbol)) : Fin (vocabulary Control Symbol) :=
  tokenCode (.inr (.inr (opcodeCode.symm opcode
    (controlOf (tokenCode.symm (selected 0)), symbolOf (tokenCode.symm (selected 1))))))

def front (steps : ℕ) : ℕ := steps + 2
def window (steps : ℕ) : ℕ := 2 * steps + 2

def eventTime (steps : ℕ) (position : Fin (window steps)) : ℕ := position.val - (steps + 1)

def queryPosition (steps : ℕ) (time : Fin (steps + 1)) : Fin (window steps) :=
  ⟨steps + 1 + time.val, by have h := time.isLt; unfold window; omega⟩

@[simp] theorem queryPosition_val (steps : ℕ) (time : Fin (steps + 1)) :
    (queryPosition steps time).val = steps + 1 + time.val := rfl

@[simp] theorem eventTime_queryPosition (steps : ℕ) (time : Fin (steps + 1)) :
    eventTime steps (queryPosition steps time) = time.val := by
  change steps + 1 + time.val - (steps + 1) = time.val
  omega

def controlRoute (steps : ℕ) (position : Fin (window steps)) : Fin (window steps) :=
  if eventTime steps position = 0 then ⟨0, by have h := position.isLt; omega⟩ else position

theorem controlRoute_le (steps : ℕ) (position : Fin (window steps)) : controlRoute steps position ≤ position := by
  unfold controlRoute
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

def memoryIndex (program : Program Input Address Control Symbol) (steps time : ℕ) : ℕ :=
    match lastBefore program.position time (program.position time) with
    | none => time + 1
    | some previous => front steps + previous.val

def cellIndex (program : Program Input Address Control Symbol) (steps position : ℕ) : ℕ :=
  if position < steps + 1 then 0 else memoryIndex program steps (position - (steps + 1))

def cellRoute (program : Program Input Address Control Symbol) (steps : ℕ) (position : Fin (window steps)) :
    Fin (window steps) := ⟨cellIndex program steps position.val, by
  have hp := position.isLt
  unfold cellIndex memoryIndex
  split_ifs with hfront
  · omega
  · split
    · unfold window at *; omega
    · rename_i previous heq
      have ht := previous.isLt
      unfold front window at *
      omega⟩

omit [Fintype Control] [Fintype Symbol] [Inhabited Control] [Inhabited Symbol] in
theorem cellRoute_le (program : Program Input Address Control Symbol) (steps : ℕ)
    (position : Fin (window steps)) : cellRoute program steps position ≤ position := by
  change cellIndex program steps position.val ≤ position.val
  unfold cellIndex memoryIndex
  split_ifs with hfront
  · exact Nat.zero_le _
  · split
    · omega
    · rename_i previous heq
      have ht := previous.isLt
      unfold front at *
      omega

def plan (program : Program Input Address Control Symbol) (steps : ℕ) :
    RoutedMatrix.Plan (vocabulary Control Symbol) (window steps) 2 (opcodes Control Symbol) where
  route position head := if head = 0 then controlRoute steps position else cellRoute program steps position
  causal := by
    intro position head
    split_ifs
    · exact controlRoute_le steps position
    · exact cellRoute_le program steps position
  opcode position := opcodeCode (update (program.instruction (eventTime steps position)))

omit [Inhabited Control] [Inhabited Symbol] in
@[simp] theorem route_control (program : Program Input Address Control Symbol) (steps : ℕ)
    (position : Fin (window steps)) : (plan program steps).route position 0 = controlRoute steps position := by
  simp [plan]

omit [Inhabited Control] [Inhabited Symbol] in
@[simp] theorem route_cell (program : Program Input Address Control Symbol) (steps : ℕ)
    (position : Fin (window steps)) : (plan program steps).route position 1 = cellRoute program steps position := by
  simp [plan]

def prompt (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input) :
    Fin (front steps) → Fin (vocabulary Control Symbol) :=
  Fin.cases (tokenCode (.inl program.initialControl))
    (fun time => tokenCode (.inr (.inl (program.initialMemory input (program.position time)))))

def localMap : Bits (RoutedMatrix.featureCount (vocabulary Control Symbol) 2 (opcodes Control Symbol)) →
    Fin (vocabulary Control Symbol) :=
  RoutedMatrix.transitionMap vocabulary_positive opcodes_positive transition

def label (finish : Control → Bool) (token : Fin (vocabulary Control Symbol)) : Bool :=
  finish (controlOf (tokenCode.symm token))

def model (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool) :
    CausalAutoregressive.Model
      (RoutedMatrix.architecture (vocabulary Control Symbol) (window steps) 2 (opcodes Control Symbol))
      (front steps) steps :=
  RoutedMatrix.causalModel (plan program steps) localMap (label finish) vocabulary_positive
    (by unfold front; omega) (by unfold front window; omega)

def context (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input)
    (time : Fin (steps + 1)) : Fin (window steps) → Fin (vocabulary Control Symbol) :=
  RoutedMatrix.contextWord vocabulary_positive (prompt program steps input) time.val
    (fun previous => traceEncoding (program.traceToken input previous.val))

theorem context_prompt (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input)
    (time : Fin (steps + 1)) (position : Fin (window steps)) (hposition : position.val < front steps) :
    context program steps input time position = prompt program steps input ⟨position.val, hposition⟩ := by
  simp only [context, RoutedMatrix.contextWord, dif_pos hposition]

theorem context_previous (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input)
    (time : Fin (steps + 1)) (position : Fin (window steps))
    (hposition : front steps ≤ position.val) (hprevious : position.val - front steps < time.val) :
    context program steps input time position = traceEncoding (program.traceToken input (position.val - front steps)) := by
  simp only [context, RoutedMatrix.contextWord, dif_neg (by omega : ¬position.val < front steps), dif_pos hprevious]

theorem control_read (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input)
    (time : Fin (steps + 1)) :
    controlOf (tokenCode.symm (context program steps input time (controlRoute steps (queryPosition steps time)))) =
      (program.configurationAt input time.val).control := by
  by_cases htime : time.val = 0
  · have hr : controlRoute steps (queryPosition steps time) = ⟨0, by unfold window; omega⟩ := by
      simp [controlRoute, htime]
    rw [hr, context_prompt program steps input time _ (by change 0 < steps + 2; omega)]
    simp [prompt, controlOf, htime, Program.configurationAt]
  · have hr : controlRoute steps (queryPosition steps time) = queryPosition steps time := by
      simp [controlRoute, htime]
    rw [hr, context_previous program steps input time _
      (by simp only [queryPosition_val, front]; omega) (by simp only [queryPosition_val, front]; omega)]
    simp only [traceEncoding, Equiv.symm_apply_apply, controlOf, Program.traceToken_control]
    congr 2
    simp only [queryPosition_val, front]
    omega

theorem cell_read (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input)
    (time : Fin (steps + 1)) :
    symbolOf (tokenCode.symm (context program steps input time (cellRoute program steps (queryPosition steps time)))) =
      (program.configurationAt input time.val).memory (program.position time.val) := by
  rw [program.scanned_eq_last_write]
  have hr : (cellRoute program steps (queryPosition steps time)).val =
      match lastBefore program.position time.val (program.position time.val) with
      | none => time.val + 1
      | some previous => front steps + previous.val := by
    change cellIndex program steps (steps + 1 + time.val) = _
    unfold cellIndex
    rw [if_neg (by omega : ¬steps + 1 + time.val < steps + 1), Nat.add_sub_cancel_left]
    unfold memoryIndex
    cases lastBefore program.position time.val (program.position time.val) <;> rfl
  cases hprior : lastBefore program.position time.val (program.position time.val) with
  | none =>
      have hrval : (cellRoute program steps (queryPosition steps time)).val = time.val + 1 := by simpa [hprior] using hr
      rw [context_prompt program steps input time _ (by rw [hrval]; have ht := time.isLt; unfold front; omega)]
      have hpos : (⟨(cellRoute program steps (queryPosition steps time)).val,
          by rw [hrval]; have ht := time.isLt; unfold front; omega⟩ : Fin (front steps)) = time.succ := by
        apply Fin.ext
        exact hrval
      rw [hpos]
      simp [prompt, symbolOf]
  | some previous =>
      have hrval : (cellRoute program steps (queryPosition steps time)).val = front steps + previous.val := by
        simpa [hprior] using hr
      rw [context_previous program steps input time _ (by rw [hrval]; omega)
        (by rw [hrval, Nat.add_sub_cancel_left]; exact previous.isLt)]
      simp only [hrval, Nat.add_sub_cancel_left, traceEncoding, Equiv.symm_apply_apply, symbolOf]

/-- A complete numerical routing/MLP step emits the actual instruction
event, with no supplied step-correctness field on the Transformer. -/
theorem step_correct (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input)
    (time : Fin (steps + 1)) :
    localMap (RoutedMatrix.features (plan program steps) (context program steps input time)
      (queryPosition steps time)) = traceEncoding (program.traceToken input time.val) := by
  unfold localMap
  rw [RoutedMatrix.transitionMap_features]
  have hop : (plan program steps).opcode (queryPosition steps time) =
      opcodeCode (update (program.instruction time.val)) := by simp [plan]
  rw [hop]
  unfold transition
  simp only [Equiv.symm_apply_apply, route_control, route_cell]
  rw [control_read, cell_read]
  rfl

theorem routed_correct (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input)
    (time : Fin (steps + 1)) :
    RoutedMatrix.routedToken (plan program steps) localMap vocabulary_positive
      (by unfold front; omega) (by unfold front window; omega) (prompt program steps input) time =
        traceEncoding (program.traceToken input time.val) := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h n ih =>
      rw [RoutedMatrix.routedToken]
      have hprevious : (fun previous : Fin time.val =>
          RoutedMatrix.routedToken (plan program steps) localMap vocabulary_positive
            (by unfold front; omega) (by unfold front window; omega) (prompt program steps input)
            ⟨previous.val, previous.isLt.trans time.isLt⟩) =
          (fun previous : Fin time.val => traceEncoding (program.traceToken input previous.val)) := by
        funext previous
        exact ih previous.val (by omega) _ rfl
      rw [hprevious]
      have hposition : (⟨front steps + time.val - 1, by
          have h := time.isLt; unfold front window; omega⟩ : Fin (window steps)) = queryPosition steps time := by
        apply Fin.ext
        simp only [queryPosition_val, front]
        omega
      rw [hposition]
      simpa only [context, ht] using step_correct program steps input time

/-- The original greedy growing-prefix driver executes the fixed-address
program, token for token, using one shared set of numerical matrices. -/
theorem generated_correct (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool)
    (input : Input) (time : Fin (steps + 1)) :
    (model program steps finish).generatedToken (RoutedMatrix.promptInput (prompt program steps input)) time =
      traceEncoding (program.traceToken input time.val) := by
  unfold model
  rw [RoutedMatrix.autoregressive_correct]
  exact routed_correct program steps input time

theorem output_correct (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool)
    (input : Input) :
    (model program steps finish).answer (RoutedMatrix.promptInput (prompt program steps input)) =
      finish (program.configurationAt input (steps + 1)).control := by
  unfold CausalAutoregressive.Model.answer
  rw [generated_correct]
  change label finish (traceEncoding (program.traceToken input steps)) = _
  simp only [label, traceEncoding, Equiv.symm_apply_apply, controlOf, Program.traceToken_control]

omit [DecidableEq Address] [Inhabited Control] [Inhabited Symbol] in
theorem prompt_control (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input) :
    prompt program steps input ⟨0, by unfold front; omega⟩ = tokenCode (.inl program.initialControl) := rfl

omit [DecidableEq Address] [Inhabited Control] [Inhabited Symbol] in
/-- Prompt cells copy only initial contents at fixed visited addresses.
Neither a future control state nor an attended/updated value is initialized. -/
theorem prompt_cell (program : Program Input Address Control Symbol) (steps : ℕ) (input : Input)
    (time : Fin (steps + 1)) : prompt program steps input time.succ =
      tokenCode (.inr (.inl (program.initialMemory input (program.position time.val)))) := by
  simp only [prompt, Fin.cases_succ]

omit [Inhabited Control] [Inhabited Symbol] in
theorem vocabulary_card : vocabulary Control Symbol =
    Fintype.card Control + Fintype.card Symbol + Fintype.card Control * Fintype.card Symbol := by
  simp [vocabulary, Token, Nat.add_assoc]

theorem fixed_precision (program : Program Input Address Control Symbol) (steps : ℕ) (finish : Control → Bool) :
    (model program steps finish).parameters.scalarBits =
      RoutedMatrix.precision (vocabulary Control Symbol) 2 (opcodes Control Symbol) := rfl

omit [Inhabited Control] [Inhabited Symbol] in
theorem one_layer (steps : ℕ) :
    (RoutedMatrix.architecture (vocabulary Control Symbol) (window steps) 2 (opcodes Control Symbol)).layers = 1 := rfl

omit [Inhabited Control] [Inhabited Symbol] in
theorem two_heads (steps : ℕ) :
    (RoutedMatrix.architecture (vocabulary Control Symbol) (window steps) 2 (opcodes Control Symbol)).heads = 2 := rfl

omit [Inhabited Control] [Inhabited Symbol] in
theorem hidden_dimension_bound (steps : ℕ) :
    (RoutedMatrix.architecture (vocabulary Control Symbol) (window steps) 2 (opcodes Control Symbol)).hiddenWidth ≤
      2 * RoutedMatrix.dimensionConstant (vocabulary Control Symbol) 2 (opcodes Control Symbol) * (window steps + 1) :=
  RoutedMatrix.hidden_dimension_linear

omit [Inhabited Control] [Inhabited Symbol] in
theorem parameter_count_bound (steps : ℕ) :
    (RoutedMatrix.architecture (vocabulary Control Symbol) (window steps) 2 (opcodes Control Symbol)).parameterCount ≤
      (3 * vocabulary Control Symbol * RoutedMatrix.dimensionConstant (vocabulary Control Symbol) 2 (opcodes Control Symbol) +
        4 * (3 * 2 + 2) * RoutedMatrix.dimensionConstant (vocabulary Control Symbol) 2 (opcodes Control Symbol) ^ 2) *
          (window steps + 1) ^ 2 := RoutedMatrix.parameter_count_quadratic

end ObliviousMatrix
