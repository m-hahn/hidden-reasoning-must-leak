import RoutedMatrixCorrectness

/-!
# Compiling finite local transitions into the routing MLP

A transition consumes an opcode and one selected token per head. The MLP
truth table is constructed from that transition and the literal one-hot
feature encoding; no decoding or local-map realization certificate is used.
-/

noncomputable section
namespace RoutedMatrix
open TransformerAC0

variable {vocabulary window heads opcodes : ℕ}

def indicator (token : Fin count) : Bits count := fun candidate => decide (candidate = token)

theorem indicator_injective (count : ℕ) : Function.Injective (indicator (count := count)) := by
  intro first second heq
  have h := congrFun heq first
  simpa [indicator] using h.symm

def decodeIndicator (positive : 0 < count) (bits : Bits count) : Fin count :=
  letI : Nonempty (Fin count) := ⟨⟨0, positive⟩⟩
  Function.invFun indicator bits

theorem decodeIndicator_indicator (positive : 0 < count) (token : Fin count) :
    decodeIndicator positive (indicator token) = token := by
  letI : Nonempty (Fin count) := ⟨⟨0, positive⟩⟩
  exact Function.leftInverse_invFun (indicator_injective count) token

def selectedToken (hv : 0 < vocabulary) (input : Bits (featureCount vocabulary heads opcodes))
    (head : Fin heads) : Fin vocabulary :=
  decodeIndicator hv (fun token => input (headFeature head token))

def selectedOpcode (ho : 0 < opcodes) (input : Bits (featureCount vocabulary heads opcodes)) : Fin opcodes :=
  decodeIndicator ho (fun opcode => input (opcodeFeature opcode))

theorem selectedToken_features (plan : Plan vocabulary window heads opcodes)
    (word : Fin window → Fin vocabulary) (position : Fin window) (hv : 0 < vocabulary) (head : Fin heads) :
    selectedToken hv (features plan word position) head = word (plan.route position head) := by
  have hbits : (fun token => features plan word position (headFeature head token)) =
      indicator (word (plan.route position head)) := by
    funext token
    simp only [features, headFeature, Fin.addCases_left, Equiv.symm_apply_apply, indicator]
    simp only [eq_comm]
  unfold selectedToken
  rw [hbits]
  exact decodeIndicator_indicator hv _

theorem selectedOpcode_features (plan : Plan vocabulary window heads opcodes)
    (word : Fin window → Fin vocabulary) (position : Fin window) (ho : 0 < opcodes) :
    selectedOpcode ho (features plan word position) = plan.opcode position := by
  have hbits : (fun opcode => features plan word position (opcodeFeature opcode)) =
      indicator (plan.opcode position) := by
    funext opcode
    simp only [features, opcodeFeature, Fin.addCases_right, indicator, eq_comm]
  unfold selectedOpcode
  rw [hbits]
  exact decodeIndicator_indicator ho _

def transitionMap (hv : 0 < vocabulary) (ho : 0 < opcodes)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (input : Bits (featureCount vocabulary heads opcodes)) : Fin vocabulary :=
  transition (selectedOpcode ho input) (selectedToken hv input)

theorem transitionMap_features (plan : Plan vocabulary window heads opcodes)
    (word : Fin window → Fin vocabulary) (position : Fin window) (hv : 0 < vocabulary) (ho : 0 < opcodes)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) :
    transitionMap hv ho transition (features plan word position) =
      transition (plan.opcode position) (fun head => word (plan.route position head)) := by
  unfold transitionMap
  rw [selectedOpcode_features]
  have ht : selectedToken hv (features plan word position) = fun head => word (plan.route position head) := by
    funext head
    exact selectedToken_features plan word position hv head
  rw [ht]

/-- Any finite opcode-controlled local transition is executed by actual
one-layer numerical matrices on every growing prefix of one parameter set. -/
theorem transition_prefix_correct (plan : Plan vocabulary window heads opcodes)
    (hv : 0 < vocabulary) (ho : 0 < opcodes)
    (transition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (word : Fin window → Fin vocabulary) (length : ℕ) (bounded : length ≤ window) (hlength : 0 < length) :
    (CausalMatrix.restrictContext (transformer plan (transitionMap hv ho transition) label) length bounded).runToken hv hlength
      (CausalMatrix.restrictInput (transformer plan (transitionMap hv ho transition) label) length bounded (oneHot word)) =
      transition (plan.opcode (Fin.castLE bounded ⟨length - 1, by omega⟩))
        (fun head => word (plan.route (Fin.castLE bounded ⟨length - 1, by omega⟩) head)) := by
  rw [run_token_prefix_correct, transitionMap_features]

end RoutedMatrix
