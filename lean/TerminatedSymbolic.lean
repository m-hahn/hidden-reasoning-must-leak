import UniformTaskFootprint
import TerminatedAutoregressive

/-!
# Full-alphabet variable-length footprint and length bounds

The symbolic input is uniform over its whole alphabet. Every even/odd slice
uses the same matrix Transformer and separator classifier. Its terminated
fiber circuits are constructed by `TerminatedAutoregressive`; averaging the
slice caps proves the full-uniform information bound. The expected length is
computed from the actual first-separator execution.
-/

noncomputable section

namespace TerminatedSymbolic

open TransformerAC0 Autoregressive FiniteInformation UniformTaskFootprint

def separatorAt [DecidableEq Alphabet]
    (data : SymbolGenerator n bound Alphabet)
    (separatorLabel : Fin data.architecture.vocabulary → Bool)
    (input : Fin n → Alphabet) (time : ℕ) : Bool :=
  ({ data.transformer with outputLabel := separatorLabel } : FixedPrecisionTransformer data.architecture).run
    (fun wire => (data.context time (fun previous => data.generatedToken input previous) wire).eval input)

structure Generator (n bound : ℕ) (Alphabet : Type*) [DecidableEq Alphabet] where
  data : SymbolGenerator n bound Alphabet
  separatorLabel : Fin data.architecture.vocabulary → Bool
  terminates : ∀ input : Fin n → Alphabet, ∃ time : ℕ,
    time ≤ bound ∧ separatorAt data separatorLabel input time = true

namespace Generator

variable {Alphabet Label : Type*} [DecidableEq Alphabet]
variable {n bound : ℕ}

def length (model : Generator n bound Alphabet) (input : Fin n → Alphabet) : Fin (bound + 1) :=
  ⟨Nat.find (model.terminates input), by
    have h := (Nat.find_spec (model.terminates input)).1
    omega⟩

def transcript (model : Generator n bound Alphabet) (input : Fin n → Alphabet) :
    TerminatedAutoregressive.Transcript bound :=
  ⟨model.length input, fun time => model.data.generatedToken input time⟩

def answer (model : Generator n bound Alphabet) (input : Fin n → Alphabet) : Bool :=
  model.data.generatedToken input ((model.length input).val + 1)

theorem separatorAt_slice (model : Generator n bound Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) (input : Bits n) (time : ℕ) :
    TerminatedAutoregressive.separatorAt (model.data.slice pairing labels) model.separatorLabel input time =
      separatorAt model.data model.separatorLabel
        (fun i => pairing.symm (input i, labels i)) time := by
  unfold TerminatedAutoregressive.separatorAt separatorAt TerminatedAutoregressive.separatorModel
  change ({ model.data.transformer with outputLabel := model.separatorLabel } :
      FixedPrecisionTransformer model.data.architecture).run _ =
    ({ model.data.transformer with outputLabel := model.separatorLabel } :
      FixedPrecisionTransformer model.data.architecture).run _
  congr 1
  funext wire
  change ((model.data.context time
      (fun previous => (model.data.slice pairing labels).generatedToken input previous) wire).restrict pairing labels).eval input = _
  rw [SymbolLiteral.eval_restrict]
  congr 2
  funext previous
  exact model.data.slice_generatedToken pairing labels input previous

def slice (model : Generator n bound Alphabet) (pairing : Alphabet ≃ Bool × Label)
    (labels : Fin n → Label) : TerminatedAutoregressive.Generator n bound where
  data := model.data.slice pairing labels
  separatorLabel := model.separatorLabel
  terminates := by
    intro input
    obtain ⟨time, hbound, hstop⟩ := model.terminates (fun i => pairing.symm (input i, labels i))
    exact ⟨time, hbound, by rw [model.separatorAt_slice pairing labels input time]; exact hstop⟩

theorem slice_length (model : Generator n bound Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) (input : Bits n) :
    (model.slice pairing labels).length input =
      model.length (fun i => pairing.symm (input i, labels i)) := by
  apply Fin.ext
  apply le_antisymm
  · apply Nat.find_min' ((model.slice pairing labels).terminates input)
    have h := Nat.find_spec (model.terminates (fun i => pairing.symm (input i, labels i)))
    exact ⟨h.1, by
      change TerminatedAutoregressive.separatorAt (model.data.slice pairing labels)
        model.separatorLabel input _ = true
      rw [model.separatorAt_slice]
      exact h.2⟩
  · apply Nat.find_min' (model.terminates (fun i => pairing.symm (input i, labels i)))
    have h := Nat.find_spec ((model.slice pairing labels).terminates input)
    refine ⟨h.1, ?_⟩
    have hstop := h.2
    change TerminatedAutoregressive.separatorAt (model.data.slice pairing labels)
        model.separatorLabel input _ = true at hstop
    rw [model.separatorAt_slice] at hstop
    exact hstop

@[simp] theorem slice_transcript (model : Generator n bound Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) (input : Bits n) :
    (model.slice pairing labels).transcript input =
      model.transcript (fun i => pairing.symm (input i, labels i)) := by
  unfold TerminatedAutoregressive.Generator.transcript transcript
  rw [slice_length]
  congr 1
  funext time
  exact model.data.slice_generatedToken pairing labels input time

@[simp] theorem slice_answer (model : Generator n bound Alphabet)
    (pairing : Alphabet ≃ Bool × Label) (labels : Fin n → Label) (input : Bits n) :
    (model.slice pairing labels).answer input =
      model.answer (fun i => pairing.symm (input i, labels i)) := by
  unfold TerminatedAutoregressive.Generator.answer answer
  rw [slice_length]
  exact model.data.slice_generatedToken pairing labels input _

def fiberDepth (model : Generator n bound Alphabet) : ℕ :=
  max (Circuit.depth model.data.transformer.compile)
    (Circuit.depth ({ model.data.transformer with outputLabel := model.separatorLabel } :
      FixedPrecisionTransformer model.data.architecture).compile) + 6

def fiberSize (model : Generator n bound Alphabet) : ℕ :=
  10 * (bound + 1) * (model.data.architecture.inputBits +
    max (Circuit.gateCount model.data.transformer.compile)
      (Circuit.gateCount ({ model.data.transformer with outputLabel := model.separatorLabel } :
        FixedPrecisionTransformer model.data.architecture).compile) + 1) + 20

def expectedLength [Fintype Alphabet] [Nonempty Alphabet]
    (model : Generator n bound Alphabet) : ℝ :=
  (Distribution.uniform (Fin n → Alphabet)).expectation
    (fun input => ((model.length input).val + 1 : ℕ))

theorem uniform_footprint
    [Fintype Alphabet] [Nonempty Alphabet] [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (model : Generator n bound Alphabet)
    (pairing : Alphabet ≃ Bool × Label)
    (correct : ∀ input, model.answer input = Tal.parity (fun i => (pairing (input i)).1))
    (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) ≤
      (Distribution.uniform (Fin n → Alphabet)).mutualInformation id model.transcript := by
  rw [Distribution.mutualInformation_id_eq_entropy]
  have hsize : 1 < model.fiberSize := by unfold fiberSize; omega
  apply paired_uniform_entropy_lower_bound pairing model.transcript _
    (Real.sqrt_pos.mpr (Tal.tailBound_pos _ _ _))
  intro labels candidate
  have hsliced : ∀ input, (model.slice pairing labels).answer input = Tal.parity input := by
    intro input
    rw [slice_answer, correct]
    simp
  let sliced := model.slice pairing labels
  let G := sliced.parityTrace hsliced
  have h := G.transcriptProbability_le_of_correlation
    (sliced.fiberCircuitFamily hsliced)
    (Footprint.indicatorParityCorrelationBound_of_sign hn
      (Footprint.signParityCorrelationBound_of_tal tal hsize)) candidate
  have hrewrite :
      (fun input => model.transcript (fun i => pairing.symm (input i, labels i))) = sliced.transcript := by
    funext input
    exact (model.slice_transcript pairing labels input).symm
  rw [hrewrite, Distribution.uniform_pushMass_eq_card]
  simpa only [G, Footprint.ParityTrace.transcriptProbability, Footprint.ParityTrace.transcriptFiber,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    TerminatedAutoregressive.Generator.parityTrace] using h

theorem uniform_expected_length_lower_bound
    [Fintype Alphabet] [Nonempty Alphabet] [Fintype Label] [Nonempty Label]
    (tal : Tal.FourierTailTheorem) (model : Generator n bound Alphabet)
    (pairing : Alphabet ≃ Bool × Label)
    (correct : ∀ input, model.answer input = Tal.parity (fun i => (pairing (input i)).1))
    (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) / Real.logb 2 3 ≤
      model.expectedLength := by
  have hfootprint := model.uniform_footprint tal pairing correct hn
  rw [Distribution.mutualInformation_id_eq_entropy] at hfootprint
  have hcoding := TerminatedCode.entropy_le_expected_terminated_length
    (Distribution.uniform (Fin n → Alphabet)) model.transcript 2 (by decide)
    TerminatedAutoregressive.Generator.payload TerminatedAutoregressive.Generator.payload_injective
  have hcoding' : (Distribution.uniform (Fin n → Alphabet)).entropy model.transcript ≤
      model.expectedLength * Real.logb 2 3 := by
    simpa [expectedLength, TerminatedAutoregressive.Generator.payload, transcript] using hcoding
  apply (div_le_iff₀ (Real.logb_pos (by norm_num) (by norm_num) : 0 < Real.logb 2 (3 : ℝ))).mpr
  exact hfootprint.trans hcoding'

end Generator

open TaskReductions

theorem s5_uniform_expected_length
    (tal : Tal.FourierTailTheorem) (model : Generator n bound S5)
    (correct : ∀ input, model.answer input = oddUnit (Equiv.Perm.sign (orderedProduct input)))
    (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) / Real.logb 2 3 ≤
      model.expectedLength := by
  apply model.uniform_expected_length_lower_bound tal s5Pairing _ hn
  intro input
  rw [correct, ← s5StateTrackingParity_eq_product_sign]
  rfl

theorem addition100_uniform_expected_length
    (tal : Tal.FourierTailTheorem) (model : Generator n bound (Fin 100))
    (correct : ∀ input, model.answer input = additionLSB (fun i => (input i).val))
    (hn : 1 ≤ n) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) / Real.logb 2 3 ≤
      model.expectedLength := by
  apply model.uniform_expected_length_lower_bound tal additionPairing100 _ hn
  intro input
  rw [correct, additionLSB_eq_parity]
  rfl

end TerminatedSymbolic
