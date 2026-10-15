import ObliviousSimulation

/-!
# Size accounting for the finite-configuration shortcut

The one-cell compiler in `ObliviousSimulation` stores an entire source tape
configuration in one finite-control value.  Its event count alone does not
bound the binary trace length or the Transformer vocabulary size.  These
theorems make that issue explicit: a tape with `cells` Boolean cells already
requires at least `cells` bits per event and at least `2^cells` distinct
control tokens.  The shortcut is useful for semantic preservation but does
not prove the efficient oblivious-machine construction used by the paper.
-/

noncomputable section

namespace SimulationSizeAudit

open TransformerAC0 ObliviousSimulation

/-- Any lossless binary representation needs enough strings for all tokens. -/
theorem BinaryCode.card_le_pow
    {Token : Type*} [Fintype Token] (code : BinaryCode Token width) :
    Fintype.card Token ≤ 2 ^ width := by
  have hinjective : Function.Injective code.encode := by
    intro first second heq
    have h := congrArg code.decode heq
    simpa [code.decode_encode] using h
  have h := Fintype.card_le_of_injective code.encode hinjective
  simpa [Bits] using h

abbrev ConfigurationToken (cells : ℕ) :=
  StepToken Unit (ObliviousControl Unit (Fin (cells + 1)) Unit Bool) Unit

/-- Independent tape contents are independent possible finite-control tokens
of the existing one-cell compiler. -/
def tapeToken (input : Bits (cells + 1)) : ConfigurationToken cells :=
  ⟨(true, ⟨(), fun _ => 0, fun _ position => input position⟩), fun _ => ()⟩

theorem tapeToken_injective : Function.Injective (tapeToken (cells := cells)) := by
  intro first second heq
  funext position
  exact congrArg (fun token : ConfigurationToken cells => token.state.2.tape () position) heq

/-- The shortcut token alphabet is exponentially large in tape capacity. -/
theorem configurationToken_card_lower_bound :
    2 ^ (cells + 1) ≤ Fintype.card (ConfigurationToken cells) := by
  have h := Fintype.card_le_of_injective (tapeToken (cells := cells)) tapeToken_injective
  simpa [Bits] using h

/-- Binarizing the shortcut costs at least one bit per tape cell per token. -/
theorem configurationToken_code_width_lower_bound
    (code : BinaryCode (ConfigurationToken cells) width) : cells + 1 ≤ width := by
  have h := configurationToken_card_lower_bound.trans (BinaryCode.card_le_pow code)
  by_contra hnot
  have hlt : width < cells + 1 := by omega
  have hpow : 2 ^ width < 2 ^ (cells + 1) := Nat.pow_lt_pow_right (by decide) hlt
  omega

/-- A `steps + 1` event trace of the shortcut may require a quadratic number
of binary ciphertext bits when the tape capacity grows with `steps`. -/
theorem shortcut_binary_trace_length_lower_bound
    (code : BinaryCode (ConfigurationToken cells) width) (steps : ℕ) :
    (steps + 1) * (cells + 1) ≤ (steps + 1) * width :=
  Nat.mul_le_mul_left _ (configurationToken_code_width_lower_bound code)

end SimulationSizeAudit
