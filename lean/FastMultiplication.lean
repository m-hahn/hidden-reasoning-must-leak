import MultitapeTuring
import PhaseSemantics
import MultiplicationFootprint

/-!
# The permitted N log N multitape multiplication import

As with Tal and PRG security, the research theorem is an explicit argument,
not a hidden axiom. It supplies a single fixed finite machine on ordinary
unit-motion tapes, initialized by raw bits on one input tape. It does not
supply a Transformer, an oblivious simulator, future states, or a circuit
realization certificate. All consequences below are checked in Lean.
-/

noncomputable section
namespace FastMultiplication
open TransformerAC0 MultitapeTuring ObliviousPhase

def productBits (N : ℕ) (input : Bits (N + N)) : Bits (N + N) := fun bit =>
  let pair := (MultiplicationFootprint.residuePairBitsEquiv N).symm input
  Nat.testBit (pair.1.val * pair.2.val) bit.val

theorem middleBit_eq (N : ℕ) (hN : 1 ≤ N) (input : Bits (N + N)) :
    productBits N input ⟨N - 1, by omega⟩ = MultiplicationFootprint.middleBitTarget N input := rfl

def initialTape {tapes : ℕ} {Symbol : Type*} (inputTape : Fin tapes)
    (blank : Symbol) (bitSymbol : Bool → Symbol) (input : Bits (N + N)) : Fin tapes → ℤ → Symbol :=
  fun tape position => if h : tape = inputTape ∧ 0 ≤ position ∧ position < ((N + N : ℕ) : ℤ) then
    bitSymbol (input ⟨position.toNat, by omega⟩) else blank

def initialConfiguration {tapes : ℕ} {State Symbol : Type*}
    (machine : MultitapeTuring.Machine tapes State Symbol) (inputTape : Fin tapes)
    (blank : Symbol) (bitSymbol : Bool → Symbol) (input : Bits (N + N)) : Configuration tapes State Symbol :=
  ⟨machine.initialState, fun _ => 0, initialTape inputTape blank bitSymbol input⟩

/-- Each initial tape observation is either blank or one raw input bit.
The imported machine cannot receive multiplication in its initialization. -/
theorem initialTape_raw {tapes : ℕ} {Symbol : Type*} (inputTape : Fin tapes)
    (blank : Symbol) (bitSymbol : Bool → Symbol) (input : Bits (N + N)) (tape : Fin tapes) (position : ℤ) :
    initialTape inputTape blank bitSymbol input tape position =
      if h : tape = inputTape ∧ 0 ≤ position ∧ position < ((N + N : ℕ) : ℤ) then
        bitSymbol (input ⟨position.toNat, by omega⟩) else blank := rfl

/-- Precise statement of the sole permitted multiplication upper-bound
import. The finite types and tape count are fixed across all input lengths;
the bound charges actual local multitape transitions. -/
def MultitapeNLogNTheorem : Prop :=
  ∃ (tapes states symbols : ℕ)
    (machine : MultitapeTuring.Machine tapes (Fin states) (Fin symbols))
    (inputTape outputTape : Fin tapes) (blank : Fin symbols)
    (bitSymbol : Bool → Fin symbols) (decode : Fin symbols → Bool)
    (halted : Fin states → Prop) (coefficient : ℕ) (time : ℕ → ℕ),
    inputTape ≠ outputTape ∧
    Function.Injective bitSymbol ∧ (∀ bit, blank ≠ bitSymbol bit) ∧
    (∀ N, time N ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) ∧
    (∀ state, halted state → ∀ scanned, machine.transition state scanned =
      (state, scanned, fun _ => Direction.stay)) ∧
    (∀ N (input : Bits (N + N)),
      halted (machine.run (time N) (initialConfiguration machine inputTape blank bitSymbol input)).state ∧
      ∀ bit : Fin (N + N),
        decode ((machine.run (time N) (initialConfiguration machine inputTape blank bitSymbol input)).tape outputTape bit.val) =
          productBits N input bit)

/-- The N log N imported bound is polynomial; this elementary consequence
is not an extra research assumption. -/
theorem time_polynomial (time coefficient : ℕ)
    (bound : time ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) :
    time ≤ (2 * coefficient) * (N + 1) ^ 2 := by
  have hlog := Nat.log_le_self 2 (N + 1)
  have hbound : Nat.log 2 (N + 1) + 1 ≤ 2 * (N + 1) := by omega
  calc
    _ ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1) := bound
    _ ≤ coefficient * (N + 1) * (2 * (N + 1)) := Nat.mul_le_mul_left _ hbound
    _ = _ := by ring

/-- The allowed import yields full-product correctness at the same padded
power-of-two horizon used by the efficient compiler. Padding is justified
by the genuine halting transition, not by an assumed output certificate. -/
theorem padded_full_product (imported : MultitapeNLogNTheorem) :
  ∃ (tapes states symbols : ℕ)
    (machine : MultitapeTuring.Machine tapes (Fin states) (Fin symbols))
    (inputTape outputTape : Fin tapes) (blank : Fin symbols)
    (bitSymbol : Bool → Fin symbols) (decode : Fin symbols → Bool)
    (coefficient : ℕ) (time : ℕ → ℕ),
    (∀ N, time N ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) ∧
    ∀ N (input : Bits (N + N)) (bit : Fin (N + N)),
      decode ((machine.run (2 ^ horizonLevel (time N))
        (initialConfiguration machine inputTape blank bitSymbol input)).tape outputTape bit.val) = productBits N input bit := by
  obtain ⟨tapes, states, symbols, machine, inputTape, outputTape, blank, bitSymbol, decode,
    halted, coefficient, time, _, _, _, htime, hterminal, hcorrect⟩ := imported
  refine ⟨tapes, states, symbols, machine, inputTape, outputTape, blank, bitSymbol, decode,
    coefficient, time, htime, ?_⟩
  intro N input bit
  rw [machine.terminal_run_after _ (time N) _ (horizon_covers (time N))
    (hterminal _ (hcorrect N input).1)]
  exact (hcorrect N input).2 bit

end FastMultiplication
