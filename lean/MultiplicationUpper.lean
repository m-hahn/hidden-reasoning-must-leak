import MultitapeMatrix
import FastMultiplication

/-!
# Near-linear multiplication by an actual numerical Transformer

Only the explicitly permitted N log N multitape machine theorem is imported.
The efficient oblivious instruction compiler, numerical matrix execution,
initialization, halting padding and resulting log-squared overhead are all
derived. No Transformer or simulation certificate is a theorem premise.
-/

noncomputable section
namespace MultiplicationUpper
open TransformerAC0 ObliviousPhase

def timeHorizon (time : ℕ) : ℕ := max 1 time
def traceConstant (tapes coefficient : ℕ) : ℕ :=
  (4 * (248 * tapes + 1)) * (coefficient + 1) * (Nat.log 2 (2 * (coefficient + 1)) + 4)

theorem horizon_time_bound (coefficient N time : ℕ)
    (bound : time ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) :
    timeHorizon time ≤ (coefficient + 1) * (N + 1) * (Nat.log 2 (N + 1) + 1) := by
  have hp : 1 ≤ (N + 1) * (Nat.log 2 (N + 1) + 1) := by nlinarith
  unfold timeHorizon
  apply max_le
  · nlinarith
  · nlinarith

theorem log_time_bound (coefficient N time : ℕ)
    (bound : time ≤ (coefficient + 1) * (N + 1) * (Nat.log 2 (N + 1) + 1)) :
    Nat.log 2 time + 1 ≤ (Nat.log 2 (2 * (coefficient + 1)) + 4) * (Nat.log 2 (N + 1) + 1) := by
  have hpoly := FastMultiplication.time_polynomial time (coefficient + 1) bound
  have hn : N + 1 ≤ 2 ^ (Nat.log 2 (N + 1) + 1) := (Nat.lt_pow_succ_log_self (by decide) (N + 1)).le
  have hc : 2 * (coefficient + 1) ≤ 2 ^ (Nat.log 2 (2 * (coefficient + 1)) + 1) :=
    (Nat.lt_pow_succ_log_self (by decide) (2 * (coefficient + 1))).le
  have hp : time ≤ 2 ^ ((Nat.log 2 (2 * (coefficient + 1)) + 1) + 2 * (Nat.log 2 (N + 1) + 1)) := by
    calc
      _ ≤ (2 * (coefficient + 1)) * (N + 1) ^ 2 := hpoly
      _ ≤ 2 ^ (Nat.log 2 (2 * (coefficient + 1)) + 1) * (2 ^ (Nat.log 2 (N + 1) + 1)) ^ 2 :=
        Nat.mul_le_mul hc (Nat.pow_le_pow_left hn 2)
      _ = _ := by rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
  have hl := Nat.log_mono_right (b := 2) hp
  rw [Nat.log_pow (by decide)] at hl
  nlinarith

theorem trace_bound {tapes : ℕ} {State Symbol : Type*}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (coefficient N time : ℕ) (bound : time ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) :
    MultitapeMatrix.eventSteps machine anchor (horizonLevel (timeHorizon time)) ≤
      traceConstant tapes coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1) ^ 2 := by
  have ht := horizon_time_bound coefficient N time bound
  have hl := log_time_bound coefficient N (timeHorizon time) ht
  calc
    _ ≤ (4 * (248 * tapes + 1)) * timeHorizon time * (Nat.log 2 (timeHorizon time) + 1) :=
      MultitapeMatrix.transcript_count_bound machine anchor (timeHorizon time) (Nat.le_max_left _ _)
    _ ≤ (4 * (248 * tapes + 1)) * ((coefficient + 1) * (N + 1) * (Nat.log 2 (N + 1) + 1)) *
        ((Nat.log 2 (2 * (coefficient + 1)) + 4) * (Nat.log 2 (N + 1) + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hl
    _ = _ := by unfold traceConstant; ring

theorem trace_polynomial_bound {tapes : ℕ} {State Symbol : Type*}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (coefficient N time : ℕ) (bound : time ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) :
    MultitapeMatrix.eventSteps machine anchor (horizonLevel (timeHorizon time)) ≤
      (4 * traceConstant tapes coefficient) * (N + 1) ^ 3 := by
  have ht := trace_bound machine anchor coefficient N time bound
  have hl : Nat.log 2 (N + 1) + 1 ≤ 2 * (N + 1) := by have h := Nat.log_le_self 2 (N + 1); omega
  calc
    _ ≤ traceConstant tapes coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1) ^ 2 := ht
    _ ≤ traceConstant tapes coefficient * (N + 1) * (2 * (N + 1)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl 2)
    _ = _ := by ring

def dimensionConstant (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] : ℕ :=
  RoutedMatrix.dimensionConstant (MultitapeMatrix.vocabulary tapes State Symbol) 2 (MultitapeMatrix.opcodes tapes State Symbol)

def parameterConstant (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol] : ℕ :=
  3 * MultitapeMatrix.vocabulary tapes State Symbol * dimensionConstant tapes State Symbol +
    4 * (3 * 2 + 2) * dimensionConstant tapes State Symbol ^ 2

theorem window_polynomial_bound {tapes : ℕ} {State Symbol : Type*}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (coefficient N time : ℕ) (bound : time ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) :
    ObliviousMatrix.window (MultitapeMatrix.eventSteps machine anchor (horizonLevel (timeHorizon time))) + 1 ≤
      (8 * traceConstant tapes coefficient + 3) * (N + 1) ^ 3 := by
  have he := trace_polynomial_bound machine anchor coefficient N time bound
  have hp : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  unfold ObliviousMatrix.window
  nlinarith

theorem dimension_polynomial_bound {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (coefficient N time : ℕ) (bound : time ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) :
    (RoutedMatrix.architecture (MultitapeMatrix.vocabulary tapes State Symbol)
      (ObliviousMatrix.window (MultitapeMatrix.eventSteps machine anchor (horizonLevel (timeHorizon time)))) 2
      (MultitapeMatrix.opcodes tapes State Symbol)).hiddenWidth ≤
        (2 * dimensionConstant tapes State Symbol * (8 * traceConstant tapes coefficient + 3)) * (N + 1) ^ 3 := by
  have hw := window_polynomial_bound machine anchor coefficient N time bound
  exact (RoutedMatrix.hidden_dimension_linear).trans (by
    simpa only [dimensionConstant, Nat.mul_assoc] using Nat.mul_le_mul_left (2 * dimensionConstant tapes State Symbol) hw)

theorem parameter_polynomial_bound {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (coefficient N time : ℕ) (bound : time ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)) :
    (RoutedMatrix.architecture (MultitapeMatrix.vocabulary tapes State Symbol)
      (ObliviousMatrix.window (MultitapeMatrix.eventSteps machine anchor (horizonLevel (timeHorizon time)))) 2
      (MultitapeMatrix.opcodes tapes State Symbol)).parameterCount ≤
        (parameterConstant tapes State Symbol * (8 * traceConstant tapes coefficient + 3) ^ 2) * (N + 1) ^ 6 := by
  have hw := window_polynomial_bound machine anchor coefficient N time bound
  calc
    _ ≤ parameterConstant tapes State Symbol *
        (ObliviousMatrix.window (MultitapeMatrix.eventSteps machine anchor (horizonLevel (timeHorizon time))) + 1) ^ 2 :=
      RoutedMatrix.parameter_count_quadratic
    _ ≤ parameterConstant tapes State Symbol *
        ((8 * traceConstant tapes coefficient + 3) * (N + 1) ^ 3) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2)
    _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul]; ring

/-- The real, shared numerical matrix model computes the paper's lower
middle multiplication bit, with one layer, two heads, fixed precision and
an explicitly derived N log-squared N event bound. -/
theorem matrix_upper_bound (imported : FastMultiplication.MultitapeNLogNTheorem) :
  ∃ (tapes states symbols : ℕ)
    (machine : MultitapeTuring.Machine tapes (Fin states) (Fin symbols))
    (inputTape outputTape : Fin tapes) (blank : Fin symbols)
    (bitSymbol : Bool → Fin symbols) (decode : Fin symbols → Bool)
    (coefficient : ℕ) (time : ℕ → ℕ),
    ∀ N, 1 ≤ N →
      (∀ input : Bits (N + N),
        (MultitapeMatrix.bitModel machine inputTape blank bitSymbol inputTape (N + N)
          (horizonLevel (timeHorizon (time N))) outputTape ((N - 1 : ℕ) : ℤ) decode).answer
          (MultitapeMatrix.bitInput machine inputTape blank bitSymbol inputTape
            (horizonLevel (timeHorizon (time N))) outputTape ((N - 1 : ℕ) : ℤ) input) =
              MultiplicationFootprint.middleBitTarget N input) ∧
      MultitapeMatrix.eventSteps machine inputTape (horizonLevel (timeHorizon (time N))) ≤
        traceConstant tapes coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1) ^ 2 ∧
      (MultitapeMatrix.bitModel machine inputTape blank bitSymbol inputTape (N + N)
        (horizonLevel (timeHorizon (time N))) outputTape ((N - 1 : ℕ) : ℤ) decode).parameters.scalarBits =
          RoutedMatrix.precision (MultitapeMatrix.vocabulary tapes (Fin states) (Fin symbols)) 2
            (MultitapeMatrix.opcodes tapes (Fin states) (Fin symbols)) := by
  obtain ⟨tapes, states, symbols, machine, inputTape, outputTape, blank, bitSymbol, decode,
    halted, coefficient, time, _, _, _, htime, hterminal, hcorrect⟩ := imported
  refine ⟨tapes, states, symbols, machine, inputTape, outputTape, blank, bitSymbol, decode, coefficient, time, ?_⟩
  intro N hN
  refine ⟨?_, trace_bound machine inputTape coefficient N (time N) (htime N), rfl⟩
  intro input
  rw [MultitapeMatrix.bit_output_correct]
  change decode ((machine.run (2 ^ horizonLevel (timeHorizon (time N)))
    (FastMultiplication.initialConfiguration machine inputTape blank bitSymbol input)).tape outputTape ((N - 1 : ℕ) : ℤ)) = _
  rw [machine.terminal_run_after _ (time N) _
    ((Nat.le_max_right 1 (time N)).trans (horizon_covers (timeHorizon (time N))))
    (hterminal _ (hcorrect N input).1)]
  exact (hcorrect N input).2 ⟨N - 1, by omega⟩

end MultiplicationUpper
