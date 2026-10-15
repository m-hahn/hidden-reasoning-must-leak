import TalComplete
import HiddenReasoningTax
import MultiplicationFootprint

/-! Unconditional lower-bound entry points using the locally proved Tal theorem. -/

noncomputable section
namespace TalConsequences
open TransformerAC0

theorem parityCorrelation_sq_le {n : ℕ} (circuit : Circuit n 1) (depth size : ℕ)
    (hdepth : circuit.depth ≤ depth) (hsize : circuit.gateCount ≤ size) (hsizeTwo : 1 < size) :
    Tal.uniformExpectation (fun input => Tal.circuitSign circuit input * Tal.boolSign (Tal.parity input)) ^ 2 ≤
      Tal.tailBound depth size n :=
  Tal.parityCorrelation_sq_le TalComplete.fourierTailTheorem circuit depth size hdepth hsize hsizeTwo

theorem circuit_correlation_le {n : ℕ} (target : Bits n → Bool) (circuit : Circuit n 1)
    (depth size degree : ℕ) (hdepth : circuit.depth ≤ depth) (hsize : circuit.gateCount ≤ size)
    (hsizeTwo : 1 < size) :
    |Tal.uniformExpectation (fun input => Tal.boolSign (circuit.eval input 0) * Tal.boolSign (target input))| ≤
      Real.sqrt (FourierCorrelation.lowerWeight (fun input => Tal.boolSign (target input)) degree) +
        Real.sqrt (Tal.tailBound depth size degree) :=
  FourierCorrelation.circuit_correlation_le TalComplete.fourierTailTheorem target circuit depth size degree hdepth hsize hsizeTwo

theorem footprint {n depthBound sizeBound : ℕ} {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]
    (trace : Footprint.ParityTrace n Transcript) (circuits : Footprint.FiberCircuitFamily trace depthBound sizeBound)
    (hn : 1 ≤ n) (hsizeTwo : 1 < sizeBound) :
    -Real.logb 2 (Real.sqrt (Tal.tailBound depthBound sizeBound n)) ≤ trace.uniformMutualInformation :=
  Footprint.footprint_from_tal TalComplete.fourierTailTheorem trace circuits hn hsizeTwo

theorem multiplication_footprint {N traceLength : ℕ}
    (model : Autoregressive.FixedPrecisionGenerator (N + N) traceLength)
    (correct : ∀ input, model.answer input = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.explicitFiberDepth model.explicitFiberSize) ≤
      (model.taskTrace (MultiplicationFootprint.middleBitTarget N) correct).uniformMutualInformation :=
  MultiplicationFootprint.autoregressive_footprint_explicit TalComplete.fourierTailTheorem model correct hN hsize

theorem multiplication_length {N traceLength : ℕ}
    (model : Autoregressive.FixedPrecisionGenerator (N + N) traceLength)
    (correct : ∀ input, model.answer input = MultiplicationFootprint.middleBitTarget N input)
    (hN : 2 ≤ N) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2 (MultiplicationFootprint.explicitFiberRate N model.explicitFiberDepth model.explicitFiberSize) ≤ traceLength :=
  MultiplicationFootprint.autoregressive_binary_length_lower_bound_explicit TalComplete.fourierTailTheorem model correct hN hsize

end TalConsequences
