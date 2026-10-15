import Footprint
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The hidden-reasoning length tax

This file formalizes the information-theoretic argument called the *Covert
Computation Length Tax* in the paper.  We keep the proof at exactly the level
used in the appendix.  Its three inputs are:

* the public input is recoverable from the terminated trace, hence
  `H(public, trace) = H(trace)`;
* adjoining the trace cannot decrease entropy, hence
  `H(covert, public) <= H(covert, public, trace)`;
* the terminal separator makes complete traces prefix-free, so the usual
  source-coding inequality gives
  `H(trace) <= E[length trace] * log₂ |ExtendedVocab|`.

The first two facts imply the exact identity-and-inequality calculation

`H(public) + I(covert ; (public, trace)) - I(covert ; public) <= H(trace)`.

Combining this with a footprint lower bound produces the paper's public-input
cost, covert-computation length tax, and piggy-backing benefit.  The final
theorems instantiate the footprint premise from the sign-correlation theorem
and directly from Tal's full Fourier-tail theorem.
-/

noncomputable section

namespace HiddenReasoningTax

/-! ## The entropy profile used by the appendix calculation -/

/--
The six Shannon entropies that occur in the length-tax proof.  This compact
profile avoids imposing a particular finite-probability-space API: the proof
uses only these entropies and the two standard laws stated below.
-/
structure EntropyProfile where
  covertEntropy : ℝ
  publicEntropy : ℝ
  traceEntropy : ℝ
  covertPublicEntropy : ℝ
  publicTraceEntropy : ℝ
  covertPublicTraceEntropy : ℝ

namespace EntropyProfile

/-- `I(covert ; public) = H(covert) + H(public) - H(covert, public)`. -/
def covertPublicMutualInformation (profile : EntropyProfile) : ℝ :=
  profile.covertEntropy + profile.publicEntropy - profile.covertPublicEntropy

/--
`I(covert ; (public, trace))`, the quantity to which the footprint theorem is
applied in the appendix.
-/
def covertPublicTraceMutualInformation (profile : EntropyProfile) : ℝ :=
  profile.covertEntropy + profile.publicTraceEntropy -
    profile.covertPublicTraceEntropy

/--
The entropy consequence of deterministic recoverability of the public input
from the trace: adjoining the recovered value does not change entropy.
-/
def PublicRecoverable (profile : EntropyProfile) : Prop :=
  profile.publicTraceEntropy = profile.traceEntropy

/--
The nonnegativity of `H(trace | covert, public)`, written in the form used by
the proof.
-/
def TraceConditionalEntropyNonnegative (profile : EntropyProfile) : Prop :=
  profile.covertPublicEntropy ≤ profile.covertPublicTraceEntropy

/--
The public marginal is uniform on strings of length `publicLength` over an
alphabet of cardinality `inputAlphabetCard`.
-/
def UniformPublicMarginal
    (profile : EntropyProfile) (publicLength inputAlphabetCard : ℕ) : Prop :=
  profile.publicEntropy =
    (publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ)

/--
The source-coding bound for terminated (therefore prefix-free) traces over the
extended vocabulary.  It is isolated as a named interface because the paper
uses the standard Kraft/source-coding theorem at this point.
-/
def EntropyLengthBound
    (profile : EntropyProfile) (expectedLength : ℝ)
    (extendedAlphabetCard : ℕ) : Prop :=
  profile.traceEntropy ≤
    expectedLength * Real.logb 2 (extendedAlphabetCard : ℝ)

/--
The core chain-rule calculation from the appendix.  Recoverability replaces
`H(public, trace)` by `H(trace)`; nonnegative conditional entropy accounts for
the only inequality.
-/
theorem entropy_tradeoff
    (profile : EntropyProfile)
    (recoverable : profile.PublicRecoverable)
    (conditionalEntropy : profile.TraceConditionalEntropyNonnegative) :
    profile.publicEntropy + profile.covertPublicTraceMutualInformation -
        profile.covertPublicMutualInformation ≤ profile.traceEntropy := by
  unfold PublicRecoverable at recoverable
  unfold TraceConditionalEntropyNonnegative at conditionalEntropy
  unfold covertPublicTraceMutualInformation covertPublicMutualInformation
  rw [recoverable]
  linarith

end EntropyProfile

/-! ## The exact hidden-reasoning tax -/

/--
The paper's length tax in exact, non-asymptotic form.

`footprintLower` is any proved lower bound on
`I(covert ; (public, trace))`.  The three summands in the conclusion are,
respectively, the public-input cost, the hidden-computation tax, and the
piggy-backing benefit.
-/
theorem hidden_reasoning_tax
    (profile : EntropyProfile)
    (publicLength inputAlphabetCard extendedAlphabetCard : ℕ)
    (expectedLength footprintLower : ℝ)
    (recoverable : profile.PublicRecoverable)
    (conditionalEntropy : profile.TraceConditionalEntropyNonnegative)
    (uniformPublic : profile.UniformPublicMarginal publicLength inputAlphabetCard)
    (sourceCoding : profile.EntropyLengthBound expectedLength extendedAlphabetCard)
    (footprint : footprintLower ≤ profile.covertPublicTraceMutualInformation)
    (extendedAlphabet_nontrivial : 1 < extendedAlphabetCard) :
    (publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) /
          Real.logb 2 (extendedAlphabetCard : ℝ) +
        footprintLower / Real.logb 2 (extendedAlphabetCard : ℝ) -
        profile.covertPublicMutualInformation /
          Real.logb 2 (extendedAlphabetCard : ℝ) ≤
      expectedLength := by
  have hlog : 0 < Real.logb 2 (extendedAlphabetCard : ℝ) := by
    apply Real.logb_pos
    · norm_num
    · exact_mod_cast extendedAlphabet_nontrivial
  have hentropy := profile.entropy_tradeoff recoverable conditionalEntropy
  have hnumerator :
      (publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) +
          footprintLower - profile.covertPublicMutualInformation ≤
        profile.traceEntropy := by
    rw [← uniformPublic]
    linarith
  rw [← add_div, ← sub_div]
  apply (div_le_iff₀ hlog).2
  exact hnumerator.trans sourceCoding

/-!
## Instantiating the footprint premise

The visible object in the footprint theorem is the pair `(public, trace)`.
`agreesWithFootprint` identifies the entropy-profile mutual information with
the concrete uniform mutual information already defined in `Footprint.lean`.
-/

open Footprint
open TransformerAC0

variable {n depthBound sizeBound : ℕ}
variable {Public Trace : Type*}
variable [Fintype Public] [DecidableEq Public]
variable [Fintype Trace] [DecidableEq Trace]

/--
Length tax from an arbitrary already-established footprint lower bound for a
concrete parity computation.
-/
theorem hidden_reasoning_tax_of_footprint
    (G : ParityTrace n (Public × Trace))
    (profile : EntropyProfile)
    (publicLength inputAlphabetCard extendedAlphabetCard : ℕ)
    (expectedLength footprintLower : ℝ)
    (recoverable : profile.PublicRecoverable)
    (conditionalEntropy : profile.TraceConditionalEntropyNonnegative)
    (uniformPublic : profile.UniformPublicMarginal publicLength inputAlphabetCard)
    (sourceCoding : profile.EntropyLengthBound expectedLength extendedAlphabetCard)
    (agreesWithFootprint :
      profile.covertPublicTraceMutualInformation = G.uniformMutualInformation)
    (footprint : footprintLower ≤ G.uniformMutualInformation)
    (extendedAlphabet_nontrivial : 1 < extendedAlphabetCard) :
    (publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) /
          Real.logb 2 (extendedAlphabetCard : ℝ) +
        footprintLower / Real.logb 2 (extendedAlphabetCard : ℝ) -
        profile.covertPublicMutualInformation /
          Real.logb 2 (extendedAlphabetCard : ℝ) ≤
      expectedLength := by
  apply hidden_reasoning_tax profile publicLength inputAlphabetCard
    extendedAlphabetCard expectedLength footprintLower recoverable conditionalEntropy
    uniformPublic sourceCoding
  · simpa only [agreesWithFootprint] using footprint
  · exact extendedAlphabet_nontrivial

/--
The exact tax obtained from the usual AC⁰ sign-correlation bound.  The term
`q - 3/2` is the explicit footprint lower bound proved in `Footprint.lean`.
-/
theorem hidden_reasoning_tax_of_sign_correlation
    (G : ParityTrace n (Public × Trace))
    (C : FiberCircuitFamily G depthBound sizeBound)
    (profile : EntropyProfile)
    (publicLength inputAlphabetCard extendedAlphabetCard : ℕ)
    (expectedLength q : ℝ)
    (recoverable : profile.PublicRecoverable)
    (conditionalEntropy : profile.TraceConditionalEntropyNonnegative)
    (uniformPublic : profile.UniformPublicMarginal publicLength inputAlphabetCard)
    (sourceCoding : profile.EntropyLengthBound expectedLength extendedAlphabetCard)
    (agreesWithFootprint :
      profile.covertPublicTraceMutualInformation = G.uniformMutualInformation)
    (hn : 1 ≤ n)
    (correlation : SignParityCorrelationBound n depthBound sizeBound
      ((2 : ℝ) ^ ((3 / 2 : ℝ) - q)))
    (extendedAlphabet_nontrivial : 1 < extendedAlphabetCard) :
    (publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) /
          Real.logb 2 (extendedAlphabetCard : ℝ) +
        (q - 3 / 2) / Real.logb 2 (extendedAlphabetCard : ℝ) -
        profile.covertPublicMutualInformation /
          Real.logb 2 (extendedAlphabetCard : ℝ) ≤
      expectedLength := by
  apply hidden_reasoning_tax_of_footprint G profile publicLength inputAlphabetCard
    extendedAlphabetCard expectedLength (q - 3 / 2) recoverable conditionalEntropy
    uniformPublic sourceCoding agreesWithFootprint
  · exact footprint_quantitative_of_sign G C hn q correlation
  · exact extendedAlphabet_nontrivial

/--
The hidden-reasoning tax obtained directly from Tal's full Fourier-tail
theorem, without assuming a separate parity-correlation theorem.
-/
theorem hidden_reasoning_tax_of_tal
    (tal : Tal.FourierTailTheorem)
    (G : ParityTrace n (Public × Trace))
    (C : FiberCircuitFamily G depthBound sizeBound)
    (profile : EntropyProfile)
    (publicLength inputAlphabetCard extendedAlphabetCard : ℕ)
    (expectedLength : ℝ)
    (recoverable : profile.PublicRecoverable)
    (conditionalEntropy : profile.TraceConditionalEntropyNonnegative)
    (uniformPublic : profile.UniformPublicMarginal publicLength inputAlphabetCard)
    (sourceCoding : profile.EntropyLengthBound expectedLength extendedAlphabetCard)
    (agreesWithFootprint :
      profile.covertPublicTraceMutualInformation = G.uniformMutualInformation)
    (hn : 1 ≤ n) (hsizeTwo : 1 < sizeBound)
    (extendedAlphabet_nontrivial : 1 < extendedAlphabetCard) :
    (publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) /
          Real.logb 2 (extendedAlphabetCard : ℝ) +
        (-Real.logb 2 (Real.sqrt (Tal.tailBound depthBound sizeBound n))) /
          Real.logb 2 (extendedAlphabetCard : ℝ) -
        profile.covertPublicMutualInformation /
          Real.logb 2 (extendedAlphabetCard : ℝ) ≤
      expectedLength := by
  apply hidden_reasoning_tax_of_footprint G profile publicLength inputAlphabetCard
    extendedAlphabetCard expectedLength
      (-Real.logb 2 (Real.sqrt (Tal.tailBound depthBound sizeBound n)))
      recoverable conditionalEntropy uniformPublic sourceCoding agreesWithFootprint
  · exact footprint_from_tal tal G C hn hsizeTwo
  · exact extendedAlphabet_nontrivial

/--
The appendix's fully substituted, non-asymptotic version.  Its middle summand
is the explicit representative of the displayed `Omega-tilde(n)` length tax;
the last summand is exactly the piggy-backing benefit.
-/
theorem hidden_reasoning_tax_quantitative
    (G : ParityTrace n (Public × Trace))
    (C : FiberCircuitFamily G depthBound sizeBound)
    (profile : EntropyProfile)
    (publicLength inputAlphabetCard extendedAlphabetCard : ℕ)
    (expectedLength M maxTraceLength F : ℝ) (L c : ℕ)
    (recoverable : profile.PublicRecoverable)
    (conditionalEntropy : profile.TraceConditionalEntropyNonnegative)
    (uniformPublic : profile.UniformPublicMarginal publicLength inputAlphabetCard)
    (sourceCoding : profile.EntropyLengthBound expectedLength extendedAlphabetCard)
    (agreesWithFootprint :
      profile.covertPublicTraceMutualInformation = G.uniformMutualInformation)
    (hn : 1 ≤ n)
    (correlation : SignParityCorrelationBound n depthBound sizeBound
      ((2 : ℝ) ^ ((3 / 2 : ℝ) -
        n / footprintScale n M maxTraceLength F L c)))
    (extendedAlphabet_nontrivial : 1 < extendedAlphabetCard) :
    (publicLength : ℝ) * Real.logb 2 (inputAlphabetCard : ℝ) /
          Real.logb 2 (extendedAlphabetCard : ℝ) +
        (n / footprintScale n M maxTraceLength F L c - 3 / 2) /
          Real.logb 2 (extendedAlphabetCard : ℝ) -
        profile.covertPublicMutualInformation /
          Real.logb 2 (extendedAlphabetCard : ℝ) ≤
      expectedLength := by
  apply hidden_reasoning_tax_of_footprint G profile publicLength inputAlphabetCard
    extendedAlphabetCard expectedLength
      (n / footprintScale n M maxTraceLength F L c - 3 / 2)
      recoverable conditionalEntropy uniformPublic sourceCoding agreesWithFootprint
  · exact footprint_information_lower_bound G C hn M maxTraceLength F L c correlation
  · exact extendedAlphabet_nontrivial

end HiddenReasoningTax
