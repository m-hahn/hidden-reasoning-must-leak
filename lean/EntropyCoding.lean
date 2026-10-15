import Autoregressive
import FiniteInformation
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Finite Shannon coding bounds

This file proves, rather than assumes, the finite-alphabet entropy-capacity
bound used to turn a footprint into a trace-length lower bound.
-/

noncomputable section

namespace EntropyCoding

open scoped BigOperators
open TransformerAC0
open Footprint

/-- The original footprint entropy is the Shannon entropy of the explicit
uniform input distribution. -/
theorem uniform_entropy_eq_transcriptEntropy
    {n : ℕ} {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]
    (G : ParityTrace n Transcript) :
    (FiniteInformation.Distribution.uniform (Bits n)).entropy G.transcript =
      G.transcriptEntropy := by
  unfold FiniteInformation.Distribution.entropy ParityTrace.transcriptEntropy
  apply Finset.sum_congr rfl
  intro transcript _
  rw [FiniteInformation.Distribution.uniform_pushMass_eq_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  change Real.negMulLog (G.transcriptProbability transcript) / Real.log 2 =
    -(G.transcriptProbability transcript) * Real.logb 2 (G.transcriptProbability transcript)
  unfold Real.negMulLog Real.logb
  ring

/-- Deterministic Shannon mutual information agrees with the footprint API. -/
theorem uniform_mutualInformation_eq_footprint
    {n : ℕ} {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]
    (G : ParityTrace n Transcript) :
    (FiniteInformation.Distribution.uniform (Bits n)).mutualInformation id G.transcript =
      G.uniformMutualInformation := by
  let D := FiniteInformation.Distribution.uniform (Bits n)
  have hjoint : D.jointEntropy id G.transcript = D.entropy id := by
    apply D.entropy_eq_of_comp (fun input => (input, G.transcript input)) id
      (fun input => (input, G.transcript input)) (fun _ => rfl) Prod.fst (fun _ => rfl)
  unfold FiniteInformation.Distribution.mutualInformation
  change D.entropy id + D.entropy G.transcript - D.jointEntropy id G.transcript = _
  rw [hjoint]
  have heq := uniform_entropy_eq_transcriptEntropy G
  change D.entropy G.transcript = G.uniformMutualInformation at heq
  linarith

variable {n : ℕ} {Transcript : Type*}
variable [Fintype Transcript] [DecidableEq Transcript] [Nonempty Transcript]

/-- Natural-log entropy of the deterministic transcript distribution. -/
def naturalEntropy (G : ParityTrace n Transcript) : ℝ :=
  ∑ transcript, Real.negMulLog (G.transcriptProbability transcript)

omit [DecidableEq Transcript] in
theorem transcript_card_pos : (0 : ℝ) < Fintype.card Transcript := by
  exact_mod_cast Fintype.card_pos

omit [DecidableEq Transcript] in
theorem sum_uniform_weights :
    ∑ _transcript : Transcript, (1 / (Fintype.card Transcript : ℝ)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_congr (Equiv.refl Transcript)]
  simp only [nsmul_eq_mul]
  field_simp

/-- Shannon entropy on a finite alphabet is at most the logarithm of the
alphabet cardinality. -/
theorem naturalEntropy_le_log_card (G : ParityTrace n Transcript) :
    naturalEntropy G ≤ Real.log (Fintype.card Transcript) := by
  let card : ℝ := Fintype.card Transcript
  have hcard : 0 < card := transcript_card_pos
  have hweights : ∑ _transcript : Transcript, (1 / card : ℝ) = 1 := by
    simpa [card] using (sum_uniform_weights (Transcript := Transcript))
  have hprob : ∀ transcript, 0 ≤ G.transcriptProbability transcript :=
    G.transcriptProbability_nonneg
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset Transcript))
    (w := fun _ => (1 / card : ℝ))
    (p := fun transcript => card * G.transcriptProbability transcript)
    (fun _ _ => by positivity) hweights
    (fun transcript _ => by
      exact Set.mem_Ici.mpr (mul_nonneg hcard.le (hprob transcript)))
  have hcenter :
      (∑ transcript : Transcript,
          (1 / card : ℝ) • (card * G.transcriptProbability transcript)) = 1 := by
    simp only [smul_eq_mul]
    calc
      (∑ transcript : Transcript,
          (1 / card) * (card * G.transcriptProbability transcript)) =
          ∑ transcript : Transcript, G.transcriptProbability transcript := by
            apply Finset.sum_congr rfl
            intro transcript _
            field_simp
      _ = 1 := G.sum_transcriptProbability
  rw [hcenter, Real.negMulLog_one] at hjensen
  have hexpand :
      (∑ transcript : Transcript,
          (1 / card : ℝ) •
            Real.negMulLog (card * G.transcriptProbability transcript)) =
        -Real.log card + naturalEntropy G := by
    simp only [smul_eq_mul, Real.negMulLog_mul]
    calc
      (∑ transcript : Transcript,
          (1 / card) *
            (G.transcriptProbability transcript * Real.negMulLog card +
              card * Real.negMulLog (G.transcriptProbability transcript))) =
          ∑ transcript : Transcript,
            ((1 / card) * G.transcriptProbability transcript * Real.negMulLog card +
              Real.negMulLog (G.transcriptProbability transcript)) := by
                apply Finset.sum_congr rfl
                intro transcript _
                field_simp
                ring
      _ = ∑ transcript : Transcript,
            (((1 / card) * Real.negMulLog card) *
              G.transcriptProbability transcript) + naturalEntropy G := by
            rw [Finset.sum_add_distrib]
            unfold naturalEntropy
            congr 1
            apply Finset.sum_congr rfl
            intro transcript _
            ring
      _ = (1 / card) * Real.negMulLog card *
            (∑ transcript : Transcript, G.transcriptProbability transcript) +
          naturalEntropy G := by
            rw [Finset.mul_sum]
      _ = -Real.log card + naturalEntropy G := by
            rw [G.sum_transcriptProbability, mul_one, Real.negMulLog]
            field_simp
            ring
  rw [hexpand] at hjensen
  linarith

omit [Nonempty Transcript] in
/-- Conversion between the paper's base-two entropy and natural entropy. -/
theorem transcriptEntropy_eq_naturalEntropy_div_log_two
    (G : ParityTrace n Transcript) :
    G.transcriptEntropy = naturalEntropy G / Real.log 2 := by
  unfold ParityTrace.transcriptEntropy naturalEntropy Real.negMulLog Real.logb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro transcript _
  ring

theorem transcriptEntropy_le_log_card (G : ParityTrace n Transcript) :
    G.transcriptEntropy ≤ Real.logb 2 (Fintype.card Transcript) := by
  rw [transcriptEntropy_eq_naturalEntropy_div_log_two, Real.logb]
  exact (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).2
    (naturalEntropy_le_log_card G)

/-- A length-`length` trace over an alphabet of cardinality `alphabet` carries
at most `length * log₂ alphabet` bits. -/
theorem fixedLength_entropy_le
    (G : ParityTrace n (Fin length → Fin alphabet))
    (halphabet : 0 < alphabet) :
    G.transcriptEntropy ≤
      (length : ℝ) * Real.logb 2 (alphabet : ℝ) := by
  letI : Nonempty (Fin alphabet) := Fin.pos_iff_nonempty.mp halphabet
  have h := transcriptEntropy_le_log_card G
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  have hcast : ((alphabet ^ length : ℕ) : ℝ) = (alphabet : ℝ) ^ length := by
    norm_num
  rw [hcast, Real.logb, Real.log_pow] at h
  rw [Real.logb]
  convert h using 1 <;> ring

/-- End-to-end binary trace-length lower bound from Tal and an automatically
constructed fixed-prefix circuit family. -/
theorem binary_length_at_least_footprint
    (G : ParityTrace n (Fin length → Bool)) (lower : ℝ)
    (footprint : lower ≤ G.uniformMutualInformation) :
    lower ≤ length := by
  have hcap : G.transcriptEntropy ≤ (length : ℝ) := by
    have h := transcriptEntropy_le_log_card G
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    have hcast : (((2 : ℕ) ^ length : ℕ) : ℝ) = (2 : ℝ) ^ length := by
      norm_num
    rw [hcast, Real.logb, Real.log_pow] at h
    have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
    convert h using 1
    field_simp
  exact footprint.trans hcap

/-- The footprint and coding arguments composed for an actual autoregressive
matrix-level fixed-precision Transformer.  No entropy profile, source-coding
certificate, or fiber-circuit family is assumed. -/
theorem autoregressive_binary_length_lower_bound
    (tal : Tal.FourierTailTheorem)
    (model : Autoregressive.FixedPrecisionGenerator n length)
    (correct : ∀ input, model.answer input = Tal.parity input)
    (hn : 1 ≤ n) (hsize : 1 < model.explicitFiberSize) :
    -Real.logb 2
        (Real.sqrt (Tal.tailBound model.explicitFiberDepth
          model.explicitFiberSize n)) ≤ length := by
  apply binary_length_at_least_footprint (model.parityTrace correct)
  exact model.footprint tal correct hn hsize

end EntropyCoding

