import EntropyCoding

/-!
# A self-contained public-input length tax

This is the independent-uniform specialization of the paper's public/covert
length tradeoff.  It avoids an abstract entropy profile: public and covert
inputs, transcript fibers, recoverability, Shannon entropy, and the fixed
alphabet capacity bound are all concrete finite objects.
-/

open scoped BigOperators

noncomputable section

namespace PublicReasoningTax

open TransformerAC0

structure PublicBooleanTrace (covertBits publicBits : ℕ)
    (target : Bits covertBits → Bool) (Transcript : Type*) where
  transcript : Bits publicBits → Bits covertBits → Transcript
  answer : Bits publicBits → Bits covertBits → Bool
  answer_correct : ∀ public covert, answer public covert = target covert

namespace PublicBooleanTrace

variable {covertBits publicBits : ℕ} {target : Bits covertBits → Bool}
variable {Transcript : Type*} [Fintype Transcript] [DecidableEq Transcript]

def fixedPublic (G : PublicBooleanTrace covertBits publicBits target Transcript)
    (public : Bits publicBits) :
    TaskFootprint.BooleanTrace covertBits target Transcript where
  transcript := G.transcript public
  answer := G.answer public
  answer_correct := G.answer_correct public

def splitInput : Bits (publicBits + covertBits) ≃
    Bits publicBits × Bits covertBits :=
  (Equiv.piCongrLeft (fun _ : Fin (publicBits + covertBits) => Bool)
    finSumFinEquiv).symm |>.trans
      (Equiv.sumPiEquivProdPi (fun _ => Bool))

/-- The global transcript under independent uniform public and covert inputs. -/
def globalTrace (G : PublicBooleanTrace covertBits publicBits target Transcript) :
    Footprint.ParityTrace (publicBits + covertBits) Transcript where
  transcript := fun input =>
    let pair := splitInput.symm.symm input
    G.transcript pair.1 pair.2
  answer := Tal.parity
  answer_correct := fun _ => rfl

/-- The public input is exactly recoverable from the visible trace. -/
def PublicRecoverable
    (G : PublicBooleanTrace covertBits publicBits target Transcript) : Prop :=
  ∃ decode : Transcript → Bits publicBits,
    ∀ public covert, decode (G.transcript public covert) = public

omit [Fintype Transcript] in
theorem global_probability_eq_fixed_div
    (G : PublicBooleanTrace covertBits publicBits target Transcript)
    (recoverable : G.PublicRecoverable) (transcript : Transcript) :
    (G.globalTrace.transcriptProbability transcript) =
      (G.fixedPublic (Classical.choose recoverable transcript)).transcriptProbability
        transcript / (2 ^ publicBits : ℕ) := by
  classical
  let decode : Transcript → Bits publicBits := Classical.choose recoverable
  have hdecode : ∀ public covert,
      decode (G.transcript public covert) = public := Classical.choose_spec recoverable
  let selected := decode transcript
  have hvanish : ∀ public : Bits publicBits, public ≠ selected →
      ∀ covert : Bits covertBits, G.transcript public covert ≠ transcript := by
    intro public hpublic covert hequal
    apply hpublic
    rw [← hdecode public covert, hequal]
  rw [Footprint.ParityTrace.transcriptProbability_eq_expectation]
  rw [TaskFootprint.BooleanTrace.transcriptProbability,
    Footprint.ParityTrace.transcriptProbability_eq_expectation]
  change (∑ input : Bits (publicBits + covertBits),
      Footprint.boolIndicator
        (decide (G.globalTrace.transcript input = transcript))) /
      (2 ^ (publicBits + covertBits) : ℕ) =
    ((∑ covert : Bits covertBits,
      Footprint.boolIndicator
        (decide (G.transcript selected covert = transcript))) /
      (2 ^ covertBits : ℕ)) / (2 ^ publicBits : ℕ)
  have hreindex :
      (∑ pair : Bits publicBits × Bits covertBits,
          Footprint.boolIndicator
            (decide (G.transcript pair.1 pair.2 = transcript))) =
        ∑ input : Bits (publicBits + covertBits),
          Footprint.boolIndicator
            (decide (G.globalTrace.transcript input = transcript)) := by
    simpa [globalTrace, splitInput] using
      (Equiv.sum_comp splitInput
        (fun pair : Bits publicBits × Bits covertBits =>
          Footprint.boolIndicator
            (decide (G.transcript pair.1 pair.2 = transcript)))).symm
  rw [← hreindex, Fintype.sum_prod_type]
  have hcollapse :
      (∑ public : Bits publicBits, ∑ covert : Bits covertBits,
          Footprint.boolIndicator
            (decide (G.transcript public covert = transcript))) =
        ∑ covert : Bits covertBits,
          Footprint.boolIndicator
            (decide (G.transcript selected covert = transcript)) := by
    calc
      (∑ public : Bits publicBits, ∑ covert : Bits covertBits,
          Footprint.boolIndicator
            (decide (G.transcript public covert = transcript))) =
        ∑ public : Bits publicBits,
          if public = selected then
            ∑ covert : Bits covertBits,
              Footprint.boolIndicator
                (decide (G.transcript selected covert = transcript))
          else 0 := by
            apply Finset.sum_congr rfl
            intro public _
            by_cases hpublic : public = selected
            · subst public
              simp
            · simp [hpublic, hvanish public hpublic, Footprint.boolIndicator]
      _ = ∑ covert : Bits covertBits,
          Footprint.boolIndicator
            (decide (G.transcript selected covert = transcript)) := by simp
  rw [hcollapse]
  rw [pow_add]
  push_cast
  have hp : (2 : ℝ) ^ publicBits ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : (2 : ℝ) ^ covertBits ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hp, hc]
  exact Or.inl (mul_comm _ _)

theorem global_probability_le
    (G : PublicBooleanTrace covertBits publicBits target Transcript)
    (circuits : ∀ public,
      TaskFootprint.FiberCircuitFamily (G.fixedPublic public) depth size)
    {rate : ℝ}
    (correlation : TaskFootprint.SignCorrelationBound target depth size rate)
    (recoverable : G.PublicRecoverable) (transcript : Transcript) :
    G.globalTrace.transcriptProbability transcript ≤
      (rate + |TaskFootprint.targetBias target|) / (2 ^ publicBits : ℕ) := by
  rw [G.global_probability_eq_fixed_div recoverable transcript]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact TaskFootprint.transcriptProbability_le
    (G.fixedPublic (Classical.choose recoverable transcript))
    (circuits _) correlation transcript

/-- Concrete public-input plus hidden-computation entropy lower bound. -/
theorem entropy_lower_bound
    (G : PublicBooleanTrace covertBits publicBits target Transcript)
    (circuits : ∀ public,
      TaskFootprint.FiberCircuitFamily (G.fixedPublic public) depth size)
    {rate : ℝ}
    (correlation : TaskFootprint.SignCorrelationBound target depth size rate)
    (recoverable : G.PublicRecoverable)
    (hpositive : 0 < rate + |TaskFootprint.targetBias target|) :
    -Real.logb 2
        ((rate + |TaskFootprint.targetBias target|) / (2 ^ publicBits : ℕ)) ≤
      G.globalTrace.transcriptEntropy := by
  apply G.globalTrace.entropy_ge_neg_log_maxProbability
  · positivity
  · exact G.global_probability_le circuits correlation recoverable

/-- Fully concrete fixed-length version of the public-input reasoning tax. -/
theorem fixedLength_lower_bound
    (G : PublicBooleanTrace covertBits publicBits target
      (Fin length → Fin alphabet))
    (circuits : ∀ public,
      TaskFootprint.FiberCircuitFamily (G.fixedPublic public) depth size)
    {rate : ℝ}
    (correlation : TaskFootprint.SignCorrelationBound target depth size rate)
    (recoverable : G.PublicRecoverable)
    (hpositive : 0 < rate + |TaskFootprint.targetBias target|)
    (halphabet : 0 < alphabet) :
    -Real.logb 2
        ((rate + |TaskFootprint.targetBias target|) / (2 ^ publicBits : ℕ)) ≤
      (length : ℝ) * Real.logb 2 (alphabet : ℝ) := by
  exact (G.entropy_lower_bound circuits correlation recoverable hpositive).trans
    (EntropyCoding.fixedLength_entropy_le G.globalTrace halphabet)

end PublicBooleanTrace

end PublicReasoningTax
