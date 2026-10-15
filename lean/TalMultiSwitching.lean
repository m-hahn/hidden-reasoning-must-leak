import TalFamilyDecoding
import TalSwitching

/-!
# The common-tree family switching bound

The bad event is the absence of a shared adaptive restriction tree whose
leaves make every family member shallow. Its encoder, decoder, and weighted
injection are proved here using actual recoverable bad-event witnesses.
There is no assumption of an encoding, injectivity, or a switching theorem.
-/

open scoped ENNReal
noncomputable section
namespace TalMultiSwitching
open Algebraic AC0 TalCommonTree TalFamilyWitness

def Bad {n m : ℕ} (family : Fin m → DNF n) (shallow length : ℕ)
    (rho : PartialAssignment n) : Prop :=
  ¬HasCommonTree (fun index => (family index).eval) rho shallow (length - 1)

instance badDecidable {n m : ℕ} (family : Fin m → DNF n) (shallow length : ℕ) :
    DecidablePred (Bad family shallow length) := Classical.decPred _

def chosenWitness {n m width : ℕ} [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (rho : PartialAssignment n) (hbad : Bad family shallow length rho) :
    Witness family shallow width rho length :=
  Classical.choose (exists_recoverable_witness family shallow hwidth length rho hbad)

theorem chosenWitness_recoverable {n m width : ℕ} [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (rho : PartialAssignment n) (hbad : Bad family shallow length rho) :
    (chosenWitness family shallow hwidth length rho hbad).Recoverable :=
  Classical.choose_spec (exists_recoverable_witness family shallow hwidth length rho hbad)

def defaultAdvice (m width shallow length : ℕ) [NeZero m] [NeZero width] :
    TalFamilyAdvice.BroadAdvice m width shallow length :=
  (fun _ => false, fun _ => Fin.ofNat' m 0, TalBlockAdvice.Advice.default width length)

def encode {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (rho : PartialAssignment n) :
    PartialAssignment n × TalFamilyAdvice.BroadAdvice m width shallow length := by
  classical
  exact if hbad : Bad family shallow length rho then
    (chosenWitness family shallow hwidth length rho hbad).encode hwidth
  else (rho, defaultAdvice m width shallow length)

def extension {n m width : ℕ} [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (rho : PartialAssignment n) : PartialAssignment n := by
  classical
  exact if hbad : Bad family shallow length rho then
    (chosenWitness family shallow hwidth length rho hbad).extension
  else PartialAssignment.empty

theorem decode_encode_of_bad {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (rho : PartialAssignment n) (hbad : Bad family shallow length rho) :
    TalFamilyDecoder.decode family shallow length (encode family shallow hwidth length rho) = rho := by
  classical
  simp only [encode, dif_pos hbad]
  exact TalFamilyDecoding.decode_encode _
    (chosenWitness_recoverable family shallow hwidth length rho hbad) hwidth

theorem encode_injectiveOn_bad {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ) :
    ∀ left, Bad family shallow length left →
      ∀ right, Bad family shallow length right →
        encode family shallow hwidth length left = encode family shallow hwidth length right →
          left = right := by
  intro left hleft right hright heq
  have h := congrArg (TalFamilyDecoder.decode family shallow length) heq
  rwa [decode_encode_of_bad family shallow hwidth length left hleft,
    decode_encode_of_bad family shallow hwidth length right hright] at h

/-- The exact division-free common-tree switching inequality, including `p=0,1`. -/
theorem probability_bad_card_scaled_le {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (p : NNReal) (hone : p ≤ 1) :
    (RandomRestriction.fixedWeight p : ENNReal) ^ length *
        RandomRestriction.probability n p hone (Bad family shallow length) ≤
      (Fintype.card (TalFamilyAdvice.BroadAdvice m width shallow length) : ENNReal) *
        (p : ENNReal) ^ length := by
  classical
  apply RandomRestriction.probability_scaled_le_of_refinement_encoding
    n p hone (Bad family shallow length) (TalFamilyAdvice.BroadAdvice m width shallow length)
    length (extension family shallow hwidth length) (encode family shallow hwidth length)
    (encode_injectiveOn_bad family shallow hwidth length)
  · intro rho hbad
    simp only [encode, extension, dif_pos hbad, Witness.encode]
  · intro rho hbad
    simp only [extension, dif_pos hbad]
    exact (chosenWitness family shallow hwidth length rho hbad).extension_fixesOnlyLive
  · intro rho hbad
    simp only [extension, dif_pos hbad]
    exact (chosenWitness family shallow hwidth length rho hbad).extension_fixedCount

theorem card_broadAdvice_cast_le_ennreal (m width shallow length : ℕ)
    (hm : 0 < m) (hw : 0 < width) (hindices : m ≤ 2 ^ (shallow + 1)) :
    (Fintype.card (TalFamilyAdvice.BroadAdvice m width shallow length) : ENNReal) ≤
      (m : ENNReal) * (12 * (width : ENNReal)) ^ length := by
  have hnn : (Fintype.card (TalFamilyAdvice.BroadAdvice m width shallow length) : NNReal) ≤
      (m : NNReal) * (12 * (width : NNReal)) ^ length := by
    exact_mod_cast TalFamilyAdvice.card_broadAdvice_le m width shallow length hm hw hindices
  simpa using ENNReal.coe_le_coe.mpr hnn

/-- Explicit scaled probability bound with all finite advice counted. -/
theorem probability_bad_scaled_le {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (hindices : m ≤ 2 ^ (shallow + 1)) (p : NNReal) (hone : p ≤ 1) :
    (RandomRestriction.fixedWeight p : ENNReal) ^ length *
        RandomRestriction.probability n p hone (Bad family shallow length) ≤
      (m : ENNReal) * (12 * (p : ENNReal) * (width : ENNReal)) ^ length := by
  calc
    _ ≤ (Fintype.card (TalFamilyAdvice.BroadAdvice m width shallow length) : ENNReal) *
        (p : ENNReal) ^ length := probability_bad_card_scaled_le family shallow hwidth length p hone
    _ ≤ ((m : ENNReal) * (12 * (width : ENNReal)) ^ length) * (p : ENNReal) ^ length :=
      mul_le_mul_right' (card_broadAdvice_cast_le_ennreal m width shallow length
        (NeZero.pos m) (NeZero.pos width) hindices) _
    _ = _ := by rw [mul_assoc, ← mul_pow]; congr 2; ring

/-- Common-tree multi-switching for the independent `p`-restriction law. -/
theorem probability_bad_le {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (hindices : m ≤ 2 ^ (shallow + 1)) (p : NNReal) (hp : p < 1) :
    RandomRestriction.probability n p hp.le (Bad family shallow length) ≤
      (m : ENNReal) * ((24 * p * (width : NNReal) / (1 - p) : NNReal) : ENNReal) ^ length := by
  classical
  have hpositive : 0 < RandomRestriction.fixedWeight p := by
    exact div_pos (tsub_pos_iff_lt.mpr hp) (by norm_num)
  have hstepNN : RandomRestriction.fixedWeight p *
      (24 * p * (width : NNReal) / (1 - p)) = 12 * p * width := by
    unfold RandomRestriction.fixedWeight
    have hden : (1 - p : NNReal) ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hp)
    field_simp [hden]
    ring
  have hstep : (RandomRestriction.fixedWeight p : ENNReal) *
      ((24 * p * (width : NNReal) / (1 - p) : NNReal) : ENNReal) =
        12 * (p : ENNReal) * (width : ENNReal) := by
    exact_mod_cast hstepNN
  have hscaled := probability_bad_scaled_le family shallow hwidth length hindices p hp.le
  rw [← hstep, mul_pow] at hscaled
  have hscaled' : (RandomRestriction.fixedWeight p : ENNReal) ^ length *
      RandomRestriction.probability n p hp.le (Bad family shallow length) ≤
      (RandomRestriction.fixedWeight p : ENNReal) ^ length *
        ((m : ENNReal) * ((24 * p * (width : NNReal) / (1 - p) : NNReal) : ENNReal) ^ length) := by
    simpa only [mul_left_comm, mul_assoc] using hscaled
  by_contra h
  have hstrict := (ENNReal.mul_lt_mul_left
    (pow_ne_zero length (ENNReal.coe_ne_zero.mpr (ne_of_gt hpositive)))
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)).mpr (lt_of_not_ge h)
  exact (not_lt_of_ge hscaled') hstrict

/-- The same theorem in the real-valued law used by the Fourier lemmas. -/
theorem real_probability_bad_le {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (hindices : m ≤ 2 ^ (shallow + 1)) (p : NNReal) (hp : p < 1) :
    TalRandomRestriction.probability (p : ℝ) (Bad family shallow length) ≤
      (m : ℝ) * (24 * (p : ℝ) * width / (1 - p)) ^ length := by
  classical
  have hpReal : (p : ℝ) < 1 := NNReal.coe_lt_coe.mpr hp
  have hpZero : 0 ≤ (p : ℝ) := p.coe_nonneg
  have hbaseNonneg : 0 ≤ 24 * (p : ℝ) * width / (1 - p) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpZero) (Nat.cast_nonneg width))
      (sub_nonneg.mpr hpReal.le)
  have h := probability_bad_le family shallow hwidth length hindices p hp
  rw [← TalSwitching.ofReal_probability p hp.le] at h
  have htarget : (m : ENNReal) *
      ((24 * p * (width : NNReal) / (1 - p) : NNReal) : ENNReal) ^ length =
      ENNReal.ofReal ((m : ℝ) * (24 * (p : ℝ) * width / (1 - p)) ^ length) := by
    have hbase : ((24 * p * (width : NNReal) / (1 - p) : NNReal) : ℝ) =
        24 * (p : ℝ) * width / (1 - p) := by simp [NNReal.coe_sub hp.le]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_pow hbaseNonneg, ← hbase]
    simp only [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
  rw [htarget] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hbaseNonneg _))).mp h

theorem default_shallow_indices (m : ℕ) : m ≤ 2 ^ (Nat.log 2 (2 * m) + 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 * m)
  omega

theorem small_parameter_base {width : ℕ} [NeZero width] (p : NNReal)
    (hsmall : 30 * p * width ≤ 1) :
    p < 1 ∧ 24 * p * (width : NNReal) / (1 - p) ≤ 5 / 6 := by
  have hw : (1 : NNReal) ≤ width := by exact_mod_cast NeZero.pos width
  have h30 : 30 * p ≤ 1 := by
    have hprod : 30 * p ≤ 30 * p * width := by
      simpa only [mul_one] using mul_le_mul_left' hw (30 * p)
    exact hprod.trans hsmall
  have hp30 : p ≤ (1 / 30 : NNReal) := by
    apply (le_div_iff₀ (by norm_num : (0 : NNReal) < 30)).mpr
    simpa only [mul_comm] using h30
  have hp : p < 1 := hp30.trans_lt (by apply NNReal.coe_lt_coe.mp; norm_num)
  refine ⟨hp, ?_⟩
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
    NNReal.coe_sub hp.le, NNReal.coe_one]
  have hpReal : (p : ℝ) < 1 := NNReal.coe_lt_coe.mpr hp
  have hsmallReal : 30 * (p : ℝ) * width ≤ 1 := by exact_mod_cast hsmall
  have h30Real : 30 * (p : ℝ) ≤ 1 := by exact_mod_cast h30
  apply (div_le_iff₀ (sub_pos.mpr hpReal)).mpr
  nlinarith

/-- The constant-parameter geometric form used in circuit-depth reduction. -/
theorem real_probability_bad_le_geometric {n m width : ℕ} [NeZero m] [NeZero width]
    (family : Fin m → DNF n) (shallow : ℕ)
    (hwidth : ∀ index, (family index).WidthAtMost width) (length : ℕ)
    (hindices : m ≤ 2 ^ (shallow + 1)) (p : NNReal) (hsmall : 30 * p * width ≤ 1) :
    TalRandomRestriction.probability (p : ℝ) (Bad family shallow length) ≤
      (m : ℝ) * (5 / 6 : ℝ) ^ length := by
  obtain ⟨hp, hbase⟩ := small_parameter_base p hsmall
  have hbaseReal : 24 * (p : ℝ) * width / (1 - p) ≤ (5 / 6 : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hbase
    simpa only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
      NNReal.coe_sub hp.le, NNReal.coe_one] using h
  have hzero : 0 ≤ 24 * (p : ℝ) * width / (1 - p) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.coe_nonneg) (Nat.cast_nonneg width))
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hp.le))
  exact (real_probability_bad_le family shallow hwidth length hindices p hp).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hzero hbaseReal length) (Nat.cast_nonneg m))

end TalMultiSwitching
