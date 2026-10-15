import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedAdvice
import TalOptimizedNumerics
import TalBlockAdvice

/-!
# Quantitative advice count for family multi-switching

A phase consumes at least `shallow + 1` queries except at the end. Thus a
length-`D` encoding has at most `ceil(D/(shallow+1))` family indices. Global
answers and combined source-term advice are counted explicitly. This module
only counts the finite advice; it does not assume or assert an encoder for
the common-tree bad event.
-/

open scoped BigOperators
noncomputable section
namespace TalFamilyAdvice
open Algebraic AC0 Switching

def phaseSlots (shallow length : ℕ) : ℕ :=
  (length + shallow) / (shallow + 1)

def Advice (members width shallow length : ℕ) :=
  (Fin length → Bool) × (Fin (phaseSlots shallow length) → Fin members) ×
    CombinedAdvice width length

instance adviceFintype (members width shallow length : ℕ) :
    Fintype (Advice members width shallow length) := by
  unfold Advice
  infer_instance

theorem card_advice (members width shallow length : ℕ) :
    Fintype.card (Advice members width shallow length) =
      2 ^ length * (members ^ phaseSlots shallow length *
        Fintype.card (CombinedAdvice width length)) := by
  simp [Advice]

theorem family_index_count_le (members shallow length : ℕ) (hpositive : 0 < members)
    (hwidth : members ≤ 2 ^ (shallow + 1)) :
    members ^ phaseSlots shallow length ≤ members * 2 ^ length := by
  let slots := phaseSlots shallow length
  by_cases hslots : slots = 0
  · change members ^ slots ≤ _
    rw [hslots, pow_zero]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · have hslotspos : 0 < slots := Nat.pos_of_ne_zero hslots
    have hdiv := Nat.div_mul_le_self (length + shallow) (shallow + 1)
    change slots * (shallow + 1) ≤ length + shallow at hdiv
    have hproduct : (shallow + 1) * (slots - 1) ≤ length := by
      have hsub : slots = (slots - 1) + 1 := by omega
      rw [hsub] at hdiv
      nlinarith
    have hpower := Nat.pow_le_pow_left hwidth (slots - 1)
    rw [← pow_mul] at hpower
    have htwo := Nat.pow_le_pow_right (by norm_num : 0 < 2) hproduct
    have h := Nat.mul_le_mul_left members (hpower.trans htwo)
    have hsub : slots = (slots - 1) + 1 := by omega
    change members ^ slots ≤ _
    rw [hsub, pow_succ']
    exact h

theorem default_shallow_index_count_le (members length : ℕ) (hpositive : 0 < members) :
    members ^ phaseSlots (Nat.log 2 (2 * members)) length ≤ members * 2 ^ length := by
  apply family_index_count_le members _ length hpositive
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 * members)
  omega

/-- The total advice base is `10t-2`, allowing both global answers and phase indices. -/
theorem card_advice_le (members width shallow length : ℕ)
    (hmembers : 0 < members) (hwidth : 0 < width)
    (hindices : members ≤ 2 ^ (shallow + 1)) :
    (Fintype.card (Advice members width shallow length) : ℝ) ≤
      (members : ℝ) * (10 * (width : ℝ) - 2) ^ length := by
  have hfamily : (members : ℝ) ^ phaseSlots shallow length ≤
      (members : ℝ) * (2 : ℝ) ^ length := by
    exact_mod_cast family_index_count_le members shallow length hmembers hindices
  have hcombined := card_combinedAdvice_cast_le width length hwidth
  have hw : (1 : ℝ) ≤ width := by exact_mod_cast hwidth
  rw [card_advice]
  push_cast
  calc
    _ ≤ (2 : ℝ) ^ length * ((members : ℝ) * 2 ^ length *
        (((5 : ℝ) * width - 1) / 2) ^ length) := by gcongr
    _ = _ := by
      have hbase : (2 : ℝ) * (2 * ((5 * (width : ℝ) - 1) / 2)) = 10 * (width : ℝ) - 2 := by
        ring
      rw [← hbase, mul_pow, mul_pow]
      ring

/-- The simpler all-block route allows a matching term at each phase end. -/
def BroadAdvice (members width shallow length : ℕ) :=
  (Fin length → Bool) × (Fin (phaseSlots shallow length) → Fin members) ×
    TalBlockAdvice.Advice width length

instance broadAdviceFintype (members width shallow length : ℕ) :
    Fintype (BroadAdvice members width shallow length) := by
  unfold BroadAdvice
  infer_instance

theorem card_broadAdvice_le (members width shallow length : ℕ)
    (hmembers : 0 < members) (hwidth : 0 < width)
    (hindices : members ≤ 2 ^ (shallow + 1)) :
    (Fintype.card (BroadAdvice members width shallow length) : ℝ) ≤
      (members : ℝ) * (12 * (width : ℝ)) ^ length := by
  have hfamily : (members : ℝ) ^ phaseSlots shallow length ≤
      (members : ℝ) * (2 : ℝ) ^ length := by
    exact_mod_cast family_index_count_le members shallow length hmembers hindices
  have hblocks : (Fintype.card (TalBlockAdvice.Advice width length) : ℝ) ≤
      (3 * (width : ℝ)) ^ length := by
    simpa only [Nat.card_eq_fintype_card] using TalBlockAdvice.card_advice_le width length hwidth
  have hcard : Fintype.card (BroadAdvice members width shallow length) =
      2 ^ length * (members ^ phaseSlots shallow length *
        Fintype.card (TalBlockAdvice.Advice width length)) := by
    simp [BroadAdvice]
  rw [hcard]
  push_cast
  calc
    _ ≤ (2 : ℝ) ^ length * ((members : ℝ) * 2 ^ length *
        (3 * (width : ℝ)) ^ length) := by gcongr
    _ = _ := by
      rw [show (12 : ℝ) * width = 2 * (2 * (3 * width)) by ring]
      simp only [mul_pow]
      ring

end TalFamilyAdvice
