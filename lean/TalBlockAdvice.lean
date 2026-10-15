/-
Parts adapted from Samuel Schlesinger's complexitylib:
Complexitylib/Algebraic/LowerBound/AC0/Switching/CombinedAdvice.lean,
revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
SPDX-License-Identifier: MIT

The upstream MIT copyright and permission notice is included in full at
Complexitylib/Algebraic/LICENSE. Modified for this project: allow every final
block difference string and use the (3t)^D bound for the family-switching
argument. The binomial/exponential counting helper is adapted, not claimed
as independently authored here. See NOTICE for complete provenance.
-/

import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedAdvice

/-!
# Sorted-block advice without a mismatch requirement

For family switching, a phase can end on a matching canonical term. Keeping
all difference strings avoids an extra path-selection argument. The finite
advice still has cardinality at most `(3t)^D`. This is an alternative counting
component for the family proof. The complete circuit induction and
normalization are proved in `TalNetworkFourier` and `TalSharedCircuit`.

The binomial/exponential counting helper is adapted from Samuel Schlesinger's
MIT-licensed `Switching.CombinedAdvice`, whose copyright and license are
preserved in `Complexitylib/Algebraic/`.
-/

open scoped BigOperators
noncomputable section
namespace TalBlockAdvice
open Algebraic AC0 Switching

/-- Sorted nonempty source-term blocks, occupying exactly `length` queries. -/
def Advice (width : ℕ) : ℕ → Type
  | 0 => PUnit
  | length + 1 =>
      (block : Fin (min width (length + 1))) ×
        (BlockAdvice width (block.val + 1) × Advice width (length - block.val))

instance adviceFinite (width length : ℕ) : Finite (Advice width length) := by
  induction length using Nat.strong_induction_on with
  | h length ih =>
      cases length with
      | zero => unfold Advice; infer_instance
      | succ remaining =>
          unfold Advice
          let _ : ∀ block : Fin (min width (remaining + 1)),
              Fintype (Advice width (remaining - block.val)) :=
            fun block => @Fintype.ofFinite _ (ih _ (by omega))
          infer_instance

instance adviceFintype (width length : ℕ) : Fintype (Advice width length) :=
  Fintype.ofFinite _

theorem card_advice_succ (width length : ℕ) :
    Nat.card (Advice width (length + 1)) =
      ∑ block : Fin (min width (length + 1)),
        width.choose (block.val + 1) * 2 ^ (block.val + 1) *
          Nat.card (Advice width (length - block.val)) := by
  rw [Advice]
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro block _
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := BlockAdvice _ _), card_blockAdvice]

private theorem positive_binomial_sum_le_exp (width cutoff : ℕ) (beta : ℝ)
    (hbeta : 0 < beta) :
    (∑ index : Fin (min width cutoff), (width.choose (index.val + 1) : ℝ) *
      (2 / beta) ^ (index.val + 1)) ≤ Real.exp (2 * width / beta) - 1 := by
  change (∑ index : Fin (min width cutoff),
      (fun index : ℕ => (width.choose (index + 1) : ℝ) *
        (2 / beta) ^ (index + 1)) index) ≤ _
  let summand := fun index : ℕ => (width.choose (index + 1) : ℝ) *
      (2 / beta) ^ (index + 1)
  change (∑ index : Fin (min width cutoff), summand index.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range summand (min width cutoff)]
  dsimp only [summand]
  have termwise : ∀ index ∈ Finset.range (min width cutoff),
      (width.choose (index + 1) : ℝ) * (2 / beta) ^ (index + 1) ≤
        (2 * width / beta) ^ (index + 1) / (index + 1).factorial := by
    intro index _
    calc
      _ ≤ ((width : ℝ) ^ (index + 1) / (index + 1).factorial) *
          (2 / beta) ^ (index + 1) :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div (index + 1) width) (by positivity)
      _ = _ := by
        field_simp [ne_of_gt hbeta, Nat.factorial_ne_zero]
        ring
  calc
    _ ≤ ∑ index ∈ Finset.range (min width cutoff),
        (2 * width / beta) ^ (index + 1) / (index + 1).factorial :=
      Finset.sum_le_sum termwise
    _ ≤ _ := by
      have hseries := Real.sum_le_exp_of_nonneg
        (show (0 : ℝ) ≤ 2 * width / beta by positivity) (min width cutoff + 1)
      rw [Finset.sum_range_succ'] at hseries
      norm_num [Nat.factorial] at hseries ⊢
      linarith

private theorem exp_two_thirds_le_two : Real.exp (2 / 3 : ℝ) ≤ 2 := by
  calc
    _ ≤ (∑ index ∈ Finset.range 4, (2 / 3 : ℝ) ^ index / index.factorial) +
        (2 / 3 : ℝ) ^ 4 * (4 + 1) / ((4 : ℕ).factorial * 4) :=
      Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
    _ ≤ _ := by norm_num [Finset.sum_range_succ, Nat.factorial]

theorem normalized_count_le_one (width length : ℕ) (hwidth : 0 < width) :
    (∑ index : Fin (min width length), (width.choose (index.val + 1) : ℝ) *
      (2 / (3 * (width : ℝ))) ^ (index.val + 1)) ≤ 1 := by
  have hw : (0 : ℝ) < width := by exact_mod_cast hwidth
  have h := positive_binomial_sum_le_exp width length (3 * width) (by positivity)
  have hratio : (2 * (width : ℝ)) / (3 * width) = 2 / 3 := by field_simp; ring
  rw [hratio] at h
  linarith [exp_two_thirds_le_two]

theorem card_advice_le (width length : ℕ) (hwidth : 0 < width) :
    (Nat.card (Advice width length) : ℝ) ≤ (3 * (width : ℝ)) ^ length := by
  have hw : (0 : ℝ) < width := by exact_mod_cast hwidth
  induction length using Nat.strong_induction_on with
  | h length ih =>
      cases length with
      | zero => simp [Advice]
      | succ remaining =>
          rw [card_advice_succ]
          push_cast
          calc
            _ ≤ ∑ block : Fin (min width (remaining + 1)),
                (width.choose (block.val + 1) : ℝ) * 2 ^ (block.val + 1) *
                  (3 * (width : ℝ)) ^ (remaining - block.val) := by
              apply Finset.sum_le_sum
              intro block _
              exact mul_le_mul_of_nonneg_left (ih _ (by omega)) (by positivity)
            _ = (3 * (width : ℝ)) ^ (remaining + 1) *
                ∑ block : Fin (min width (remaining + 1)),
                  (width.choose (block.val + 1) : ℝ) *
                    (2 / (3 * (width : ℝ))) ^ (block.val + 1) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro block _
              have hlength : remaining + 1 =
                  (remaining - block.val) + (block.val + 1) := by omega
              conv_rhs => lhs; rw [hlength, pow_add]
              rw [div_pow]
              field_simp
              ring
            _ ≤ (3 * (width : ℝ)) ^ (remaining + 1) * 1 :=
              mul_le_mul_of_nonneg_left (normalized_count_le_one width _ hwidth) (by positivity)
            _ = _ := mul_one _

end TalBlockAdvice
