import TalBlockAdvice
import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalPacking

/-!
# Packing the actual sorted block transcript

Unlike the sharper single-formula code, this code permits an arbitrary
difference string in every block. The last global boundary marker is omitted;
all other block ends are recovered from the indexed block lengths.
-/

noncomputable section
namespace TalBlockAdvice
open Algebraic AC0 Switching

def Advice.succEquiv (width length : ℕ) :
    Advice width (length + 1) ≃
      ((block : Fin (min width (length + 1))) ×
        (BlockAdvice width (block.val + 1) × Advice width (length - block.val))) := by
  simp only [Advice]
  exact Equiv.refl _

def Advice.toQueryList {width : ℕ} : {length : ℕ} → Advice width length → List (QueryAdvice width)
  | 0, _ => []
  | length + 1, advice =>
      let view := Advice.succEquiv width length advice
      view.2.1.toQueryList (decide (0 < length - view.1.val)) ++
        Advice.toQueryList view.2.2

theorem Advice.length_toQueryList {width length : ℕ} (advice : Advice width length) :
    advice.toQueryList.length = length := by
  induction length using Nat.strong_induction_on with
  | h length ih =>
      cases length with
      | zero => rw [Advice.toQueryList]; rfl
      | succ remaining =>
          rw [Advice.toQueryList]
          simp only [List.length_append, BlockAdvice.length_toQueryList]
          rw [ih _ (by omega)]
          have hindex := (Advice.succEquiv width remaining advice).1.isLt
          omega

def Advice.prepend {width blockRemaining tailLength : ℕ}
    (block : BlockAdvice width (blockRemaining + 1)) (tail : Advice width tailLength)
    (hwidth : blockRemaining + 1 ≤ width) : Advice width (blockRemaining + 1 + tailLength) := by
  have htotal : blockRemaining + 1 + tailLength = (blockRemaining + tailLength) + 1 := by omega
  have htail : blockRemaining + tailLength - blockRemaining = tailLength := by omega
  let index : Fin (min width (blockRemaining + tailLength + 1)) := ⟨blockRemaining, by omega⟩
  let payload : Advice width (blockRemaining + tailLength - index.val) :=
    htail.symm ▸ tail
  let raw : Advice width ((blockRemaining + tailLength) + 1) :=
    (Advice.succEquiv width (blockRemaining + tailLength)).symm ⟨index, block, payload⟩
  exact htotal.symm ▸ raw

theorem Advice.toQueryList_cast {width left right : ℕ} (heq : left = right)
    (advice : Advice width left) :
    Advice.toQueryList (length := right) (heq ▸ advice) = advice.toQueryList := by
  subst right
  rfl

theorem Advice.toQueryList_prepend {width blockRemaining tailLength : ℕ}
    (block : BlockAdvice width (blockRemaining + 1)) (tail : Advice width tailLength)
    (hwidth : blockRemaining + 1 ≤ width) :
    (Advice.prepend block tail hwidth).toQueryList =
      block.toQueryList (decide (0 < tailLength)) ++ tail.toQueryList := by
  unfold Advice.prepend
  rw [Advice.toQueryList_cast, Advice.toQueryList]
  dsimp only
  rw [Equiv.apply_symm_apply]
  have htail : blockRemaining + tailLength - blockRemaining = tailLength := by omega
  simp only [htail, Advice.toQueryList_cast]

structure Packing (width : ℕ) (blocks : List (List (RelativeQuery width))) where
  advice : Advice width (blocks.map List.length).sum
  toQueryList : advice.toQueryList = relativeBlocksToQueryList blocks

def pack (width : ℕ) (blocks : List (List (RelativeQuery width)))
    (hnonempty : ∀ block ∈ blocks, block ≠ [])
    (hsorted : ∀ block ∈ blocks, (block.map Prod.fst).Pairwise (· < ·))
    (hwidth : ∀ block ∈ blocks, block.length ≤ width) : Packing width blocks := by
  induction blocks with
  | nil =>
      let unit : Advice width 0 := by simp only [Advice]; exact PUnit.unit
      exact ⟨unit, by rw [Advice.toQueryList]; rfl⟩
  | cons block tail ih =>
      have hblock := hnonempty block (by simp)
      cases block with
      | nil => exact False.elim (hblock rfl)
      | cons query rest =>
          have htailnonempty : ∀ block ∈ tail, block ≠ [] := fun block h =>
            hnonempty block (by simp [h])
          let tailPacking := ih htailnonempty
            (fun block h => hsorted block (by simp [h]))
            (fun block h => hwidth block (by simp [h]))
          let blockAdvice := BlockAdvice.ofRelativeBlock (query :: rest) (hsorted _ (by simp))
          let raw := Advice.prepend blockAdvice tailPacking.advice
            (hwidth (query :: rest) (by simp))
          have htotal : rest.length + 1 + (tail.map List.length).sum =
              (((query :: rest) :: tail).map List.length).sum := by simp
          refine ⟨htotal ▸ raw, ?_⟩
          rw [show Advice.toQueryList (length := (((query :: rest) :: tail).map List.length).sum)
              (htotal ▸ raw) = raw.toQueryList from
              Advice.toQueryList_cast htotal raw,
            Advice.toQueryList_prepend,
            BlockAdvice.toQueryList_ofRelativeBlock, tailPacking.toQueryList]
          cases tail with
          | nil => simp [relativeBlocksToQueryList]
          | cons next remaining =>
              have hnext := htailnonempty next (by simp)
              have hpositive := List.length_pos_iff.mpr hnext
              have hsum : 0 < ((next :: remaining).map List.length).sum := by
                simp only [List.map_cons, List.sum_cons]
                omega
              simp only [hsum, decide_true]
              rfl

/-- Harmless total advice for restrictions outside the counted event. -/
def Advice.default (width : ℕ) [NeZero width] : (length : ℕ) → Advice width length
  | 0 => by simp only [Advice]; exact PUnit.unit
  | length + 1 => by
      let index : Fin (min width (length + 1)) := ⟨0, by have h := NeZero.pos width; omega⟩
      let block : BlockAdvice width 1 :=
        ⟨⟨{Fin.ofNat' width 0}, by simp⟩, fun _ => false⟩
      refine (Advice.succEquiv width length).symm ?_
      refine ⟨index, block, ?_⟩
      simpa only [Nat.sub_zero] using Advice.default width length

end TalBlockAdvice
