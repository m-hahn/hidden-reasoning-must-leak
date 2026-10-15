/-
Copyright (c) 2026 Kenny Daniel. MIT license; see IntegerMultBounds/LICENSE.
Ported from platypii/integer-mult-bounds-lean, commit
9b148a008183b1342e134af1270d3a7dafad4a9c, for Lean/mathlib v4.19.0.
All proof dependencies of the classical multiplier are included locally.
-/

import IntegerMultBounds.Machine.Placement
import Mathlib.Logic.Equiv.Fintype

/-! A fixed injection of active tape slots extends to a whole-bank placement.
The complementary tape ordering is irrelevant: every complementary tape and
head is preserved by the already verified placement construction. -/


namespace IntegerMultBounds.Machine.InjectivePlacement
variable {s u t : ℕ}

theorem exists_extending_pair {α β : Type*} [Fintype β]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ p : Equiv.Perm β, ∀ x, p (f x) = g x := by
  classical
  let e := (Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)
  refine ⟨e.extendSubtype, fun x => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (f x) ⟨x, rfl⟩]
  change (e ((Equiv.ofInjective f hf) x)).val = g x
  simp [e]

noncomputable def permutation (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) : Equiv.Perm (Fin t) :=
  Classical.choose (exists_extending_pair
    (fun i => (finCongr hsize) (Fin.castAdd u i)) slot
    ((finCongr hsize).injective.comp (Fin.castAdd_injective _ _)) hinj)

theorem permutation_apply (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) (i : Fin s) :
    permutation slot hinj hsize ((finCongr hsize) (Fin.castAdd u i)) = slot i :=
  Classical.choose_spec (exists_extending_pair
    (fun i => (finCongr hsize) (Fin.castAdd u i)) slot
    ((finCongr hsize).injective.comp (Fin.castAdd_injective _ _)) hinj) i

noncomputable def placement (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) : Fin (s+u) ≃ Fin t :=
  (finCongr hsize).trans (permutation slot hinj hsize)

@[simp] theorem active_slot (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) (i : Fin s) : placement slot hinj hsize (Fin.castAdd u i) = slot i :=
  permutation_apply slot hinj hsize i

theorem active_bank {a : ℕ} (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) (v : Tapes t a) :
    Placement.active (placement slot hinj hsize) v = ⟨fun i => v.head (slot i),fun i => v.tape (slot i)⟩ := by
  simp [Placement.active]

end IntegerMultBounds.Machine.InjectivePlacement
