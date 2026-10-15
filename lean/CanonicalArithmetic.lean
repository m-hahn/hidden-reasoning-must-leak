import TransformerAC0
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Concrete fixed-point arithmetic

Scalars are a finite equally spaced lattice, encoded by `bits` Boolean wires.
Every operation is evaluated over the reals and rounded to the nearest lattice
point (ties upward), saturating at the endpoints.  The monotonicity of rounded
addition is proved from the explicit rounding function.  Thus the arithmetic
law used by the AC⁰ compiler is discharged for actual fixed-point arithmetic.
-/

noncomputable section

namespace CanonicalArithmetic

open TransformerAC0

def rank (bits : ℕ) : Bits bits ≃ Fin (Fintype.card (Bits bits)) := Fintype.equivFin _

def scale (fractionBits : ℕ) : ℝ := (2 : ℝ) ^ fractionBits

theorem scale_positive (fractionBits : ℕ) : 0 < scale fractionBits := by
  unfold scale
  positivity

/-- The lower lattice endpoint is `-offset / scale`. -/
def rankValue (fractionBits offset : ℕ) (index : Fin (Fintype.card (Bits bits))) : ℝ :=
  ((index.val : ℝ) - offset) / scale fractionBits

def value (bits fractionBits offset : ℕ) (scalar : Bits bits) : ℝ :=
  rankValue fractionBits offset (rank bits scalar)

/-- Explicit nearest-point rounding with endpoint saturation. -/
def roundIndex (bits fractionBits offset : ℕ) (x : ℝ) : Fin (Fintype.card (Bits bits)) :=
  ⟨min (Nat.floor (x * scale fractionBits + offset + 1 / 2))
      (Fintype.card (Bits bits) - 1),
    (min_le_right _ _).trans_lt (by have h := Fintype.card_pos (α := Bits bits); omega)⟩

def encode (bits fractionBits offset : ℕ) (x : ℝ) : Bits bits :=
  (rank bits).symm (roundIndex bits fractionBits offset x)

/-- Already representable lattice values are rounded exactly. -/
theorem roundIndex_rankValue (fractionBits offset : ℕ)
    (index : Fin (Fintype.card (Bits bits))) :
    roundIndex bits fractionBits offset (rankValue fractionBits offset index) = index := by
  apply Fin.ext
  unfold roundIndex rankValue
  dsimp only
  have hscale : scale fractionBits ≠ 0 := (scale_positive fractionBits).ne'
  have hcoordinate :
      ((index.val : ℝ) - offset) / scale fractionBits * scale fractionBits + offset + 1 / 2 =
        (index.val : ℝ) + 1 / 2 := by field_simp [hscale]
  rw [hcoordinate]
  have hfloor : Nat.floor ((index.val : ℝ) + 1 / 2) = index.val := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> linarith
  rw [hfloor, min_eq_left (by have h := index.isLt; omega)]

@[simp] theorem encode_value (bits fractionBits offset : ℕ) (scalar : Bits bits) :
    encode bits fractionBits offset (value bits fractionBits offset scalar) = scalar := by
  simp [encode, value, roundIndex_rankValue]

theorem roundIndex_monotone (bits fractionBits offset : ℕ) :
    Monotone (roundIndex bits fractionBits offset) := by
  intro x y hxy
  apply Fin.mk_le_mk.mpr
  apply min_le_min _ le_rfl
  apply Nat.floor_mono
  have hscale := scale_positive fractionBits
  nlinarith

theorem rankValue_monotone (fractionBits offset : ℕ) :
    Monotone (rankValue (bits := bits) fractionBits offset) := by
  intro left right hle
  unfold rankValue
  apply (div_le_div_iff_of_pos_right (scale_positive fractionBits)).mpr
  exact sub_le_sub_right (by exact_mod_cast hle : (left.val : ℝ) ≤ right.val) _

/-- The scalar encoding order agrees exactly with the numerical lattice. -/
theorem value_le_iff_rank_le (bits fractionBits offset : ℕ) (left right : Bits bits) :
    value bits fractionBits offset left ≤ value bits fractionBits offset right ↔
      rank bits left ≤ rank bits right := by
  unfold value rankValue
  rw [div_le_div_iff_of_pos_right (scale_positive fractionBits), sub_le_sub_iff_right]
  exact_mod_cast (Fin.mk_le_mk (n := Fintype.card (Bits bits)))

def first (pair : Bits (bits + bits)) : Bits bits := fun i => pair (Fin.castAdd bits i)
def second (pair : Bits (bits + bits)) : Bits bits := fun i => pair (Fin.natAdd bits i)

@[simp] theorem first_append (left right : Bits bits) : first (Fin.append left right) = left := by
  funext i
  simp [first]

@[simp] theorem second_append (left right : Bits bits) : second (Fin.append left right) = right := by
  funext i
  rw [second, Fin.append_right]

/-- Rounded fixed-point addition preserves the scalar order. -/
theorem rounded_add_monotone (bits fractionBits offset : ℕ) (term : Bits bits) :
    Monotone fun state : Fin (Fintype.card (Bits bits)) =>
      rank bits (encode bits fractionBits offset
        (value bits fractionBits offset ((rank bits).symm state) +
          value bits fractionBits offset term)) := by
  intro left right hle
  simp only [encode, Equiv.apply_symm_apply, value]
  apply roundIndex_monotone
  apply add_le_add_right
  exact rankValue_monotone fractionBits offset hle

/-- Canonical arithmetic on a signed fixed-point grid.  `bits`,
`fractionBits`, and `offset` are fixed precision parameters, independent of
the input length. -/
def arithmetic (bits fractionBits offset : ℕ) : FixedPrecisionArithmetic bits where
  zero := encode bits fractionBits offset 0
  scalarRank := rank bits
  round := id
  roundedAdd := fun pair => encode bits fractionBits offset
    (value bits fractionBits offset (first pair) + value bits fractionBits offset (second pair))
  roundedAdd_monotone := by
    intro term
    simpa only [first_append, second_append] using rounded_add_monotone bits fractionBits offset term
  multiply := fun pair => encode bits fractionBits offset
    (value bits fractionBits offset (first pair) * value bits fractionBits offset (second pair))
  exponentiate := fun scalar => encode bits fractionBits offset
    (Real.exp (value bits fractionBits offset scalar))
  divide := fun pair => encode bits fractionBits offset
    (value bits fractionBits offset (first pair) / value bits fractionBits offset (second pair))
  relu := fun scalar => encode bits fractionBits offset (max 0 (value bits fractionBits offset scalar))

/-- The compiler's derived comparison is the ordinary numerical comparison
on this fixed-point grid. -/
theorem arithmetic_lessEqual (bits fractionBits offset : ℕ) (first second : Bits bits) :
    (arithmetic bits fractionBits offset).lessEqual (Fin.append first second) =
      decide (value bits fractionBits offset first ≤ value bits fractionBits offset second) := by
  rw [FixedPrecisionArithmetic.lessEqual_append]
  simp only [value_le_iff_rank_le]
  rfl

/-- A matrix Transformer with this concrete arithmetic has a correct,
polynomial-size AC⁰ compilation with a depth bound depending only on fixed
precision and layer count. -/
theorem matrix_transformer_to_ac0
    {a : Architecture} (model : FixedPrecisionTransformer a)
    (bits fractionBits offset : ℕ) (hbits : model.scalarBits = bits)
    (harithmetic : hbits ▸ model.arithmetic = arithmetic bits fractionBits offset)
    (hv : 1 ≤ a.vocabulary) (hd : 1 ≤ a.halfWidth) (hl : 1 ≤ a.layers) :
    (∀ input, Circuit.eval model.compile input 0 = model.run input) ∧
      Circuit.depth model.compile ≤
        (a.layers + 2) * TransformerDepthCost.stage (arithmetic bits fractionBits offset) ∧
      ∃ coefficient exponent : ℕ,
        Circuit.gateCount model.compile ≤ coefficient *
          (a.parameterCount + a.contextLength + 1) ^ exponent := by
  subst bits
  refine ⟨model.compile_correct, ?_, polynomial_size_translation model hv hd hl⟩
  simpa [harithmetic] using model.compile_depth_le_fixed

end CanonicalArithmetic
