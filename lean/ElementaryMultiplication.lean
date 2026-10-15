import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Bitwise

/-!
# The elementary additive-Fourier proof for the middle bit of multiplication

This follows the proof in the paper appendix.  The half-period sign function
is expanded in additive characters modulo `2^N`; its Fourier coefficients
have harmonic `l¹` norm, while every phase matrix belonging to a nonzero
coefficient is a rescaled Fourier matrix.
-/

open scoped BigOperators ComplexConjugate
open Complex ZMod AddChar

noncomputable section

namespace ElementaryMultiplication

/-- The sign of the upper half of `ZMod (2^N)`. -/
def halfSign (N : ℕ) (z : ZMod (2 ^ N)) : ℝ :=
  if z.val < 2 ^ (N - 1) then 1 else -1

/-- The sign matrix for the lower middle bit of an `N`-by-`N` product. -/
def productSign (N : ℕ) (x y : ZMod (2 ^ N)) : ℝ :=
  halfSign N (x * y)

/-- The unnormalized additive Fourier coefficient of `halfSign`. -/
def signDFT (N : ℕ) (a : ZMod (2 ^ N)) : ℂ :=
  𝓕 (fun z => (halfSign N z : ℂ)) a

/-- The normalized coefficient in the additive Fourier expansion. -/
def signCoeff (N : ℕ) (a : ZMod (2 ^ N)) : ℂ :=
  ((2 ^ N : ℕ) : ℂ)⁻¹ * signDFT N a

lemma sum_zmod_eq_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ z : ZMod q, f z) = ∑ z ∈ Finset.range q, f (z : ZMod q) := by
  calc
    (∑ z : ZMod q, f z) = ∑ i : Fin q, f (ZMod.finEquiv q i) :=
      (Equiv.sum_comp (ZMod.finEquiv q).toEquiv f).symm
    _ = ∑ i : Fin q, f (i.val : ZMod q) := by
      apply Fintype.sum_congr
      intro i
      congr 1
      apply ZMod.val_injective q
      have hval : (ZMod.finEquiv q i).val = i.val := by
        cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q => rfl
      rw [hval, ZMod.val_natCast_of_lt i.isLt]
    _ = ∑ z ∈ Finset.range q, f (z : ZMod q) :=
      Fin.sum_univ_eq_sum_range (fun z => f (z : ZMod q)) q

lemma halfSign_natCast_lower (N z : ℕ) (hN : 1 ≤ N)
    (hz : z < 2 ^ (N - 1)) :
    halfSign N (z : ZMod (2 ^ N)) = 1 := by
  have hzq : z < 2 ^ N := by
    exact hz.trans (pow_lt_pow_right₀ (by omega : 1 < 2) (by omega))
  simp [halfSign, ZMod.val_natCast_of_lt hzq, hz]

lemma halfSign_natCast_upper (N z : ℕ) (hN : 1 ≤ N)
    (hz : z < 2 ^ (N - 1)) :
    halfSign N ((2 ^ (N - 1) + z : ℕ) : ZMod (2 ^ N)) = -1 := by
  have hpow : 2 ^ N = 2 ^ (N - 1) + 2 ^ (N - 1) := by
    calc
      2 ^ N = 2 ^ (N - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (N - 1) * 2 := pow_succ _ _
      _ = 2 ^ (N - 1) + 2 ^ (N - 1) := by ring
  have hzq : 2 ^ (N - 1) + z < 2 ^ N := by rw [hpow]; omega
  rw [halfSign, ZMod.val_natCast_of_lt hzq, if_neg (by omega)]

/-- Splitting the DFT into the two half-periods gives the geometric sum in
the paper verbatim. -/
lemma signDFT_eq_geometric (N : ℕ) (hN : 1 ≤ N)
    (a : ZMod (2 ^ N)) :
    signDFT N a =
      (1 - stdAddChar
        (-(((2 ^ (N - 1) : ℕ) : ZMod (2 ^ N)) * a))) *
        ∑ z ∈ Finset.range (2 ^ (N - 1)),
          stdAddChar (-((z : ZMod (2 ^ N)) * a)) := by
  let H := 2 ^ (N - 1)
  have hq : 2 ^ N = H + H := by
    dsimp [H]
    calc
      2 ^ N = 2 ^ (N - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (N - 1) * 2 := pow_succ _ _
      _ = 2 ^ (N - 1) + 2 ^ (N - 1) := by ring
  rw [signDFT, ZMod.dft_apply, sum_zmod_eq_range]
  rw [show Finset.range (2 ^ N) = Finset.range (H + H) by rw [hq],
    Finset.sum_range_add]
  have hlower :
      (∑ z ∈ Finset.range H,
        stdAddChar (-((z : ZMod (2 ^ N)) * a)) •
          (halfSign N (z : ZMod (2 ^ N)) : ℂ)) =
      ∑ z ∈ Finset.range H,
        stdAddChar (-((z : ZMod (2 ^ N)) * a)) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [halfSign_natCast_lower N z hN (Finset.mem_range.1 hz)]
    simp
  have hupper :
      (∑ z ∈ Finset.range H,
        stdAddChar (-(((H + z : ℕ) : ZMod (2 ^ N)) * a)) •
          (halfSign N ((H + z : ℕ) : ZMod (2 ^ N)) : ℂ)) =
      -stdAddChar (-(((H : ℕ) : ZMod (2 ^ N)) * a)) *
        ∑ z ∈ Finset.range H,
          stdAddChar (-((z : ZMod (2 ^ N)) * a)) := by
    change
      (∑ z ∈ Finset.range H,
        stdAddChar (-(((H + z : ℕ) : ZMod (2 ^ N)) * a)) •
          (halfSign N ((H + z : ℕ) : ZMod (2 ^ N)) : ℂ)) =
      -stdAddChar (-(((H : ℕ) : ZMod (2 ^ N)) * a)) *
        ∑ z ∈ Finset.range H,
          stdAddChar (-((z : ZMod (2 ^ N)) * a))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [halfSign_natCast_upper N z hN (Finset.mem_range.1 hz)]
    push_cast
    simp only [smul_eq_mul]
    rw [add_mul, neg_add, map_add_eq_mul]
    ring
  rw [hlower, hupper]
  ring

lemma norm_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) :
    ‖stdAddChar a‖ = 1 := by
  rw [stdAddChar_apply]
  exact Circle.norm_coe _

lemma star_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) :
    star (stdAddChar a) = stdAddChar (-a) := by
  rw [stdAddChar_apply, stdAddChar_apply]
  rw [← starRingEnd_apply]
  calc
    (starRingEnd ℂ) (↑(toCircle a) : ℂ) =
        (↑((toCircle a)⁻¹) : ℂ) := (Circle.coe_inv_eq_conj _).symm
    _ = ↑(toCircle (-a)) :=
      congrArg Subtype.val (AddChar.map_neg_eq_inv ZMod.toCircle a).symm

lemma norm_exp_two_mul_I_sub_one (x : ℝ) :
    ‖Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1‖ =
      2 * |Real.sin x| := by
  have hsquare :
      ‖Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 =
        (2 * |Real.sin x|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [map_mul, ofReal_ofNat, ofReal_re, I_re, mul_re, ofReal_im,
      zero_mul, I_im, mul_im, mul_one, add_zero, sub_re, one_re, sub_im,
      one_im, sub_zero]
    rw [Real.sin_two_mul, Real.cos_two_mul]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, mul_one, add_zero]
    ring_nf
    rw [sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hleft := norm_nonneg
    (Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1)
  have hright : 0 ≤ 2 * |Real.sin x| := by positivity
  nlinarith [hsquare]

lemma norm_stdAddChar_natCast_sub_one_lower {q : ℕ} [NeZero q]
    (a : ℕ) (ha : 2 * a ≤ q) :
    (4 * a : ℝ) / q ≤
      ‖stdAddChar (a : ZMod q) - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  let x : ℝ := Real.pi * a / q
  have hx0 : 0 ≤ x := by positivity
  have hxpi : x ≤ Real.pi / 2 := by
    dsimp [x]
    apply (div_le_iff₀ hq).2
    have ha' : (2 : ℝ) * a ≤ q := by exact_mod_cast ha
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hx0 hxpi
  have hexp :
      stdAddChar (a : ZMod q) =
        Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) := by
    rw [show (a : ZMod q) = ((a : ℤ) : ZMod q) by norm_num,
      ZMod.stdAddChar_coe]
    dsimp [x]
    push_cast
    congr 1
    field_simp
    ring
  rw [hexp, norm_exp_two_mul_I_sub_one]
  rw [abs_of_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨hx0, hxpi.trans (by linarith [Real.pi_pos])⟩)]
  dsimp [x] at hsin ⊢
  have hsimple : (2 * a : ℝ) / q ≤
      Real.sin (Real.pi * a / q) := by
    calc
      (2 * a : ℝ) / q =
          2 / Real.pi * (Real.pi * a / q) := by
        field_simp [Real.pi_ne_zero]
        ring
      _ ≤ Real.sin (Real.pi * a / q) := hsin
  calc
    (4 * a : ℝ) / q = 2 * ((2 * a : ℝ) / q) := by ring
    _ ≤ 2 * Real.sin (Real.pi * a / q) := by gcongr

lemma geometric_sum_norm_le {q : ℕ} [NeZero q]
    (a H : ℕ) (ha0 : 1 ≤ a) (ha : 2 * a ≤ q) :
    ‖∑ n ∈ Finset.range H,
      stdAddChar ((a * n : ℕ) : ZMod q)‖ ≤
      (q : ℝ) / (2 * a) := by
  let r := stdAddChar (a : ZMod q)
  have hr : ‖r‖ = 1 := norm_stdAddChar _
  have hden : (4 * a : ℝ) / q ≤ ‖r - 1‖ :=
    norm_stdAddChar_natCast_sub_one_lower a ha
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hdenpos : 0 < ‖r - 1‖ :=
    lt_of_lt_of_le (div_pos (by positivity) hq) hden
  have hgeom :
      (∑ n ∈ Finset.range H,
        stdAddChar ((a * n : ℕ) : ZMod q)) =
        ∑ n ∈ Finset.range H, r ^ n := by
    apply Finset.sum_congr rfl
    intro n _hn
    dsimp [r]
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    simp [nsmul_eq_mul, mul_comm]
  rw [hgeom]
  have hprod := congrArg norm (geom_sum_mul r H)
  rw [norm_mul] at hprod
  have hnum : ‖r ^ H - 1‖ ≤ 2 := by
    calc
      ‖r ^ H - 1‖ ≤ ‖r ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hr]; norm_num
  have hmul :
      ‖∑ n ∈ Finset.range H, r ^ n‖ * ‖r - 1‖ ≤ 2 := by
    rw [hprod]
    exact hnum
  have hsmall :
      ‖∑ n ∈ Finset.range H, r ^ n‖ * ((4 * a : ℝ) / q) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans hmul
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)).2
  calc
    ‖∑ n ∈ Finset.range H, r ^ n‖ * (2 * a) =
        (q / 2 : ℝ) *
          (‖∑ n ∈ Finset.range H, r ^ n‖ * ((4 * a : ℝ) / q)) := by
      field_simp
      ring
    _ ≤ (q / 2 : ℝ) * 2 := by gcongr
    _ = q := by ring

lemma geometric_sum_norm_le_symmetric {q : ℕ} [NeZero q]
    (a H : ℕ) (ha0 : 1 ≤ a) (haq : a < q) :
    ‖∑ n ∈ Finset.range H,
      stdAddChar ((a * n : ℕ) : ZMod q)‖ ≤
      (q : ℝ) / (2 * min a (q - a)) := by
  by_cases ha : 2 * a ≤ q
  · rw [min_eq_left (by omega)]
    exact geometric_sum_norm_le a H ha0 ha
  · have hb0 : 1 ≤ q - a := by omega
    have hb : 2 * (q - a) ≤ q := by omega
    rw [min_eq_right (by omega)]
    have hbound := geometric_sum_norm_le (q := q) (q - a) H hb0 hb
    have harg (n : ℕ) :
        (((q - a) * n : ℕ) : ZMod q) =
          -((a * n : ℕ) : ZMod q) := by
      push_cast [Nat.cast_sub (Nat.le_of_lt haq)]
      simp
    have hsum :
        (∑ n ∈ Finset.range H,
            stdAddChar (((q - a) * n : ℕ) : ZMod q)) =
          star (∑ n ∈ Finset.range H,
            stdAddChar ((a * n : ℕ) : ZMod q)) := by
      rw [← starRingEnd_apply, map_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [harg, ← star_stdAddChar]
      exact (starRingEnd_apply _).symm
    rw [hsum, norm_star] at hbound
    exact hbound

lemma isUnit_iff_odd_val (N : ℕ) (hN : 0 < N)
    (a : ZMod (2 ^ N)) : IsUnit a ↔ Odd a.val := by
  calc
    IsUnit a ↔ IsUnit (a.val : ZMod (2 ^ N)) := by
      rw [ZMod.natCast_zmod_val]
    _ ↔ Odd a.val := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hN,
        Nat.coprime_two_right]

lemma half_mul_eq_zero_of_not_unit (N : ℕ) (hN : 1 ≤ N)
    (a : ZMod (2 ^ N)) (ha : ¬ IsUnit a) :
    ((2 ^ (N - 1) : ℕ) : ZMod (2 ^ N)) * a = 0 := by
  have hnotodd : ¬ Odd a.val := by
    rwa [isUnit_iff_odd_val N (by omega)] at ha
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hnotodd
  have hpow : 2 ^ N = 2 ^ (N - 1) * 2 := by
    calc
      2 ^ N = 2 ^ (N - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (N - 1) * 2 := pow_succ _ _
  rw [← ZMod.natCast_zmod_val a, hk]
  change ((2 ^ (N - 1) : ℕ) : ZMod (2 ^ N)) *
      ((k + k : ℕ) : ZMod (2 ^ N)) = 0
  rw [show k + k = 2 * k by omega, ← Nat.cast_mul]
  rw [show 2 ^ (N - 1) * (2 * k) = 2 ^ N * k by rw [hpow]; ring]
  simp

/-- Exactly as in the appendix, the even frequencies disappear. -/
lemma signDFT_eq_zero_of_not_unit (N : ℕ) (hN : 1 ≤ N)
    (a : ZMod (2 ^ N)) (ha : ¬ IsUnit a) : signDFT N a = 0 := by
  rw [signDFT_eq_geometric N hN]
  rw [half_mul_eq_zero_of_not_unit N hN a ha]
  simp

lemma negative_geometric_sum_norm (N : ℕ) (a : ZMod (2 ^ N)) (H : ℕ) :
    ‖∑ z ∈ Finset.range H,
        stdAddChar (-((z : ZMod (2 ^ N)) * a))‖ =
      ‖∑ z ∈ Finset.range H,
        stdAddChar ((a.val * z : ℕ) : ZMod (2 ^ N))‖ := by
  have hsum :
      (∑ z ∈ Finset.range H,
        stdAddChar (-((z : ZMod (2 ^ N)) * a))) =
      star (∑ z ∈ Finset.range H,
        stdAddChar ((a.val * z : ℕ) : ZMod (2 ^ N))) := by
    rw [← starRingEnd_apply, map_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    rw [← star_stdAddChar]
    congr 1
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    ring
  rw [hsum, norm_star]

/-- The appendix's pointwise bound `|c_a| ≤ 1/min(a,q-a)`. -/
lemma norm_signCoeff_le (N : ℕ) (hN : 1 ≤ N)
    (a : ZMod (2 ^ N)) (ha : a ≠ 0) :
    ‖signCoeff N a‖ ≤
      ((min a.val (2 ^ N - a.val) : ℕ) : ℝ)⁻¹ := by
  let q := 2 ^ N
  let H := 2 ^ (N - 1)
  have hq : (0 : ℝ) < q := by positivity
  have ha0 : 1 ≤ a.val := by
    have : a.val ≠ 0 := by simpa [ZMod.val_eq_zero] using ha
    omega
  have haq : a.val < q := ZMod.val_lt a
  have hgeom :
      ‖∑ z ∈ Finset.range H,
        stdAddChar (-((z : ZMod q) * a))‖ ≤
        (q : ℝ) / (2 * min a.val (q - a.val)) := by
    rw [negative_geometric_sum_norm N a H]
    exact geometric_sum_norm_le_symmetric a.val H ha0 haq
  have hprefactor :
      ‖1 - stdAddChar
        (-(((H : ℕ) : ZMod q) * a))‖ ≤ 2 := by
    calc
      ‖1 - stdAddChar (-(((H : ℕ) : ZMod q) * a))‖ ≤
          ‖(1 : ℂ)‖ + ‖stdAddChar (-(((H : ℕ) : ZMod q) * a))‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [norm_stdAddChar]; norm_num
  have hdft :
      ‖signDFT N a‖ ≤
        (q : ℝ) / ((min a.val (q - a.val) : ℕ) : ℝ) := by
    rw [signDFT_eq_geometric N hN, norm_mul]
    calc
      ‖1 - stdAddChar (-(((H : ℕ) : ZMod q) * a))‖ *
          ‖∑ z ∈ Finset.range H,
            stdAddChar (-((z : ZMod q) * a))‖ ≤
          2 * ((q : ℝ) /
            (2 * ((min a.val (q - a.val) : ℕ) : ℝ))) := by
        gcongr
      _ = (q : ℝ) / ((min a.val (q - a.val) : ℕ) : ℝ) := by
        ring
  rw [signCoeff, norm_mul, norm_inv, norm_natCast]
  calc
    (q : ℝ)⁻¹ * ‖signDFT N a‖ ≤
        (q : ℝ)⁻¹ *
          ((q : ℝ) / ((min a.val (q - a.val) : ℕ) : ℝ)) := by
      gcongr
    _ = ((min a.val (q - a.val) : ℕ) : ℝ)⁻¹ := by
      have hminNat : 0 < min a.val (q - a.val) := by omega
      have hmin : (0 : ℝ) < ((min a.val (q - a.val) : ℕ) : ℝ) := by
        exact_mod_cast hminNat
      field_simp

lemma sum_min_reciprocal_le (q : ℕ) :
    (∑ a ∈ Finset.Icc 1 (q - 1),
        ((min a (q - a) : ℕ) : ℝ)⁻¹) ≤
      2 * (harmonic (q - 1) : ℝ) := by
  calc
    (∑ a ∈ Finset.Icc 1 (q - 1),
        ((min a (q - a) : ℕ) : ℝ)⁻¹) ≤
        ∑ a ∈ Finset.Icc 1 (q - 1),
          ((a : ℝ)⁻¹ + ((q - a : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro a ha
      rcases Finset.mem_Icc.1 ha with ⟨ha1, haq⟩
      rw [min_def]
      split_ifs
      · exact le_add_of_nonneg_right (inv_nonneg.2 (Nat.cast_nonneg _))
      · exact le_add_of_nonneg_left (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = (harmonic (q - 1) : ℝ) + (harmonic (q - 1) : ℝ) := by
      rw [Finset.sum_add_distrib]
      have hfirst :
          (∑ a ∈ Finset.Icc 1 (q - 1), (a : ℝ)⁻¹) =
            (harmonic (q - 1) : ℝ) := by
        simpa [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
          congrArg (fun z : ℚ => (z : ℝ))
            (harmonic_eq_sum_Icc (n := q - 1)).symm
      have hsecond :
          (∑ a ∈ Finset.Icc 1 (q - 1), ((q - a : ℕ) : ℝ)⁻¹) =
            (harmonic (q - 1) : ℝ) := by
        calc
          (∑ a ∈ Finset.Icc 1 (q - 1), ((q - a : ℕ) : ℝ)⁻¹) =
              ∑ a ∈ Finset.Icc 1 (q - 1), (a : ℝ)⁻¹ := by
            symm
            refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
            · intro a ha
              simp only [Finset.mem_Icc] at ha ⊢
              omega
            · intro a ha b hb hab
              simp only [Finset.mem_Icc] at ha hb
              change q - a = q - b at hab
              have haQ : a ≤ q := ha.2.trans (Nat.sub_le q 1)
              have hbQ : b ≤ q := hb.2.trans (Nat.sub_le q 1)
              omega
            · intro b hb
              refine ⟨q - b, ?_, ?_⟩
              · simp only [Finset.mem_Icc] at hb ⊢
                omega
              · simp only [Finset.mem_Icc] at hb
                have hbQ : b ≤ q := hb.2.trans (Nat.sub_le q 1)
                change q - (q - b) = b
                omega
            · intro a ha
              simp only [Finset.mem_Icc] at ha
              have haQ : a ≤ q := ha.2.trans (Nat.sub_le q 1)
              dsimp
              congr 2
              omega
          _ = (harmonic (q - 1) : ℝ) := hfirst
      rw [hfirst, hsecond]
    _ = 2 * (harmonic (q - 1) : ℝ) := by ring

lemma sum_zmod_away_zero_eq_Icc {q : ℕ} [NeZero q] (f : ℕ → ℝ) :
    (∑ a : ZMod q, if a = 0 then 0 else f a.val) =
      ∑ k ∈ Finset.Icc 1 (q - 1), f k := by
  calc
    (∑ a : ZMod q, if a = 0 then 0 else f a.val) =
        ∑ i : Fin q,
          if (ZMod.finEquiv q i : ZMod q) = 0 then 0
          else f (ZMod.finEquiv q i).val := by
      exact (Equiv.sum_comp (ZMod.finEquiv q).toEquiv
        (fun a : ZMod q => if a = 0 then 0 else f a.val)).symm
    _ = ∑ i : Fin q, if i.val = 0 then 0 else f i.val := by
      apply Fintype.sum_congr
      intro i
      have hval : (ZMod.finEquiv q i).val = i.val := by
        cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q => rfl
      have hzero : (ZMod.finEquiv q i : ZMod q) = 0 ↔ i.val = 0 := by
        rw [← ZMod.val_eq_zero, hval]
      rw [hval]
      simp only [hzero]
    _ = ∑ k ∈ Finset.range q, if k = 0 then 0 else f k :=
      Fin.sum_univ_eq_sum_range (fun k => if k = 0 then 0 else f k) q
    _ = ∑ k ∈ Finset.Icc 1 (q - 1), f k := by
      calc
        (∑ k ∈ Finset.range q, if k = 0 then 0 else f k) =
            ∑ k ∈ (Finset.range q).filter (fun k => k ≠ 0), f k := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hk0 : k = 0 <;> simp [hk0]
        _ = ∑ k ∈ Finset.Icc 1 (q - 1), f k := by
          apply Finset.sum_congr
          · ext k
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
            omega
          · intro k hk
            rfl

/-- The normalized additive coefficients have the `O(N)` `l¹` norm used in
the appendix.  The harmless constant `3` avoids special-casing tiny `N`. -/
theorem sum_norm_signCoeff_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ a : ZMod (2 ^ N), ‖signCoeff N a‖) ≤ 3 * N := by
  let q := 2 ^ N
  have hpoint (a : ZMod q) :
      ‖signCoeff N a‖ ≤
        if a = 0 then 0
        else ((min a.val (q - a.val) : ℕ) : ℝ)⁻¹ := by
    by_cases ha : a = 0
    · subst a
      rw [if_pos rfl]
      rw [signCoeff, signDFT_eq_geometric N (by omega)]
      simp
    · rw [if_neg ha]
      exact norm_signCoeff_le N (by omega) a ha
  calc
    (∑ a : ZMod q, ‖signCoeff N a‖) ≤
        ∑ a : ZMod q, if a = 0 then 0
          else ((min a.val (q - a.val) : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro a _ha
      exact hpoint a
    _ = ∑ k ∈ Finset.Icc 1 (q - 1),
          ((min k (q - k) : ℕ) : ℝ)⁻¹ := by
      exact sum_zmod_away_zero_eq_Icc (fun k =>
        ((min k (q - k) : ℕ) : ℝ)⁻¹)
    _ ≤ 2 * (harmonic (q - 1) : ℝ) := sum_min_reciprocal_le q
    _ ≤ 3 * N := by
      have hqfour : 4 ≤ q := by
        dsimp [q]
        simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hN
      have hq1 : 1 ≤ q - 1 := by omega
      have hharm : (harmonic (q - 1) : ℝ) ≤
          1 + Real.log ((q - 1 : ℕ) : ℝ) :=
        harmonic_le_one_add_log (q - 1)
      have hlogmono : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hq1
        · exact_mod_cast Nat.sub_le q 1
      have hlogq : Real.log (q : ℝ) = (N : ℝ) * Real.log 2 := by
        dsimp [q]
        norm_num [Nat.cast_pow, Real.log_pow]
      have hlogtwo : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      calc
        2 * (harmonic (q - 1) : ℝ) ≤
            2 * (1 + Real.log ((q - 1 : ℕ) : ℝ)) := by gcongr
        _ ≤ 2 * (1 + Real.log (q : ℝ)) := by gcongr
        _ = 2 * (1 + (N : ℝ) * Real.log 2) := by rw [hlogq]
        _ ≤ 3 * N := by
          have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith

/-! ## The phase matrices are rescaled Fourier matrices -/

lemma stdAddChar_orthogonality {q : ℕ} [NeZero q] (i j : ZMod q) :
    (∑ k : ZMod q,
      star (stdAddChar (-(i * k))) * stdAddChar (-(j * k))) =
      if i = j then (q : ℂ) else 0 := by
  simp_rw [star_stdAddChar, ← map_add_eq_mul]
  have h := AddChar.sum_mulShift (ψ := stdAddChar (N := q)) (i - j)
    (ZMod.isPrimitive_stdAddChar q)
  rw [show (∑ k : ZMod q, stdAddChar (-(-(i * k)) + -(j * k))) =
      ∑ k : ZMod q, stdAddChar (k * (i - j)) by
    apply Fintype.sum_congr
    intro k
    congr 1
    ring]
  simpa [sub_eq_zero] using h

/-- Finite Parseval for the unnormalized DFT. -/
lemma dft_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ k, Complex.normSq (𝓕 f k) =
      (q : ℝ) * ∑ z, Complex.normSq (f z) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp only [ZMod.dft_apply, map_sum, map_mul, starRingEnd_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [smul_eq_mul, star_mul, star_stdAddChar]
  calc
    (∑ y, ∑ k, ∑ i,
        star (f i) * stdAddChar (-(-(i * k))) *
          (stdAddChar (-(y * k)) * f y)) =
        ∑ y, ∑ i, (star (f i) * f y) *
          ∑ k, stdAddChar (-(-(i * k))) * stdAddChar (-(y * k)) := by
      apply Fintype.sum_congr
      intro y
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro i
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro k
      ring
    _ = ∑ y, ∑ i, (star (f i) * f y) *
          (if i = y then (q : ℂ) else 0) := by
      apply Fintype.sum_congr
      intro y
      apply Fintype.sum_congr
      intro i
      rw [← stdAddChar_orthogonality i y]
      simp_rw [star_stdAddChar]
    _ = ∑ i, (q : ℂ) * (star (f i) * f i) := by
      simp
      apply Fintype.sum_congr
      intro i
      ring

def phaseApply (N : ℕ) (a : ZMod (2 ^ N))
    (v : ZMod (2 ^ N) → ℂ) (x : ZMod (2 ^ N)) : ℂ :=
  ∑ y, stdAddChar (a * x * y) * v y

def phaseBilinear (N : ℕ) (a : ZMod (2 ^ N))
    (u v : ZMod (2 ^ N) → ℂ) : ℂ :=
  ∑ x, u x * phaseApply N a v x

lemma sum_unit_mul {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (f : ZMod q → ℝ) :
    (∑ x, f (a.val * x)) = ∑ x, f x := by
  exact Fintype.sum_equiv a.mulLeft _ _ (fun _ => rfl)

lemma sum_neg {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ x, f (-x)) = ∑ x, f x := by
  exact Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun _ => rfl)

lemma phaseApply_eq_dft (N : ℕ) (a : ZMod (2 ^ N))
    (v : ZMod (2 ^ N) → ℂ) (x : ZMod (2 ^ N)) :
    phaseApply N a v x = 𝓕 v (-a * x) := by
  rw [phaseApply, ZMod.dft_apply]
  apply Fintype.sum_congr
  intro y
  simp only [smul_eq_mul]
  congr 2
  ring

lemma phaseApply_energy_unit (N : ℕ) (a : (ZMod (2 ^ N))ˣ)
    (v : ZMod (2 ^ N) → ℂ) :
    ∑ x, Complex.normSq (phaseApply N a.val v x) =
      ((2 ^ N : ℕ) : ℝ) * ∑ y, Complex.normSq (v y) := by
  calc
    (∑ x, Complex.normSq (phaseApply N a.val v x)) =
        ∑ x, Complex.normSq (𝓕 v (-a.val * x)) := by
      apply Fintype.sum_congr
      intro x
      rw [phaseApply_eq_dft]
    _ = ∑ x, Complex.normSq (𝓕 v (-(a.val * x))) := by
      apply Fintype.sum_congr
      intro x
      congr 2
      ring
    _ = ∑ x, Complex.normSq (𝓕 v (-x)) :=
      sum_unit_mul a (fun x => Complex.normSq (𝓕 v (-x)))
    _ = ∑ k, Complex.normSq (𝓕 v k) :=
      sum_neg (fun k => Complex.normSq (𝓕 v k))
    _ = ((2 ^ N : ℕ) : ℝ) * ∑ y, Complex.normSq (v y) :=
      dft_energy v

lemma phaseApply_energy (N : ℕ) (a : ZMod (2 ^ N))
    (ha : IsUnit a) (v : ZMod (2 ^ N) → ℂ) :
    ∑ x, Complex.normSq (phaseApply N a v x) =
      ((2 ^ N : ℕ) : ℝ) * ∑ y, Complex.normSq (v y) := by
  simpa only [ha.unit_spec] using phaseApply_energy_unit N ha.unit v

/-- For a unit frequency, the phase matrix `e_q(a x y)` has norm `√q`. -/
lemma norm_phaseBilinear_le (N : ℕ) (a : ZMod (2 ^ N))
    (ha : IsUnit a) (u v : ZMod (2 ^ N) → ℂ) :
    ‖phaseBilinear N a u v‖ ≤
      Real.sqrt ((2 ^ N : ℕ) : ℝ) *
        Real.sqrt (∑ x, Complex.normSq (u x)) *
        Real.sqrt (∑ y, Complex.normSq (v y)) := by
  have henergy := phaseApply_energy N a ha v
  calc
    ‖phaseBilinear N a u v‖ =
        ‖∑ x, u x * phaseApply N a v x‖ := rfl
    _ ≤ ∑ x, ‖u x * phaseApply N a v x‖ := norm_sum_le _ _
    _ = ∑ x, ‖u x‖ * ‖phaseApply N a v x‖ := by
      apply Fintype.sum_congr
      intro x
      rw [norm_mul]
    _ ≤ Real.sqrt (∑ x, ‖u x‖ ^ 2) *
        Real.sqrt (∑ x, ‖phaseApply N a v x‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun x => ‖u x‖) (fun x => ‖phaseApply N a v x‖)
    _ = Real.sqrt (∑ x, Complex.normSq (u x)) *
        Real.sqrt (((2 ^ N : ℕ) : ℝ) *
          ∑ y, Complex.normSq (v y)) := by
      simp_rw [← Complex.normSq_eq_norm_sq]
      rw [henergy]
    _ = Real.sqrt ((2 ^ N : ℕ) : ℝ) *
        Real.sqrt (∑ x, Complex.normSq (u x)) *
        Real.sqrt (∑ y, Complex.normSq (v y)) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 ^ N : ℕ))]
      ring

/-! ## Fourier expansion of the multiplication matrix -/

lemma halfSign_fourier_expansion (N : ℕ) (z : ZMod (2 ^ N)) :
    (halfSign N z : ℂ) =
      ∑ a : ZMod (2 ^ N), signCoeff N a * stdAddChar (a * z) := by
  have hinv := congrFun
    ((ZMod.dft (N := 2 ^ N) (E := ℂ)).symm_apply_apply
      (fun z => (halfSign N z : ℂ))) z
  rw [ZMod.invDFT_apply] at hinv
  rw [← hinv]
  simp only [smul_eq_mul, signCoeff, signDFT, Finset.mul_sum]
  apply Fintype.sum_congr
  intro a
  ring

def multiplicationBilinear (N : ℕ)
    (u v : ZMod (2 ^ N) → ℂ) : ℂ :=
  ∑ x, ∑ y, u x * (productSign N x y : ℂ) * v y

lemma multiplicationBilinear_eq_sum_phase (N : ℕ)
    (u v : ZMod (2 ^ N) → ℂ) :
    multiplicationBilinear N u v =
      ∑ a : ZMod (2 ^ N), signCoeff N a * phaseBilinear N a u v := by
  calc
    multiplicationBilinear N u v =
        ∑ x, ∑ y, ∑ a : ZMod (2 ^ N),
          u x * (signCoeff N a * stdAddChar (a * (x * y))) * v y := by
      simp only [multiplicationBilinear, productSign,
        halfSign_fourier_expansion]
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro y
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ x, ∑ a : ZMod (2 ^ N), ∑ y,
          u x * (signCoeff N a * stdAddChar (a * (x * y))) * v y := by
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ a : ZMod (2 ^ N), ∑ x, ∑ y,
          u x * (signCoeff N a * stdAddChar (a * (x * y))) * v y := by
      rw [Finset.sum_comm]
    _ = ∑ a : ZMod (2 ^ N), signCoeff N a * phaseBilinear N a u v := by
      apply Fintype.sum_congr
      intro a
      simp only [phaseBilinear, phaseApply]
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      calc
        (∑ y, u x * (signCoeff N a * stdAddChar (a * (x * y))) * v y) =
            ∑ y, signCoeff N a *
              (u x * (stdAddChar (a * x * y) * v y)) := by
          apply Fintype.sum_congr
          intro y
          ring
        _ = signCoeff N a *
            ∑ y, u x * (stdAddChar (a * x * y) * v y) :=
          (Finset.mul_sum Finset.univ
            (fun y => u x * (stdAddChar (a * x * y) * v y))
            (signCoeff N a)).symm
        _ = signCoeff N a *
            (u x * ∑ y, stdAddChar (a * x * y) * v y) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]

/-- The paper's elementary operator-norm estimate
`||A_N|| ≤ 3 N sqrt(2^N)`. -/
theorem multiplication_spectral_bound (N : ℕ) (hN : 2 ≤ N)
    (u v : ZMod (2 ^ N) → ℂ) :
    ‖multiplicationBilinear N u v‖ ≤
      3 * N * Real.sqrt ((2 ^ N : ℕ) : ℝ) *
        Real.sqrt (∑ x, Complex.normSq (u x)) *
        Real.sqrt (∑ y, Complex.normSq (v y)) := by
  let K := Real.sqrt ((2 ^ N : ℕ) : ℝ) *
    Real.sqrt (∑ x, Complex.normSq (u x)) *
    Real.sqrt (∑ y, Complex.normSq (v y))
  have hterm (a : ZMod (2 ^ N)) :
      ‖signCoeff N a * phaseBilinear N a u v‖ ≤
        ‖signCoeff N a‖ * K := by
    rw [norm_mul]
    by_cases ha : IsUnit a
    · exact mul_le_mul_of_nonneg_left
        (norm_phaseBilinear_le N a ha u v) (norm_nonneg _)
    · rw [signCoeff, signDFT_eq_zero_of_not_unit N (by omega) a ha]
      simp
  rw [multiplicationBilinear_eq_sum_phase]
  calc
    ‖∑ a : ZMod (2 ^ N), signCoeff N a * phaseBilinear N a u v‖ ≤
        ∑ a : ZMod (2 ^ N),
          ‖signCoeff N a * phaseBilinear N a u v‖ := norm_sum_le _ _
    _ ≤ ∑ a : ZMod (2 ^ N), ‖signCoeff N a‖ * K := by
      apply Finset.sum_le_sum
      intro a _ha
      exact hterm a
    _ = (∑ a : ZMod (2 ^ N), ‖signCoeff N a‖) * K := by
      rw [Finset.sum_mul]
    _ ≤ (3 * N) * K := by
      gcongr
      exact sum_norm_signCoeff_le N hN
    _ = 3 * N * Real.sqrt ((2 ^ N : ℕ) : ℝ) *
        Real.sqrt (∑ x, Complex.normSq (u x)) *
        Real.sqrt (∑ y, Complex.normSq (v y)) := by
      dsimp [K]
      ring

/-! ## Walsh coefficients and low-degree Fourier mass -/

/-- A Walsh character on the `N` binary digits of a residue modulo `2^N`. -/
def walsh {N : ℕ} (R : Finset (Fin N)) (x : ZMod (2 ^ N)) : ℂ :=
  ∏ i ∈ R, if Nat.testBit x.val i.val then -1 else 1

abbrev Frequency (N : ℕ) := Finset (Fin N) × Finset (Fin N)

def degree {N : ℕ} (w : Frequency N) : ℕ := w.1.card + w.2.card

/-- The normalized Walsh--Fourier coefficient of the middle product bit. -/
def fourierCoeff (N : ℕ) (w : Frequency N) : ℂ :=
  multiplicationBilinear N (walsh w.1) (walsh w.2) /
    (((2 ^ N : ℕ) : ℂ) ^ 2)

/-- Fourier weight through total degree `t`. -/
def lowDegreeWeight (N t : ℕ) : ℝ :=
  ∑ w ∈ (Finset.univ.filter fun w : Frequency N => degree w ≤ t),
    Complex.normSq (fourierCoeff N w)

@[simp] lemma normSq_walsh {N : ℕ} (R : Finset (Fin N))
    (x : ZMod (2 ^ N)) : Complex.normSq (walsh R x) = 1 := by
  classical
  induction R using Finset.induction_on with
  | empty => simp [walsh]
  | @insert i R hi ih =>
      rw [walsh, Finset.prod_insert hi, Complex.normSq_mul]
      change Complex.normSq
        (if Nat.testBit x.val i.val then (-1 : ℂ) else 1) *
          Complex.normSq (walsh R x) = 1
      rw [ih]
      by_cases hbit : Nat.testBit x.val i.val <;> simp [hbit]

lemma sum_normSq_walsh {N : ℕ} (R : Finset (Fin N)) :
    ∑ x : ZMod (2 ^ N), Complex.normSq (walsh R x) = (2 ^ N : ℕ) := by
  simp

/-- Equation (app-mult-each-fourier), with the harmless constant `3`. -/
theorem norm_fourierCoeff_le (N : ℕ) (hN : 2 ≤ N) (w : Frequency N) :
    ‖fourierCoeff N w‖ ≤
      3 * N / Real.sqrt ((2 ^ N : ℕ) : ℝ) := by
  let q : ℝ := (2 ^ N : ℕ)
  have hq : 0 < q := by positivity
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hs := multiplication_spectral_bound N hN (walsh w.1) (walsh w.2)
  rw [sum_normSq_walsh, sum_normSq_walsh] at hs
  rw [fourierCoeff, norm_div, norm_pow, norm_natCast]
  change ‖multiplicationBilinear N (walsh w.1) (walsh w.2)‖ / q ^ 2 ≤ _
  calc
    ‖multiplicationBilinear N (walsh w.1) (walsh w.2)‖ /
          q ^ 2 ≤
        (3 * N * Real.sqrt q * Real.sqrt q * Real.sqrt q) / q ^ 2 := by
      gcongr
    _ = 3 * N / Real.sqrt q := by
      have hsquare : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
      field_simp [hsqrt.ne', hq.ne']
      have hfour : Real.sqrt q ^ 4 = q ^ 2 := by
        calc
          Real.sqrt q ^ 4 = (Real.sqrt q ^ 2) ^ 2 := by ring
          _ = q ^ 2 := by rw [hsquare]
      calc
        3 * (N : ℝ) * Real.sqrt q * Real.sqrt q * Real.sqrt q * Real.sqrt q =
            3 * (N : ℝ) * Real.sqrt q ^ 4 := by ring
        _ = 3 * (N : ℝ) * q ^ 2 := by rw [hfour]

/-- Pairing two frequency sets is the same as a frequency set on the
disjoint union of the two operands' coordinates. -/
def frequencyLEEquiv (N t : ℕ) :
    {w : Frequency N // degree w ≤ t} ≃
      {s : Finset (Fin N ⊕ Fin N) // s.card ≤ t} where
  toFun w := ⟨Finset.sumEquiv.symm w.1, by simpa [degree] using w.2⟩
  invFun s := ⟨Finset.sumEquiv s.1, by
    simpa [degree, Finset.card_toLeft_add_card_toRight] using s.2⟩
  left_inv w := by
    apply Subtype.ext
    exact Finset.sumEquiv.apply_symm_apply w.1
  right_inv s := by
    apply Subtype.ext
    exact Finset.sumEquiv.symm_apply_apply s.1

def finsetCardLEEquiv (α : Type*) [Fintype α] [DecidableEq α] (t : ℕ) :
    {s : Finset α // s.card ≤ t} ≃
      Σ k : Fin (t + 1), {s : Finset α // s.card = k.val} where
  toFun s := ⟨⟨s.1.card, Nat.lt_succ_iff.2 s.2⟩, s.1, rfl⟩
  invFun p := ⟨p.2.1, p.2.2.trans_le (Nat.le_of_lt_succ p.1.2)⟩
  left_inv s := by simp
  right_inv p := by
    rcases p with ⟨⟨k, hk⟩, ⟨s, hs⟩⟩
    dsimp
    change s.card = k at hs
    cases hs
    rfl

theorem lowFrequency_card_eq_choose_sum (N t : ℕ) :
    (Finset.univ.filter fun w : Frequency N => degree w ≤ t).card =
      ∑ k : Fin (t + 1), Nat.choose (2 * N) k.val := by
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {w : Frequency N // degree w ≤ t} =
        Fintype.card {s : Finset (Fin N ⊕ Fin N) // s.card ≤ t} :=
      Fintype.card_congr (frequencyLEEquiv N t)
    _ = Fintype.card
          (Σ k : Fin (t + 1),
            {s : Finset (Fin N ⊕ Fin N) // s.card = k.val}) :=
      Fintype.card_congr (finsetCardLEEquiv (Fin N ⊕ Fin N) t)
    _ = ∑ k : Fin (t + 1), Nat.choose (2 * N) k.val := by
      simp [Fintype.card_sigma, Fintype.card_finset_len,
        Fintype.card_sum, two_mul]

lemma choose_lower_tail_mul_pow_le (n t : ℕ) (ht : t ≤ n) :
    ((∑ k ∈ Finset.range (t + 1), Nat.choose n k : ℕ) : ℝ) *
        (1 / 16 : ℝ) ^ t ≤ (17 / 16 : ℝ) ^ n := by
  rw [Nat.cast_sum, Finset.sum_mul]
  calc
    ∑ k ∈ Finset.range (t + 1), (Nat.choose n k : ℝ) * (1 / 16 : ℝ) ^ t
        ≤ ∑ k ∈ Finset.range (t + 1),
            (Nat.choose n k : ℝ) * (1 / 16 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_of_le_one
      · norm_num
      · norm_num
      · exact Nat.le_of_lt_succ (Finset.mem_range.1 hk)
    _ ≤ ∑ k ∈ Finset.range (n + 1),
            (Nat.choose n k : ℝ) * (1 / 16 : ℝ) ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right ht 1)
      · intro k _hk _
        positivity
    _ = (17 / 16 : ℝ) ^ n := by
      have hbinom := (add_pow (1 / 16 : ℝ) 1 n).symm
      norm_num at hbinom ⊢
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbinom

lemma weighted_tail_base_le (N : ℕ) :
    (16 : ℝ) ^ (N / 8) * (289 / 512 : ℝ) ^ N ≤
      (4 / 5 : ℝ) ^ N := by
  let m := N / 8
  let r := N % 8
  have hN : N = 8 * m + r := by
    dsimp [m, r]
    omega
  have hdiv : N / 8 = m := rfl
  rw [hdiv, hN, pow_add, pow_add, pow_mul, pow_mul]
  calc
    (16 : ℝ) ^ m * (((289 / 512 : ℝ) ^ 8) ^ m * (289 / 512 : ℝ) ^ r) =
        ((16 : ℝ) * (289 / 512 : ℝ) ^ 8) ^ m *
          (289 / 512 : ℝ) ^ r := by rw [mul_pow]; ring
    _ ≤ (((4 / 5 : ℝ) ^ 8) ^ m) * (4 / 5 : ℝ) ^ r := by
      have hblock :
          (16 : ℝ) * (289 / 512 : ℝ) ^ 8 ≤ (4 / 5 : ℝ) ^ 8 := by
        norm_num
      have hrest : (289 / 512 : ℝ) ^ r ≤ (4 / 5 : ℝ) ^ r := by
        exact pow_le_pow_left₀ (by positivity) (by norm_num) r
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hblock m)
        hrest (by positivity) (by positivity)

/-- A concrete substitute for the appendix's entropy count. -/
theorem lowFrequency_card_degree_eighth_le (N : ℕ) :
    (((Finset.univ.filter fun w : Frequency N => degree w ≤ N / 8).card : ℕ) : ℝ)
      ≤ (4 / 5 : ℝ) ^ N * ((2 ^ N : ℕ) : ℝ) := by
  rw [lowFrequency_card_eq_choose_sum, Fin.sum_univ_eq_sum_range]
  have htail := choose_lower_tail_mul_pow_le (2 * N) (N / 8) (by omega)
  have hpow : (0 : ℝ) < (1 / 16 : ℝ) ^ (N / 8) := by positivity
  have hrat :
      (17 / 16 : ℝ) ^ (2 * N) =
        (289 / 512 : ℝ) ^ N * ((2 ^ N : ℕ) : ℝ) := by
    rw [pow_mul]
    norm_num [Nat.cast_pow]
    rw [← mul_pow]
    norm_num
  have hsum :
      ((∑ k ∈ Finset.range (N / 8 + 1), Nat.choose (2 * N) k : ℕ) : ℝ)
        ≤ (16 : ℝ) ^ (N / 8) * (17 / 16 : ℝ) ^ (2 * N) := by
    have hdiv := (le_div_iff₀ hpow).2 htail
    calc
      ((∑ k ∈ Finset.range (N / 8 + 1), Nat.choose (2 * N) k : ℕ) : ℝ)
          ≤ (17 / 16 : ℝ) ^ (2 * N) / (1 / 16 : ℝ) ^ (N / 8) := hdiv
      _ = (16 : ℝ) ^ (N / 8) * (17 / 16 : ℝ) ^ (2 * N) := by
        field_simp
        ring
  calc
    ((∑ k ∈ Finset.range (N / 8 + 1), Nat.choose (2 * N) k : ℕ) : ℝ)
        ≤ (16 : ℝ) ^ (N / 8) * (17 / 16 : ℝ) ^ (2 * N) := hsum
    _ = ((16 : ℝ) ^ (N / 8) * (289 / 512 : ℝ) ^ N) *
          ((2 ^ N : ℕ) : ℝ) := by rw [hrat]; ring
    _ ≤ (4 / 5 : ℝ) ^ N * ((2 ^ N : ℕ) : ℝ) := by
      gcongr
      exact weighted_tail_base_le N

lemma lowDegreeWeight_le_card_mul_sq {N t : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hcoeff : ∀ w : Frequency N, ‖fourierCoeff N w‖ ≤ B) :
    lowDegreeWeight N t ≤
      (((Finset.univ.filter fun w : Frequency N => degree w ≤ t).card : ℕ) : ℝ) *
        B ^ 2 := by
  classical
  unfold lowDegreeWeight
  calc
    (∑ w ∈ (Finset.univ.filter fun w : Frequency N => degree w ≤ t),
        Complex.normSq (fourierCoeff N w)) ≤
        ∑ _w ∈ (Finset.univ.filter fun w : Frequency N => degree w ≤ t),
          B ^ 2 := by
      apply Finset.sum_le_sum
      intro w _hw
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hcoeff w)
    _ = (((Finset.univ.filter fun w : Frequency N => degree w ≤ t).card : ℕ) : ℝ) *
          B ^ 2 := by simp

/-- The explicit finite-width estimate obtained by squaring the pointwise
coefficient bound and summing over low frequencies. -/
theorem middle_bit_lowDegreeWeight_bound (N : ℕ) (hN : 2 ≤ N) :
    lowDegreeWeight N (N / 8) ≤
      9 * (N : ℝ) ^ 2 * (4 / 5 : ℝ) ^ N := by
  let q : ℝ := (2 ^ N : ℕ)
  have hq : 0 < q := by positivity
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  calc
    lowDegreeWeight N (N / 8) ≤
        (((Finset.univ.filter fun w : Frequency N => degree w ≤ N / 8).card : ℕ) : ℝ) *
          (3 * N / Real.sqrt q) ^ 2 :=
      lowDegreeWeight_le_card_mul_sq (by positivity) (norm_fourierCoeff_le N hN)
    _ ≤ ((4 / 5 : ℝ) ^ N * q) *
          (3 * N / Real.sqrt q) ^ 2 := by
      gcongr
      exact lowFrequency_card_degree_eighth_le N
    _ = 9 * (N : ℝ) ^ 2 * (4 / 5 : ℝ) ^ N := by
      rw [show q = Real.sqrt q * Real.sqrt q by
        symm
        exact Real.mul_self_sqrt hq.le]
      field_simp [hsqrt.ne']
      ring

/-- A number below `2^(n+1)` has its `n`th bit clear exactly when it lies in
the lower half. -/
lemma testBit_eq_false_iff_lt_pow {n z : ℕ} (hz : z < 2 ^ (n + 1)) :
    Nat.testBit z n = false ↔ z < 2 ^ n := by
  constructor
  · intro hb
    apply Nat.lt_of_testBit n hb (by simp)
    intro j hj
    have hzj : z < 2 ^ j :=
      hz.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))
    rw [Nat.testBit_eq_false_of_lt hzj]
    exact (Nat.testBit_eq_false_of_lt
      (pow_lt_pow_right₀ (by omega : 1 < 2) hj)).symm
  · exact Nat.testBit_eq_false_of_lt

lemma halfSign_eq_middle_bit (n : ℕ) (z : ZMod (2 ^ (n + 1))) :
    halfSign (n + 1) z =
      if Nat.testBit z.val n then -1 else 1 := by
  have hzq : z.val < 2 ^ (n + 1) := ZMod.val_lt z
  have hclear := testBit_eq_false_iff_lt_pow hzq
  by_cases hz : z.val < 2 ^ n
  · have hb : Nat.testBit z.val n = false := hclear.2 hz
    simp [halfSign, hz, hb]
  · have hb : Nat.testBit z.val n = true := by
      cases hbit : Nat.testBit z.val n with
      | false => exact (hz (hclear.1 hbit)).elim
      | true => rfl
    simp [halfSign, hz, hb]

/-- Thus `productSign N` is literally `(-1)` to the lower middle product
bit, numbered from zero as in the appendix. -/
theorem productSign_eq_middle_bit (N : ℕ) (hN : 1 ≤ N)
    (x y : ZMod (2 ^ N)) :
    productSign N x y =
      if Nat.testBit (x.val * y.val) (N - 1) then -1 else 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    exact ⟨N - 1, by omega⟩
  rw [productSign, halfSign_eq_middle_bit, ZMod.val_mul]
  have hb := Nat.testBit_mod_two_pow (x.val * y.val) (n + 1) n
  simp only [Nat.lt_succ_iff, le_refl, decide_true, Bool.true_and] at hb
  rw [hb]
  simp

/-- A fixed polynomial prefactor can be absorbed into any strictly weaker
geometric rate. -/
theorem polynomial_times_geometric_eventually_le
    {C a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : 0 ≤ b) :
    ∀ᶠ N : ℕ in Filter.atTop,
      C ^ 2 * (N : ℝ) ^ 2 * a ^ N ≤ b ^ N := by
  have habs : ‖a‖ < b := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ha] using hab
  have hsmall :=
    isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) 2 habs
  have hscaled := hsmall.const_mul_left (C ^ 2)
  filter_upwards [hscaled.bound (by norm_num : (0 : ℝ) < 1)] with N hN
  have hleft : 0 ≤ C ^ 2 * ((N : ℝ) ^ 2 * a ^ N) := by positivity
  have hright : 0 ≤ b ^ N := pow_nonneg hb _
  simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright,
    abs_of_nonneg ha, abs_of_nonneg hb, mul_assoc] using hN

/-- The appendix theorem in its asymptotic form: at the linear cutoff `N/8`,
the middle product bit has exponentially small low-degree Fourier mass. -/
theorem middle_bit_fourier_resilience :
    ∀ᶠ N : ℕ in Filter.atTop,
      lowDegreeWeight N (N / 8) ≤ (9 / 10 : ℝ) ^ N := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ),
      polynomial_times_geometric_eventually_le
        (C := (3 : ℝ)) (a := 4 / 5) (b := 9 / 10)
        (by norm_num) (by norm_num) (by norm_num)] with N hN hpoly
  exact (middle_bit_lowDegreeWeight_bound N hN).trans (by
    norm_num at hpoly ⊢
    simpa [mul_assoc] using hpoly)

end ElementaryMultiplication
