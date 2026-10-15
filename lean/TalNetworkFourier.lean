import TalNetworkCut

/-!
# Fourier tails by induction on the ranked shared network

The circuit induction uses the proved common-tree switching theorem and the
actual rank-lowering construction. No raw-bound or circuit-induction premise
is imported.
-/

noncomputable section
namespace TalNetworkFourier
open TransformerAC0 Algebraic AC0 TalGateNetwork TalMixedSwitching TalCommonTree
open TalRestriction TalRandomRestriction

def scale (size : ℕ) : ℝ := 72 * Real.logb 2 (2 * size : ℕ)
def denominator (height width size : ℕ) : ℝ := 20 * width * scale size ^ height
def prefactor (height : ℕ) : ℝ := 16 * 17 ^ height
def rawBound (height width size degree : ℕ) : ℝ :=
  prefactor height * (2 : ℝ) ^ (-(degree : ℝ) / denominator height width size)

theorem log_ge_one (size : ℕ) [NeZero size] : 1 ≤ Real.logb 2 (2 * size : ℕ) :=
  TalNumerics.logb_size_ge_one _ (by have h := NeZero.pos size; omega)

theorem scale_ge_one (size : ℕ) [NeZero size] : 1 ≤ scale size := by
  have h := log_ge_one size
  unfold scale
  linarith

theorem denominator_ge (height width size : ℕ) [NeZero size] :
    20 * (width : ℝ) ≤ denominator height width size := by
  have h : 1 ≤ scale size ^ height := one_le_pow₀ (scale_ge_one size)
  simpa only [mul_one, denominator] using mul_le_mul_of_nonneg_left h
    (show 0 ≤ 20 * (width : ℝ) by positivity)

theorem denominator_pos (height width size : ℕ) [NeZero size] [NeZero width] :
    0 < denominator height width size := by
  have hw : (0 : ℝ) < width := by exact_mod_cast NeZero.pos width
  exact lt_of_lt_of_le (by positivity) (denominator_ge height width size)

theorem prefactor_ge (height : ℕ) : 16 ≤ prefactor height := by
  have h : (1 : ℝ) ≤ 17 ^ height := one_le_pow₀ (by norm_num)
  unfold prefactor
  linarith

theorem shallow_positive (size : ℕ) [NeZero size] : 1 ≤ Nat.log 2 (2 * size) := by
  have hsize : 2 ≤ 2 * size := by have h := NeZero.pos size; omega
  have h := Nat.log_mono_right hsize (b := 2)
  have hbase : Nat.log 2 2 = 1 := Nat.log_eq_one_iff.mpr (by norm_num)
  rwa [hbase] at h

theorem retained_order (width degree : ℕ) [NeZero width] :
    ⌊(degree : ℝ) / (360 * width)⌋₊ ≤ ⌊(degree : ℝ) / (60 * width)⌋₊ := by
  have hw : (0 : ℝ) < width := by exact_mod_cast NeZero.pos width
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg degree) (by positivity) (by nlinarith)

theorem good_bound (height width size degree : ℕ) [NeZero width] [NeZero size] :
    rawBound height (Nat.log 2 (2 * size)) size
        (⌊(degree : ℝ) / (60 * width)⌋₊ - ⌊(degree : ℝ) / (360 * width)⌋₊) ≤
      2 * prefactor height * (2 : ℝ) ^ (-(degree : ℝ) / denominator (height + 1) width size) := by
  let shallow := Nat.log 2 (2 * size)
  have hs : 0 < shallow := by have h := shallow_positive size; omega
  letI : NeZero shallow := ⟨by omega⟩
  have hw : (0 : ℝ) < width := by exact_mod_cast NeZero.pos width
  have hlog : 0 ≤ Real.logb 2 (2 * size : ℕ) := (log_ge_one size).trans' (by norm_num)
  have hshallow : (shallow : ℝ) ≤ Real.logb 2 (2 * size : ℕ) := Real.natLog_le_logb _ _
  have hdenPrev : 1 ≤ denominator height shallow size := by
    have hsReal : (1 : ℝ) ≤ shallow := by exact_mod_cast hs
    have h := denominator_ge height shallow size
    linarith
  have hdenPositive := denominator_pos height shallow size
  have hdenTarget := denominator_pos (height + 1) width size
  have hscale : 0 ≤ scale size := (by have h := scale_ge_one size; linarith)
  have hpower : 0 ≤ scale size ^ height := pow_nonneg hscale _
  have hden : 72 * (width : ℝ) * denominator height shallow size ≤ denominator (height + 1) width size := by
    have h : denominator height shallow size ≤ 20 * Real.logb 2 (2 * size : ℕ) * scale size ^ height := by
      unfold denominator
      gcongr
    calc
      _ ≤ 72 * (width : ℝ) * (20 * Real.logb 2 (2 * size : ℕ) * scale size ^ height) := by gcongr
      _ = _ := by unfold denominator scale; rw [pow_succ]; ring
  have hretained := TalSwitchingNumerics.retained_degree_bound width degree
  have hratio : (degree : ℝ) / denominator (height + 1) width size ≤
      ((⌊(degree : ℝ) / (60 * width)⌋₊ - ⌊(degree : ℝ) / (360 * width)⌋₊ : ℕ) : ℝ) /
        denominator height shallow size + 1 := by
    calc
      _ ≤ (degree : ℝ) / (72 * width * denominator height shallow size) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg degree) (by positivity) hden
      _ = ((degree : ℝ) / (72 * width)) / denominator height shallow size := (div_div _ _ _).symm
      _ ≤ (((⌊(degree : ℝ) / (60 * width)⌋₊ - ⌊(degree : ℝ) / (360 * width)⌋₊ : ℕ) : ℝ) + 1) /
          denominator height shallow size :=
        (div_le_div_iff_of_pos_right hdenPositive).mpr (by linarith)
      _ ≤ _ := by
        rw [add_div]
        apply add_le_add_left
        exact (div_le_iff₀ hdenPositive).mpr (by simpa using hdenPrev)
  unfold rawBound
  calc
    _ ≤ prefactor height * (2 : ℝ) ^ (1 - (degree : ℝ) / denominator (height + 1) width size) := by
      apply mul_le_mul_of_nonneg_left _ (by have h := prefactor_ge height; linarith)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by rw [neg_div]; dsimp [shallow] at hratio; linarith)
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      rw [neg_div]
      ring

theorem bad_bound (height width size degree : ℕ) [NeZero width] [NeZero size] :
    2 * (2 : ℝ) ^ (-(degree : ℝ) / (1440 * width * Real.logb 2 (2 * size : ℕ))) ≤
      2 * (2 : ℝ) ^ (-(degree : ℝ) / denominator (height + 1) width size) := by
  have hw : (0 : ℝ) < width := by exact_mod_cast NeZero.pos width
  have hl : 0 < Real.logb 2 (2 * size : ℕ) := lt_of_lt_of_le (by norm_num) (log_ge_one size)
  have hpow : 1 ≤ scale size ^ height := one_le_pow₀ (scale_ge_one size)
  have hden : 1440 * (width : ℝ) * Real.logb 2 (2 * size : ℕ) ≤ denominator (height + 1) width size := by
    unfold denominator
    rw [pow_succ]
    calc
      _ ≤ 1440 * (width : ℝ) * Real.logb 2 (2 * size : ℕ) * scale size ^ height := by
        exact (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = _ := by unfold scale; ring
  have hratio := div_le_div_of_nonneg_left (Nat.cast_nonneg degree) (by positivity) hden
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [neg_div, neg_div]
  linarith

theorem rawBound_ge_one_of_small_degree (height width size degree : ℕ) [NeZero width] [NeZero size]
    (hsmall : (degree : ℝ) * (TalSwitchingNumerics.parameter width : ℝ) < 1) :
    1 ≤ rawBound height width size degree := by
  have hw : (0 : ℝ) < width := by exact_mod_cast NeZero.pos width
  have hp : (TalSwitchingNumerics.parameter width : ℝ) = 1 / (30 * width) := by
    simp [TalSwitchingNumerics.parameter]
  rw [hp] at hsmall
  have hk : (degree : ℝ) < 30 * width := by
    have hdiv : (degree : ℝ) / (30 * width) < 1 := by simpa only [mul_one_div] using hsmall
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 30 * width)).mp hdiv
    simpa only [one_mul] using h
  have hden := denominator_ge height width size
  have hratio : (degree : ℝ) / denominator height width size ≤ 4 :=
    (div_le_iff₀ (denominator_pos height width size)).mpr (by linarith)
  have hexp : (1 / 16 : ℝ) ≤ (2 : ℝ) ^ (-(degree : ℝ) / denominator height width size) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (-4 : ℝ) ≤ -(degree : ℝ) / denominator height width size by rw [neg_div]; linarith)
    norm_num at h
    exact h
  unfold rawBound
  calc
    1 = 16 * (1 / 16 : ℝ) := by norm_num
    _ ≤ prefactor height * (2 : ℝ) ^ (-(degree : ℝ) / denominator height width size) :=
      mul_le_mul (prefactor_ge height) hexp (by norm_num) (by have h := prefactor_ge height; linarith)

theorem expectation_bound {n m : ℕ} (family : Fin m → ScalarFunction Bool n)
    (f : Bits n → Bool) (shallow degree length : ℕ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (p : NNReal) (hp : p ≤ 1)
    (hgood : ∀ rho : PartialAssignment n, HasCommonTree family rho shallow (length - 1) →
      Tal.tailWeight (restrict (fun input => Tal.boolSign (f input)) rho) degree ≤ epsilon) :
    expectation (p : ℝ) (fun rho => Tal.tailWeight (restrict (fun input => Tal.boolSign (f input)) rho) degree) ≤
      epsilon + probability (p : ℝ) (fun rho => ¬HasCommonTree family rho shallow (length - 1)) := by
  classical
  calc
    _ ≤ expectation (p : ℝ) (fun rho => epsilon + if ¬HasCommonTree family rho shallow (length - 1) then 1 else 0) := by
      apply expectation_mono p.coe_nonneg (NNReal.coe_le_coe.mpr hp)
      intro rho
      by_cases h : HasCommonTree family rho shallow (length - 1)
      · simpa only [not_false_eq_true, not_not, if_neg (not_not.mpr h), add_zero] using hgood rho h
      · rw [if_pos h]
        have htail := tailWeight_le_one_of_sign (ScalarFunction.restrict f rho) degree
        exact htail.trans (by linarith)
    _ = _ := by
      unfold probability expectation
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_mass, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro rho _
      by_cases h : ¬HasCommonTree family rho shallow (length - 1) <;>
        simp only [if_pos h, if_neg h]

/-- Unconditional raw Fourier-tail theorem for the ranked shared-gate model. -/
theorem raw_tail_bound {n m width : ℕ} [NeZero m] [NeZero width] (height : ℕ)
    (model : Model n (Fin m) width) (hranks : ∀ index, model.rank index ≤ height)
    (reference : Reference n (Fin m)) (degree : ℕ) :
    Tal.tailWeight (fun input => Tal.boolSign (reference.eval model.functions input)) degree ≤
      rawBound height width m degree := by
  classical
  induction height generalizing width reference degree with
  | zero =>
      have hzero : ∀ index, model.rank index = 0 := fun index => Nat.eq_zero_of_le_zero (hranks index)
      obtain ⟨formula, hwidth, heval⟩ := model.reference_normalForm_of_rank_zero
        (NeZero.pos width) hzero reference
      rw [← heval]
      cases formula with
      | dnf formula =>
          simpa only [rawBound, prefactor, denominator, pow_zero, mul_one, NormalForm.eval] using
            TalSwitching.dnf_tailWeight_le formula width degree hwidth (NeZero.pos width)
      | cnf formula =>
          simpa only [rawBound, prefactor, denominator, pow_zero, mul_one, NormalForm.eval] using
            TalSwitching.cnf_tailWeight_le formula width degree hwidth (NeZero.pos width)
  | succ height ih =>
      let p := TalSwitchingNumerics.parameter width
      have hp : p < 1 := (TalMultiSwitching.small_parameter_base p
        (TalSwitchingNumerics.parameter_small width).le).1
      by_cases hsmall : (degree : ℝ) * (p : ℝ) < 1
      · exact (tailWeight_le_one_of_sign (reference.eval model.functions) degree).trans
          (rawBound_ge_one_of_small_degree (height + 1) width m degree hsmall)
      · let shallow := Nat.log 2 (2 * m)
        have hshallow : 1 ≤ shallow := shallow_positive m
        letI : NeZero shallow := ⟨by omega⟩
        let threshold := ⌊(degree : ℝ) / (60 * width)⌋₊
        let length := ⌊(degree : ℝ) / (360 * width)⌋₊
        let energy := (2 : ℝ) ^ (-(degree : ℝ) / denominator (height + 1) width m)
        let epsilon := 2 * prefactor height * energy
        have hepsilon : 0 ≤ epsilon := by
          have h := prefactor_ge height
          exact mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
        have hgood (rho : PartialAssignment n) (hcommon : HasCommonTree
            (fun index => (model.family index).eval) rho shallow (length - 1)) :
            Tal.tailWeight (restrict (fun input => Tal.boolSign (reference.eval model.functions input)) rho) threshold ≤ epsilon := by
          obtain ⟨tree, hleaf, hdepth⟩ := hcommon
          have hleafTail : tree.LeafTailBound
              (fun input => Tal.boolSign (reference.eval model.functions input)) rho (threshold - length) epsilon := by
            apply Tree.leafTailBound_of_leafBound tree (fun index => (model.family index).eval)
              shallow (threshold - length) _ epsilon _ rho hleaf
            intro current hcurrent
            let reduced := model.lower current shallow hshallow (model.bottom_depth_of_family current hcurrent)
            have hlowerRanks : ∀ index, reduced.rank index ≤ height := by
              intro index
              change model.rank index - 1 ≤ height
              have h := hranks index
              omega
            have h := ih reduced hlowerRanks (reference.restrict current) (threshold - length)
            have heval : (fun input => Tal.boolSign ((reference.restrict current).eval reduced.functions input)) =
                restrict (fun input => Tal.boolSign (reference.eval model.functions input)) current := by
              funext input
              rw [Model.lower_functions, Reference.eval_restrict]
              rfl
            rw [heval] at h
            exact h.trans (good_bound height width m degree)
          have h := tree.tailWeight_bound_of_depth_le _ rho (threshold - length) length epsilon
            (hdepth.trans (Nat.sub_le _ _)) hleafTail
          rwa [Nat.sub_add_cancel (retained_order width degree)] at h
        have hexpect := expectation_bound (fun index => (model.family index).eval)
          (reference.eval model.functions) shallow threshold length epsilon hepsilon p hp.le hgood
        have hbad := TalMixedSwitching.probability_no_commonTree_le model.family model.family_width degree
        have hbad' : probability (p : ℝ) (fun rho => ¬HasCommonTree (fun index => (model.family index).eval)
            rho shallow (length - 1)) ≤ 2 * energy :=
          hbad.trans (bad_bound height width m degree)
        have htransfer := TalSecondMoment.tailWeight_le_eight_expectation p.coe_nonneg
          (NNReal.coe_le_coe.mpr hp.le)
          (fun input => Tal.boolSign (reference.eval model.functions input)) degree (le_of_not_gt hsmall)
        have hthreshold : ⌊(degree : ℝ) * (p : ℝ) / 2⌋₊ = threshold := by
          have hpReal : (p : ℝ) = 1 / (30 * width) := by simp [p, TalSwitchingNumerics.parameter]
          rw [hpReal]
          congr 1
          dsimp [threshold]
          rw [mul_one_div, div_div]
          congr 1
          ring
        rw [hthreshold] at htransfer
        have hcoeff : 16 * prefactor height + 16 ≤ 17 * prefactor height := by
          have h := prefactor_ge height
          linarith
        calc
          _ ≤ 8 * (epsilon + 2 * energy) :=
            htransfer.trans (mul_le_mul_of_nonneg_left (hexpect.trans (add_le_add_left hbad' epsilon)) (by norm_num))
          _ = (16 * prefactor height + 16) * energy := by dsimp [epsilon]; ring
          _ ≤ (17 * prefactor height) * energy :=
            mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by norm_num) _)
          _ = rawBound (height + 1) width m degree := by
            unfold rawBound prefactor
            rw [pow_succ]
            dsimp [energy]
            ring

end TalNetworkFourier
