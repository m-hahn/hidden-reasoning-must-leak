import PRGRestriction

/-!
# Security under polynomially invertible reindexing

Rounded sublinear seeds need not be injective as a function of input length.
For each seed length we choose the most distinguishing circuit in its finite
fiber. This is permitted nonuniform circuit advice, and its size is bounded
by the polynomial inverse. No security of the reindexed family is assumed.
-/

noncomputable section
namespace PRGReindex
open TransformerAC0 Encryption

def family {seedLengths outputLengths : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths) (index : ℕ → ℕ) :
    NC0GeneratorFamily (fun n => seedLengths (index n)) (fun n => outputLengths (index n)) where
  locality := generator.locality
  generator n := generator.generator (index n)

def candidate {outputLengths : ℕ → ℕ} {index : ℕ → ℕ}
    (monitor : PolynomialMonitorFamily (fun n => outputLengths (index n))) (m n : ℕ) :
    Circuit (outputLengths m) 1 :=
  if h : index n = m then
    Circuit.reinput (Fin.cast (congrArg outputLengths h)) (monitor.circuit n)
  else Circuit.const (outputLengths m) false

theorem candidate_size {outputLengths : ℕ → ℕ} {index : ℕ → ℕ}
    (monitor : PolynomialMonitorFamily (fun n => outputLengths (index n))) (m n degree : ℕ)
    (bounded : n + 1 ≤ (m + 1) ^ degree) :
    (candidate monitor m n).gateCount ≤ (monitor.coefficient + 1) * (m + 1) ^ (degree * monitor.exponent) := by
  unfold candidate
  split_ifs with h
  · rw [Circuit.gateCount_reinput]
    calc
      _ ≤ monitor.coefficient * (n + 1) ^ monitor.exponent := monitor.size_le n
      _ ≤ monitor.coefficient * ((m + 1) ^ degree) ^ monitor.exponent :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bounded _)
      _ ≤ _ := by rw [← pow_mul]; exact Nat.mul_le_mul_right _ (by omega)
  · simp only [Circuit.const, Bool.false_eq_true, ↓reduceIte, Circuit.gateCount, Nat.zero_add]
    have hp : 1 ≤ (m + 1) ^ (degree * monitor.exponent) := Nat.one_le_pow _ _ (by omega)
    nlinarith

def candidateAdvantage {seedLengths outputLengths : ℕ → ℕ} {index : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths)
    (monitor : PolynomialMonitorFamily (fun n => outputLengths (index n))) (m n : ℕ) : ℝ :=
  distinguishingAdvantage (generator.generator m).generate (fun word => Circuit.eval (candidate monitor m n) word 0)

theorem candidate_at {seedLengths outputLengths : ℕ → ℕ} {index : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths)
    (monitor : PolynomialMonitorFamily (fun n => outputLengths (index n))) (n : ℕ) :
    candidateAdvantage generator monitor (index n) n =
      distinguishingAdvantage ((family generator index).generator n).generate (monitor.monitor n) := by
  simp only [candidateAdvantage, candidate, dif_pos rfl, Circuit.reinput, Circuit.eval,
    Fin.cast_refl, family, PolynomialMonitorFamily.monitor]
  rfl

def bestIndex {seedLengths outputLengths : ℕ → ℕ} {index : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths)
    (monitor : PolynomialMonitorFamily (fun n => outputLengths (index n))) (degree m : ℕ) : ℕ :=
  Classical.choose (Finset.exists_max_image (Finset.range ((m + 1) ^ degree))
    (candidateAdvantage generator monitor m) (by
      exact ⟨0, Finset.mem_range.mpr (Nat.pow_pos (by omega))⟩))

theorem bestIndex_spec {seedLengths outputLengths : ℕ → ℕ} {index : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths)
    (monitor : PolynomialMonitorFamily (fun n => outputLengths (index n))) (degree m : ℕ) :
    bestIndex generator monitor degree m < (m + 1) ^ degree ∧
      ∀ n, n < (m + 1) ^ degree → candidateAdvantage generator monitor m n ≤
        candidateAdvantage generator monitor m (bestIndex generator monitor degree m) := by
  have h := Classical.choose_spec (Finset.exists_max_image (Finset.range ((m + 1) ^ degree))
    (candidateAdvantage generator monitor m) (by
      exact ⟨0, Finset.mem_range.mpr (Nat.pow_pos (by omega))⟩))
  exact ⟨Finset.mem_range.mp h.1, fun n hn => h.2 n (Finset.mem_range.mpr hn)⟩

def liftedMonitor {seedLengths outputLengths : ℕ → ℕ} {index : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths)
    (monitor : PolynomialMonitorFamily (fun n => outputLengths (index n))) (degree : ℕ) :
    PolynomialMonitorFamily outputLengths where
  circuit m := candidate monitor m (bestIndex generator monitor degree m)
  coefficient := monitor.coefficient + 1
  exponent := degree * monitor.exponent
  size_le m := candidate_size monitor m _ degree (by
    have h := (bestIndex_spec generator monitor degree m).1
    omega)

theorem negligible_reindex {error : ℕ → ℝ} (negligible : Negligible error)
    (index : ℕ → ℕ) (degree : ℕ) (inverse : ∀ n, n + 1 ≤ (index n + 1) ^ degree) :
    Negligible (fun n => error (index n)) := by
  refine ⟨fun n => negligible.1 _, ?_⟩
  intro exponent
  obtain ⟨cutoff, hcutoff⟩ := negligible.2 (degree * exponent)
  refine ⟨(cutoff + 1) ^ degree, ?_⟩
  intro n hn
  have hindex : cutoff ≤ index n := by
    by_contra h
    have hsmall : index n + 1 ≤ cutoff + 1 := by omega
    have hpow := Nat.pow_le_pow_left hsmall degree
    have hi := inverse n
    omega
  have hpow := Nat.pow_le_pow_left (inverse n) exponent
  rw [← pow_mul] at hpow
  have hreal : ((n + 1 : ℕ) : ℝ) ^ exponent ≤ ((index n + 1 : ℕ) : ℝ) ^ (degree * exponent) := by
    exact_mod_cast hpow
  exact (hcutoff (index n) hindex).trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) hreal)

/-- Ordinary seed-indexed security suffices; polynomial invertibility is
an arithmetic property of the chosen lengths, not a research assumption. -/
theorem secure {seedLengths outputLengths : ℕ → ℕ}
    (generator : NC0GeneratorFamily seedLengths outputLengths) (security : generator.IsPseudorandom)
    (index : ℕ → ℕ) (degree : ℕ) (inverse : ∀ n, n + 1 ≤ (index n + 1) ^ degree) :
    (family generator index).IsPseudorandom := by
  intro monitor
  obtain ⟨error, hnegligible, hsecurity⟩ := security (liftedMonitor generator monitor degree)
  refine ⟨fun n => error (index n), negligible_reindex hnegligible index degree inverse, ?_⟩
  intro n
  rw [← candidate_at]
  have hbest := (bestIndex_spec generator monitor degree (index n)).2 n (by have h := inverse n; omega)
  exact hbest.trans (hsecurity (index n))

end PRGReindex
