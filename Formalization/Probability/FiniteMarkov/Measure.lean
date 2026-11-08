import Formalization.Probability.FiniteMarkov.Path
import Formalization.Probability.FreedmanExactAssembly

/-! # Finite Markov chains: the path measure, the prefix filtration and Freedman

The discrete path measure `pathMeasure ν K n` integrates as the finite sum `pathExp`. The prefix
filtration `σ(X₀,…,X_{τ+j})` (the *pair-chain* filtration of the plan) makes increments of the form
`C_j(X₀..X_{τ+j}) · h(X_{τ+j}, X_{τ+j+1})` martingale differences when `∑_y K(u,y) h(u,y) = 0`, with
conditional second moment `C_j² ∑_y K(X_{τ+j},y) h(X_{τ+j},y)²`. The source Freedman inequality
(`freedman_source_bound`, `lem:Freedman-prelim`, `chapters/prelim.tex:1056–1076`) with `K₀ = 1`
then gives `markov_freedman`. -/

open MeasureTheory
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatisticalRL.FiniteMarkov

variable {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X]
variable {K : X → X → ℝ} {ν : X → ℝ}

theorem pathMeasure_real (hK : IsStochastic K) (hν : ∀ x, 0 ≤ ν x) {n : ℕ}
    (s : Set (Fin (n + 1) → X)) :
    (pathMeasure ν K n).real s = pathExp ν K n (s.indicator fun _ ↦ 1) := by
  have hs : ∀ x, (Measure.dirac x) s = ENNReal.ofReal (s.indicator (fun _ ↦ (1 : ℝ)) x) :=
    fun x ↦ by
      rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
      by_cases h : x ∈ s <;> simp [h]
  simp only [Measure.real, pathMeasure, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
    hs]
  rw [ENNReal.toReal_sum (fun x _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  unfold pathExp
  refine sum_congr rfl fun x _ ↦ ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pathMass_nonneg hK hν x),
    ENNReal.toReal_ofReal (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x)]

theorem pathMeasure_isProb (hK : IsStochastic K) (hν : IsProb ν) (n : ℕ) :
    IsProbabilityMeasure (pathMeasure ν K n) := by
  constructor
  have h := pathMeasure_real (n := n) hK hν.nonneg Set.univ
  simp only [Set.indicator_univ] at h
  rw [pathExp_one hK hν, Measure.real, ENNReal.toReal_eq_one_iff] at h
  exact h

theorem integral_pathMeasure (hK : IsStochastic K) (hν : IsProb ν) {n : ℕ}
    (f : (Fin (n + 1) → X) → ℝ) : ∫ x, f x ∂(pathMeasure ν K n) = pathExp ν K n f := by
  haveI := pathMeasure_isProb hK hν n
  rw [integral_fintype f Integrable.of_finite]
  unfold pathExp
  refine sum_congr rfl fun x _ ↦ ?_
  rw [pathMeasure_real hK hν.nonneg, smul_eq_mul]
  congr 1
  unfold pathExp
  simp [Set.indicator_apply]

theorem setIntegral_pathMeasure (hK : IsStochastic K) (hν : IsProb ν) {n : ℕ}
    (s : Set (Fin (n + 1) → X)) (f : (Fin (n + 1) → X) → ℝ) :
    ∫ x in s, f x ∂(pathMeasure ν K n) = pathExp ν K n (fun x ↦ s.indicator (fun _ ↦ 1) x * f x) := by
  rw [← integral_indicator (MeasurableSet.of_discrete), integral_pathMeasure hK hν]
  unfold pathExp
  refine sum_congr rfl fun x _ ↦ ?_
  by_cases h : x ∈ s <;> simp [h]

/-! ## The prefix filtration -/

/-- The prefix `(x₀,…,x_k)` of a path (coordinates beyond `n` read as `x_n`). -/
def prefixMap (n k : ℕ) (x : Fin (n + 1) → X) : Fin (k + 1) → X := fun i ↦ pathAt x i

/-- `σ(X₀,…,X_k)`. -/
def prefixSigma (n k : ℕ) : MeasurableSpace (Fin (n + 1) → X) :=
  MeasurableSpace.comap (prefixMap n k) inferInstance

theorem prefixSigma_le (n k : ℕ) : prefixSigma (X := X) n k ≤ MeasurableSpace.pi :=
  (measurable_of_countable (prefixMap (X := X) n k)).comap_le

theorem prefixSigma_mono (n : ℕ) {k k' : ℕ} (h : k ≤ k') :
    prefixSigma (X := X) n k ≤ prefixSigma n k' := by
  have hr : Measurable (fun p : Fin (k' + 1) → X ↦ fun i : Fin (k + 1) ↦ p ⟨i, by omega⟩) :=
    measurable_of_countable _
  have hcomp : prefixMap (X := X) n k =
      (fun p : Fin (k' + 1) → X ↦ fun i : Fin (k + 1) ↦ p ⟨i, by omega⟩) ∘ prefixMap n k' := rfl
  unfold prefixSigma
  rw [hcomp, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hr.comap_le

/-- The pair-chain filtration `j ↦ σ(X₀,…,X_{τ+j})`. -/
def prefixFiltration (n τ : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (Fin (n + 1) → X)) :=
  ⟨fun j ↦ prefixSigma n (τ + j), fun _ _ h ↦ prefixSigma_mono n (by omega),
    fun j ↦ prefixSigma_le n (τ + j)⟩

theorem dependsUpTo_indicator {n k : ℕ} {s : Set (Fin (n + 1) → X)}
    (hs : MeasurableSet[prefixSigma n k] s) : DependsUpTo k (s.indicator fun _ ↦ (1 : ℝ)) := by
  obtain ⟨t, -, rfl⟩ := hs
  intro x x' hx
  have : prefixMap n k x = prefixMap n k x' := funext fun i ↦ hx i (by omega)
  show (prefixMap n k ⁻¹' t).indicator (fun _ ↦ (1 : ℝ)) x =
    (prefixMap n k ⁻¹' t).indicator (fun _ ↦ (1 : ℝ)) x'
  by_cases h1 : prefixMap n k x ∈ t
  · rw [Set.indicator_of_mem (by exact h1), Set.indicator_of_mem (by rw [Set.mem_preimage, ← this]; exact h1)]
  · rw [Set.indicator_of_notMem (by exact h1),
      Set.indicator_of_notMem (by rw [Set.mem_preimage, ← this]; exact h1)]

theorem DependsUpTo.stronglyMeasurable {n k : ℕ} {f : (Fin (n + 1) → X) → ℝ}
    (hf : DependsUpTo k f) : StronglyMeasurable[prefixSigma n k] f := by
  let ext : (Fin (k + 1) → X) → Fin (n + 1) → X := fun p j ↦ p ⟨min j k, by omega⟩
  have heq : f = (fun p ↦ f (ext p)) ∘ prefixMap n k := by
    funext x
    refine (hf _ _ fun i hi ↦ ?_).symm
    simp only [ext, pathAt, prefixMap]
    congr 1; ext; simp; omega
  rw [heq]
  exact ((measurable_of_countable _).comp (comap_measurable _)).stronglyMeasurable

/-- Freedman (`K₀ = 1`) for Markov martingale differences `C_j · h(X_{τ+j}, X_{τ+j+1})`. -/
theorem markov_freedman (hK : IsStochastic K) (hν : IsProb ν) {n τ m : ℕ} (hm : τ + m ≤ n)
    (C : ℕ → (Fin (n + 1) → X) → ℝ) (hC : ∀ j, DependsUpTo (τ + j) (C j))
    {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ j x, |C j x| ≤ Cb)
    (h : X → X → ℝ) (hcent : ∀ u, ∑ y, K u y * h u y = 0) {Hb : ℝ} (hHb0 : 0 ≤ Hb)
    (hHb : ∀ u y, |h u y| ≤ Hb) {σ₂ : ℝ} (hσ0 : 0 ≤ σ₂)
    (hσ : ∀ x, ∑ j ∈ range m, C j x ^ 2 *
      ∑ y, K (pathAt x (τ + j)) y * h (pathAt x (τ + j)) y ^ 2 ≤ σ₂)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (pathMeasure ν K n).real {x | |∑ j ∈ range m,
      C j x * h (pathAt x (τ + j)) (pathAt x (τ + j + 1))| ≤
        Real.sqrt (8 * σ₂ * Real.log (2 / δ)) + (4 / 3) * (Cb * Hb) * Real.log (2 / δ)} := by
  set μ := pathMeasure ν K n
  haveI := pathMeasure_isProb hK hν n
  set F := prefixFiltration (X := X) n τ
  let inc : ℕ → (Fin (n + 1) → X) → ℝ := fun j x ↦
    if j < m then C j x * h (pathAt x (τ + j)) (pathAt x (τ + j + 1)) else 0
  have hdep : ∀ j, DependsUpTo (τ + j + 1) (inc j) := fun j x x' hx ↦ by
    simp only [inc]
    split_ifs
    · rw [(hC j).mono (Nat.le_succ _) x x' hx, hx (τ + j) (Nat.le_succ _), hx (τ + j + 1) le_rfl]
    · rfl
  have hX : ∀ j, StronglyMeasurable[F (j + 1)] (inc j) := fun j ↦ (hdep j).stronglyMeasurable
  have hb : ∀ j, ∀ᵐ x ∂μ, |inc j x| ≤ Cb * Hb := fun j ↦ Filter.Eventually.of_forall fun x ↦ by
    simp only [inc]
    split_ifs
    · rw [abs_mul]; exact mul_le_mul (hCb j x) (hHb _ _) (abs_nonneg _) hCb0
    · simp [mul_nonneg hCb0 hHb0]
  have hint : ∀ f : (Fin (n + 1) → X) → ℝ, Integrable f μ := fun f ↦ Integrable.of_finite
  -- set integrals of Markov increments
  have hset : ∀ j, j < m → ∀ (G : (Fin (n + 1) → X) → ℝ), DependsUpTo (τ + j) G →
      ∀ (g : X → X → ℝ), ∀ s, MeasurableSet[F j] s →
      ∫ x in s, G x * g (pathAt x (τ + j)) (pathAt x (τ + j + 1)) ∂μ =
        ∫ x in s, G x * ∑ y, K (pathAt x (τ + j)) y * g (pathAt x (τ + j)) y ∂μ := by
    intro j hj G hG g s hs
    rw [setIntegral_pathMeasure hK hν, setIntegral_pathMeasure hK hν]
    have hGs : DependsUpTo (τ + j) (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) x * G x) :=
      (dependsUpTo_indicator hs).mul hG
    have := pathExp_markov_step (ν := ν) hK (k := τ + j) (by omega) _ hGs g
    simp only [mul_assoc] at this
    exact this
  have hc : ∀ j, μ[inc j | F j] =ᵐ[μ] fun _ ↦ 0 := by
    intro j
    by_cases hj : j < m
    · refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le j) (hint _)
        (fun s _ _ ↦ integrableOn_zero) (fun s hs _ ↦ ?_)
        stronglyMeasurable_const.aestronglyMeasurable).symm
      have h1 := hset j hj (C j) (hC j) h s hs
      simp only [hcent, mul_zero, integral_zero] at h1
      simp only [inc, if_pos hj, integral_zero]
      exact h1.symm
    · have : inc j = fun _ ↦ 0 := funext fun x ↦ by simp [inc, hj]
      rw [this, condExp_const (F.le j)]
  have hsq : ∀ j, j < m → μ[fun x ↦ inc j x ^ 2 | F j] =ᵐ[μ] fun x ↦ C j x ^ 2 *
      ∑ y, K (pathAt x (τ + j)) y * h (pathAt x (τ + j)) y ^ 2 := by
    intro j hj
    have hg : DependsUpTo (τ + j) (fun x ↦ C j x ^ 2 *
        ∑ y, K (pathAt x (τ + j)) y * h (pathAt x (τ + j)) y ^ 2) := fun x x' hx ↦ by
      show C j x ^ 2 * ∑ y, K (pathAt x (τ + j)) y * h (pathAt x (τ + j)) y ^ 2 =
        C j x' ^ 2 * ∑ y, K (pathAt x' (τ + j)) y * h (pathAt x' (τ + j)) y ^ 2
      rw [hC j x x' hx, hx (τ + j) le_rfl]
    refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le j) (hint _)
      (fun s _ _ ↦ (hint _).integrableOn) (fun s hs _ ↦ ?_)
      (hg.stronglyMeasurable.aestronglyMeasurable (μ := μ))).symm
    have h1 := hset j hj (fun x ↦ C j x ^ 2) (fun x x' hx ↦ by
      show C j x ^ 2 = C j x' ^ 2; rw [hC j x x' hx]) (fun u v ↦ h u v ^ 2) s hs
    simp only [inc, if_pos hj]
    rw [← h1]
    congr 1; funext x; ring
  have hcap : ∀ᵐ x ∂μ, predictableSecondMomentSum μ F inc m x ≤ σ₂ := by
    have hall : ∀ᵐ x ∂μ, ∀ j, j < m → μ[fun x ↦ inc j x ^ 2 | F j] x = C j x ^ 2 *
        ∑ y, K (pathAt x (τ + j)) y * h (pathAt x (τ + j)) y ^ 2 := by
      rw [ae_all_iff]; intro j
      by_cases hj : j < m
      · filter_upwards [hsq j hj] with x hx _; exact hx
      · exact Filter.Eventually.of_forall fun x hj' ↦ absurd hj' hj
    filter_upwards [hall] with x hx
    unfold predictableSecondMomentSum
    rw [sum_congr rfl fun j hj ↦ hx j (mem_range.mp hj)]
    exact hσ x
  have hfr := freedman_source_bound μ F inc (Cb * Hb) σ₂ (mul_nonneg hCb0 hHb0) hσ0 hX hb hc m 1
    one_pos hcap δ hδ hδ1
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  refine hfr.trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae ?_))
  filter_upwards [hcap] with x hx hmem
  change |incrementSum inc m x| ≤ _ at hmem
  change |∑ j ∈ range m, C j x * h (pathAt x (τ + j)) (pathAt x (τ + j + 1))| ≤ _
  have hi : incrementSum inc m x = ∑ j ∈ range m, C j x * h (pathAt x (τ + j)) (pathAt x (τ + j + 1)) :=
    sum_congr rfl fun j hj ↦ by simp [inc, mem_range.mp hj]
  rw [hi] at hmem
  simp only [Nat.cast_one, mul_one, pow_one] at hmem
  have hmax : max (predictableSecondMomentSum μ F inc m x) (σ₂ / 2) ≤ σ₂ := max_le hx (by linarith)
  have hs : Real.sqrt (8 * max (predictableSecondMomentSum μ F inc m x) (σ₂ / 2) * Real.log (2 / δ)) ≤
      Real.sqrt (8 * σ₂ * Real.log (2 / δ)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) hL)
  linarith

end StatisticalRL.FiniteMarkov
