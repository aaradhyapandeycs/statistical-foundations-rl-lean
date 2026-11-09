import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Smooth compactly supported test functions determine weak convergence

Generic infrastructure (no source claim). On a finite-dimensional real normed space `E` with its
Borel σ-algebra, if probability measures `μₙ` satisfy `∫ f dμₙ → ∫ f dν` for every `C^∞`
compactly supported `f : E → ℝ`, then `∫ g dμₙ → ∫ g dν` for every bounded continuous `g`, i.e.
`μₙ → ν` weakly. No tightness hypothesis is needed: the open-set Portmanteau criterion
(`MeasureTheory.tendsto_of_forall_isOpen_le_liminf'`) only requires probability measures.

For an open set `G` the approximants are `h_k = χ_k · (1 − (1 − f)^k)`, where `f` is smooth with
support exactly `G` and values in `[0, 1]` (`IsOpen.exists_smooth_support_eq`) and `χ_k` is a
smooth bump equal to `1` on the closed ball of radius `k + 1`. Each `h_k` is smooth, compactly
supported, `0 ≤ h_k ≤ 1_G`, and `h_k → 1_G` pointwise; dominated convergence gives
`∫ h_k dν → ν(G)`.

Exports:
* `exists_smooth_approx_indicator_of_isOpen`;
* `tendsto_integral_bcf_of_tendsto_integral_smooth` (the bridge);
* `exists_smooth_test_bounds` (a `C^∞` compactly supported `f` is `C²` with bounded first
  derivative and Lipschitz second derivative).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace StatisticalRL.Probability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Smooth compactly supported approximants of the indicator of an open set, from below. -/
theorem exists_smooth_approx_indicator_of_isOpen {G : Set E} (hG : IsOpen G) :
    ∃ h : ℕ → E → ℝ, (∀ k, ContDiff ℝ ∞ (h k)) ∧ (∀ k, HasCompactSupport (h k)) ∧
      (∀ k x, 0 ≤ h k x) ∧ (∀ k x, h k x ≤ G.indicator 1 x) ∧
      ∀ x, Tendsto (fun k ↦ h k x) atTop (𝓝 (G.indicator 1 x)) := by
  obtain ⟨f, hfs, hfc, hfr⟩ := hG.exists_smooth_support_eq
  have hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := fun x ↦ hfr (mem_range_self x)
  let χ : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨(k : ℝ) + 1, (k : ℝ) + 2, by positivity, by linarith⟩
  have hpow : ∀ k x, 0 ≤ (1 - f x) ^ k ∧ (1 - f x) ^ k ≤ 1 := fun k x ↦
    ⟨pow_nonneg (by linarith [hf01 x]) k, pow_le_one₀ (by linarith [hf01 x]) (by linarith [hf01 x])⟩
  have hoff : ∀ k x, x ∉ G → (χ k x) * (1 - (1 - f x) ^ k) = 0 := by
    intro k x hx
    have : f x = 0 := by
      rw [← hfs] at hx
      exact Function.notMem_support.1 hx
    rw [this, sub_zero, one_pow, sub_self, mul_zero]
  refine ⟨fun k x ↦ χ k x * (1 - (1 - f x) ^ k), ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (χ k).contDiff.mul (contDiff_const.sub ((contDiff_const.sub hfc).pow k))
  · intro k
    exact (χ k).hasCompactSupport.mul_right
  · intro k x
    exact mul_nonneg (χ k).nonneg (by linarith [hpow k x])
  · intro k x
    dsimp only
    by_cases hx : x ∈ G
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact mul_le_one₀ (χ k).le_one (by linarith [hpow k x]) (by linarith [hpow k x])
    · rw [hoff k x hx, indicator_of_notMem hx]
  · intro x
    dsimp only
    by_cases hx : x ∈ G
    · rw [indicator_of_mem hx, Pi.one_apply]
      have hfx : 0 < f x := by
        rcases (hf01 x).1.eq_or_lt with h | h
        · exfalso
          rw [← hfs] at hx
          exact hx h.symm
        · exact h
      have hlim : Tendsto (fun k : ℕ ↦ 1 - (1 - f x) ^ k) atTop (𝓝 1) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hf01 x])
          (by linarith : 1 - f x < 1)).const_sub (1 : ℝ)
        rwa [sub_zero] at this
      refine hlim.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      refine ⟨⌈‖x‖⌉₊, fun k hk ↦ ?_⟩
      have hxk : x ∈ Metric.closedBall (0 : E) (χ k).rIn := by
        rw [mem_closedBall_zero_iff]
        have h1 : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈‖x‖⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
        change ‖x‖ ≤ (k : ℝ) + 1
        linarith
      rw [(χ k).one_of_mem_closedBall hxk, one_mul]
    · rw [indicator_of_notMem hx]
      exact tendsto_const_nhds.congr fun k ↦ (hoff k x hx).symm

variable [MeasurableSpace E] [BorelSpace E]

/-- **Smooth compactly supported tests determine weak convergence.** If probability measures
`μs n` on a finite-dimensional real normed space satisfy `∫ f d(μs n) → ∫ f dν` for every `C^∞`
compactly supported `f`, then the same holds for every bounded continuous `g`. -/
theorem tendsto_integral_bcf_of_tendsto_integral_smooth {μs : ℕ → Measure E}
    [∀ n, IsProbabilityMeasure (μs n)] {ν : Measure E} [IsProbabilityMeasure ν]
    (h : ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n)) atTop (𝓝 (∫ x, f x ∂ν)))
    (g : BoundedContinuousFunction E ℝ) :
    Tendsto (fun n ↦ ∫ x, g x ∂(μs n)) atTop (𝓝 (∫ x, g x ∂ν)) := by
  let P : ℕ → ProbabilityMeasure E := fun n ↦ ⟨μs n, inferInstance⟩
  let Q : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hPQ : Tendsto P atTop (𝓝 Q) := by
    refine tendsto_of_forall_isOpen_le_liminf' fun G hG ↦ ?_
    change ν G ≤ atTop.liminf (fun n ↦ μs n G)
    obtain ⟨hk, hsm, hcs, h0, h1, hlim⟩ := exists_smooth_approx_indicator_of_isOpen hG
    have hint : ∀ k (m : Measure E) [IsProbabilityMeasure m], Integrable (hk k) m := fun k m _ ↦
      (hsm k).continuous.integrable_of_hasCompactSupport (hcs k)
    have hle : ∀ k (m : Measure E) [IsProbabilityMeasure m],
        ENNReal.ofReal (∫ x, hk k x ∂m) ≤ m G := by
      intro k m _
      have hI : ∫ x, hk k x ∂m ≤ m.real G := by
        rw [← integral_indicator_one hG.measurableSet]
        exact integral_mono (hint k m) ((integrable_const (1 : ℝ)).indicator hG.measurableSet)
          (h1 k)
      calc ENNReal.ofReal (∫ x, hk k x ∂m) ≤ ENNReal.ofReal (m.real G) :=
            ENNReal.ofReal_le_ofReal hI
        _ = m G := ofReal_measureReal
    have hstep : ∀ k, ENNReal.ofReal (∫ x, hk k x ∂ν) ≤ atTop.liminf (fun n ↦ μs n G) := by
      intro k
      have ht := (ENNReal.continuous_ofReal.tendsto _).comp (h _ (hsm k) (hcs k))
      rw [← ht.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall fun n ↦ hle k (μs n))
    have hconv : Tendsto (fun k ↦ ∫ x, hk k x ∂ν) atTop (𝓝 (ν.real G)) := by
      rw [← integral_indicator_one hG.measurableSet]
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
        (fun k ↦ (hsm k).continuous.aestronglyMeasurable) (integrable_const 1)
        (fun k ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall hlim)
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 k x)]
      refine (h1 k x).trans ?_
      by_cases hx : x ∈ G
      · rw [indicator_of_mem hx, Pi.one_apply]
      · rw [indicator_of_notMem hx]; exact zero_le_one
    have hconv' : Tendsto (fun k ↦ ENNReal.ofReal (∫ x, hk k x ∂ν)) atTop (𝓝 (ν G)) := by
      rw [← ofReal_measureReal (μ := ν) (s := G)]
      exact (ENNReal.continuous_ofReal.tendsto _).comp hconv
    exact le_of_tendsto' hconv' hstep
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hPQ g

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A `C^∞` compactly supported `f : E → ℝ` is `C²`, has bounded first derivative and Lipschitz
second derivative (the hypothesis shape of `scaledError_smooth_gaussian_le`). -/
theorem exists_smooth_test_bounds {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f) :
    ContDiff ℝ 2 f ∧ (∃ L₁ : ℝ, ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) ∧
      ∃ L₂ : ℝ, ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂ * ‖x - y‖ := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.2 le_top)
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := h2.fderiv_right (by norm_num)
  have h3 : ContDiff ℝ 3 f := hf.of_le (WithTop.coe_le_coe.2 le_top)
  have h2' : ContDiff ℝ 2 (fderiv ℝ f) := h3.fderiv_right (by norm_num)
  have h1' : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := h2'.fderiv_right (by norm_num)
  refine ⟨h2, ?_, ?_⟩
  · exact (hcs.fderiv ℝ).exists_bound_of_continuous (h1.continuous)
  · obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport ((hcs.fderiv ℝ).fderiv ℝ) h1'
      le_rfl
    refine ⟨C, fun x y ↦ ?_⟩
    have := hC.dist_le_mul x y
    rwa [dist_eq_norm, dist_eq_norm] at this

end StatisticalRL.Probability
