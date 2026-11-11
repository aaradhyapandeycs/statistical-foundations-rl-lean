import Formalization.TDInference.ZeroNoiseRefutation
import Formalization.TDInference.SomeInitVariants
import Formalization.TDInference.PathMarginals
import Formalization.Analysis.StepSizeSums

/-!
# Theorem 7.11 is false for every fixed initialization under `r(s) = r_π(s)` with
action-dependent rewards (SOURCE-ISSUES C43, refutation R2)

Reading: rewards depend on `(s,a)` as printed (`inference.tex:62`) and the undefined `r(s)` in the
printed `Γ` is `r_π(s)` (`prelim.tex:418`); the state-only-reward reading and the corrected
statement with the true `Γ` are not refuted here.

Source: `chapters/inference.tex:132–141` (statement), :99–117 (`A`, `Γ`), :47–90 (algorithm).

Instance Z of `TDInference/ZeroNoiseRefutation.lean` (two states and actions, `γ = 1/2`, `μ`, `π` uniform,
`s' = a`, `r = (1/2, 3/4; 0, 1/4)`, `V^π = (1, 1/2)`) has zero per-sample TD noise. Here the
initialization `V₀` is *arbitrary*, so this refutes the readings in which the bound need only hold
for one `V₀` per instance (e.g. the convention `V₀ = 0`).

Route (check file §3.2–3.4, fixes F5, O4):
1. Lyapunov step (`zOneStep`): with `Φ(V) = ‖V − V^π‖²`, one TD step at step size `η ∈ [0,1]`
   satisfies `E Φ(V') ≤ (1 − 3η/8) Φ(V)` (exactly `E Φ(V') = (1 − η/2 + η²/8)Φ − …`).
2. Hence `E Φ(V_t) ≤ Φ(V₀) exp(−(3/8)∑_{i≤t} η_i) ≤ Φ(V₀) exp(−(3/8)η₀ t^{1/3})`
   (`zLyap_expect_le`), using `∑_{i≤t} i^{-2/3} ≥ t^{1/3}`.
3. `E|V_t(0) − V^π(0)| ≤ ((Φ(V₀)+1)/2) exp(−(3η₀/16) t^{1/3})` (`zAbsDev_expect_le`; AM–GM, no
   square roots), and the stretched exponentials are summable uniformly in `T`, so
   `E|(√T Δ̄_T)(0)| ≤ D/√T` (`zScaledError_expect_le`).
4. Markov: `P(|(√T Δ̄_T)(0)| ≤ 1/20) ≥ 1 − 20 D/√T` (`zLawProb_slab_ge`).
5. The printed Gaussian puts mass `≤ 2ε/(|(A⁻¹)₀₀ √Γ₀|√(2π)) = 4/(15√π) < 1/4` on the closed
   convex slab `{x : |x 0| ≤ 1/20}` (`zGauss_slab_le`; `(A⁻¹)₀₀ = 3`, `Γ₀ = 1/128`). This
   conditioning bound (≈ 0.150) dominates the exact marginal mass (≈ 0.142, variance 10/128).
6. So the gap on that slab is `≥ 3/4 − 20D/√T`, while the printed right-hand side tends to `0` for
   any constants `c, C̃` (`anyInit_violates`). No CLT is used.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

namespace ZeroNoise

/-- `Φ(V) = ‖V − V^π‖²` at instance Z, `V^π = (1, 1/2)`. -/
noncomputable def zLyap (V : Fin 2 → ℝ) : ℝ := (V 0 - 1) ^ 2 + (V 1 - 1 / 2) ^ 2

theorem zLyap_nonneg (V : Fin 2 → ℝ) : 0 ≤ zLyap V := by unfold zLyap; positivity

/-- One TD step contracts `Φ` in expectation: `E Φ(TDstep_η(V)) ≤ (1 − 3η/8) Φ(V)` for
`η ∈ [0, 1]` (the per-sample noise vanishes at instance Z). -/
theorem zOneStep (V : Fin 2 → ℝ) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ∑ x, tupleProb zMDP zPolicy zMu x * zLyap (tdStep zMDP η V x) ≤ (1 - 3 * η / 8) * zLyap V := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, tupleProb, zTransition_prob, zMu, zPolicy,
    uniformRow_two_prob]
  simp [zLyap, tdStep, zMDP]
  nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1))
    (add_nonneg (mul_nonneg zero_le_two (sq_nonneg ((V 0 - 1) - (V 1 - 1 / 2))))
      (add_nonneg (sq_nonneg (V 0 - 1)) (sq_nonneg (V 1 - 1 / 2))))]

theorem stepSize_succ_nonneg {η₀ : ℝ} (h0 : 0 ≤ η₀) (t : ℕ) : 0 ≤ stepSize η₀ (t + 1) :=
  mul_nonneg h0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem stepSize_succ_le {η₀ : ℝ} (h0 : 0 ≤ η₀) (t : ℕ) : stepSize η₀ (t + 1) ≤ η₀ := by
  refine mul_le_of_le_one_right h0 (Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num))
  exact_mod_cast Nat.le_add_left 1 t

/-- `∑_{i=1}^t η_i ≥ η₀ t^{1/3}` for the printed schedule `η_i = η₀ i^{-2/3}`. -/
theorem sum_stepSize_ge {η₀ : ℝ} (h0 : 0 ≤ η₀) (t : ℕ) :
    η₀ * (t : ℝ) ^ (1 / 3 : ℝ) ≤ ∑ i ∈ range t, stepSize η₀ (i + 1) := by
  have h := sum_range_succ_rpow_neg_ge t (p := 2 / 3) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num] at h
  simp only [stepSize, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h h0

/-- Lyapunov decay along the TD path: `E Φ(V_t) ≤ Φ(V₀) exp(−(3/8)∑_{i=1}^t η_i)`. -/
theorem zLyap_expect_le_exp_sum {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (V₀ : Fin 2 → ℝ) (t : ℕ) :
    ∑ ω : Fin t → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * zLyap (tdIter zMDP η₀ V₀ ω t) ≤
      zLyap V₀ * Real.exp (-(3 / 8) * ∑ i ∈ range t, stepSize η₀ (i + 1)) := by
  induction t with
  | zero => simp [pathWeight, tdIter]
  | succ t ih =>
    rw [sum_pathWeight_mul_tdIter_succ]
    set η := stepSize η₀ (t + 1) with hη
    have hη0 : 0 ≤ η := stepSize_succ_nonneg h0 t
    have hη1 : η ≤ 1 := (stepSize_succ_le h0 t).trans h1
    have hS : 0 ≤ ∑ ω : Fin t → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * zLyap (tdIter zMDP η₀ V₀ ω t) :=
      sum_nonneg fun ω _ ↦ mul_nonneg (pathWeight_nonneg _ _ _ ω) (zLyap_nonneg _)
    calc _ ≤ ∑ ω : Fin t → Tuple (Fin 2) (Fin 2), pathWeight zMDP zPolicy zMu ω *
          ((1 - 3 * η / 8) * zLyap (tdIter zMDP η₀ V₀ ω t)) :=
          sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (zOneStep _ hη0 hη1)
            (pathWeight_nonneg _ _ _ ω)
      _ = (1 - 3 * η / 8) * ∑ ω : Fin t → Tuple (Fin 2) (Fin 2),
          pathWeight zMDP zPolicy zMu ω * zLyap (tdIter zMDP η₀ V₀ ω t) := by
          rw [Finset.mul_sum]
          exact sum_congr rfl fun ω _ ↦ by ring
      _ ≤ Real.exp (-(3 / 8) * η) *
          (zLyap V₀ * Real.exp (-(3 / 8) * ∑ i ∈ range t, stepSize η₀ (i + 1))) := by
          refine mul_le_mul ?_ ih hS (Real.exp_pos _).le
          linarith [Real.add_one_le_exp (-(3 / 8) * η)]
      _ = zLyap V₀ * Real.exp (-(3 / 8) * ∑ i ∈ range (t + 1), stepSize η₀ (i + 1)) := by
          rw [sum_range_succ, mul_add, Real.exp_add]
          ring

/-- `E Φ(V_t) ≤ Φ(V₀) exp(−(3/8) η₀ t^{1/3})`. -/
theorem zLyap_expect_le {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (V₀ : Fin 2 → ℝ) (t : ℕ) :
    ∑ ω : Fin t → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * zLyap (tdIter zMDP η₀ V₀ ω t) ≤
      zLyap V₀ * Real.exp (-(3 / 8 * (η₀ * (t : ℝ) ^ (1 / 3 : ℝ)))) := by
  refine (zLyap_expect_le_exp_sum h0 h1 V₀ t).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (zLyap_nonneg V₀))
  linarith [sum_stepSize_ge h0 t]

/-- First-moment decay of the first coordinate:
`E|V_t(0) − 1| ≤ ((Φ(V₀)+1)/2) exp(−(3η₀/16) t^{1/3})`. -/
theorem zAbsDev_expect_le {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (V₀ : Fin 2 → ℝ) (t : ℕ) :
    ∑ ω : Fin t → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * |tdIter zMDP η₀ V₀ ω t 0 - 1| ≤
      (zLyap V₀ + 1) / 2 * Real.exp (-(3 * η₀ / 16 * (t : ℝ) ^ (1 / 3 : ℝ))) := by
  set δ := Real.exp (-(3 * η₀ / 16 * (t : ℝ) ^ (1 / 3 : ℝ))) with hδ
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ2 : Real.exp (-(3 / 8 * (η₀ * (t : ℝ) ^ (1 / 3 : ℝ)))) = δ * δ := by
    rw [hδ, ← Real.exp_add]; ring_nf
  have hpt : ∀ V : Fin 2 → ℝ, |V 0 - 1| ≤ zLyap V / (2 * δ) + δ / 2 := by
    intro V
    have h2 : (V 0 - 1) ^ 2 ≤ zLyap V := by
      unfold zLyap; nlinarith [sq_nonneg (V 1 - 1 / 2)]
    rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|V 0 - 1| - δ), sq_abs (V 0 - 1)]
  have hE := zLyap_expect_le h0 h1 V₀ t
  rw [hδ2] at hE
  calc _ ≤ ∑ ω : Fin t → Tuple (Fin 2) (Fin 2), pathWeight zMDP zPolicy zMu ω *
        (zLyap (tdIter zMDP η₀ V₀ ω t) / (2 * δ) + δ / 2) :=
        sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hpt _) (pathWeight_nonneg _ _ _ ω)
    _ = (∑ ω : Fin t → Tuple (Fin 2) (Fin 2),
          pathWeight zMDP zPolicy zMu ω * zLyap (tdIter zMDP η₀ V₀ ω t)) / (2 * δ) +
          δ / 2 * ∑ ω : Fin t → Tuple (Fin 2) (Fin 2), pathWeight zMDP zPolicy zMu ω := by
        rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact sum_congr rfl fun ω _ ↦ by ring
    _ ≤ zLyap V₀ * (δ * δ) / (2 * δ) + δ / 2 * 1 := by
        rw [sum_pathWeight]
        gcongr
    _ = (zLyap V₀ + 1) / 2 * δ := by field_simp

/-- `√T Δ̄_T` evaluated at state `0` is `T^{-1/2} ∑_{t=1}^T (V_t(0) − V^π(0))`. -/
theorem zScaledError_apply_zero (η₀ : ℝ) (V₀ : Fin 2 → ℝ) {T : ℕ} (hT : 1 ≤ T)
    (ω : Fin T → Tuple (Fin 2) (Fin 2)) :
    scaledError zMDP zPolicy η₀ V₀ ω 0 =
      (Real.sqrt T)⁻¹ * ∑ t ∈ range T, (tdIter zMDP η₀ V₀ ω (t + 1) 0 - 1) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  simp only [scaledError, zValueFixedPoint, prAverage, Pi.smul_apply, Pi.sub_apply,
    Finset.sum_apply, smul_eq_mul, Finset.sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hz : zV 0 = 1 := rfl
  have key : (Real.sqrt T)⁻¹ = Real.sqrt T * (T : ℝ)⁻¹ := by
    calc (Real.sqrt T)⁻¹ = Real.sqrt T * (Real.sqrt T * Real.sqrt T)⁻¹ := by field_simp
      _ = _ := by rw [hss]
  rw [hz, key]
  field_simp

/-- `E|(√T Δ̄_T)(0)| ≤ T^{-1/2} · ((Φ(V₀)+1)/2) · 1440/(3η₀/16)^6`. -/
theorem zScaledError_expect_le {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : Fin 2 → ℝ) {T : ℕ}
    (hT : 1 ≤ T) :
    ∑ ω : Fin T → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * |scaledError zMDP zPolicy η₀ V₀ ω 0| ≤
      (Real.sqrt T)⁻¹ * ((zLyap V₀ + 1) / 2 * (1440 / (3 * η₀ / 16) ^ 6)) := by
  have hs : 0 ≤ (Real.sqrt T)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hc : 0 < 3 * η₀ / 16 := by positivity
  calc _ ≤ ∑ ω : Fin T → Tuple (Fin 2) (Fin 2), pathWeight zMDP zPolicy zMu ω *
        ((Real.sqrt T)⁻¹ * ∑ t ∈ range T, |tdIter zMDP η₀ V₀ ω (t + 1) 0 - 1|) := by
        refine sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg _ _ _ ω)
        rw [zScaledError_apply_zero η₀ V₀ hT, abs_mul, abs_of_nonneg hs]
        exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hs
    _ = (Real.sqrt T)⁻¹ * ∑ t ∈ range T, ∑ ω : Fin (t + 1) → Tuple (Fin 2) (Fin 2),
          pathWeight zMDP zPolicy zMu ω * |tdIter zMDP η₀ V₀ ω (t + 1) 0 - 1| := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine sum_congr rfl fun t ht ↦ ?_
        have htT : t + 1 ≤ T := mem_range.1 ht
        rw [← Finset.mul_sum,
          ← sum_pathWeight_mul_tdIter_of_le zMDP zPolicy zMu η₀ V₀ (fun V ↦ |V 0 - 1|) htT,
          Finset.mul_sum]
        exact sum_congr rfl fun ω _ ↦ by ring
    _ ≤ (Real.sqrt T)⁻¹ * ∑ t ∈ range T, (zLyap V₀ + 1) / 2 *
          Real.exp (-(3 * η₀ / 16 * ((t : ℝ) + 1) ^ (1 / 3 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun t _ ↦ ?_) hs
        have := zAbsDev_expect_le h0.le h1 V₀ (t + 1)
        push_cast at this
        exact this
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sum_range_exp_neg_mul_cbrt_le hc T) ?_) hs
        have := zLyap_nonneg V₀
        positivity

/-- The closed convex slab `{x : |x 0| ≤ ε}`. -/
def zSlab (ε : ℝ) : Set (Fin 2 → ℝ) := {x | |x 0| ≤ ε}

theorem zSlab_convex (ε : ℝ) : Convex ℝ (zSlab ε) := by
  intro x hx y hy a b ha hb hab
  simp only [zSlab, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  calc |a * x 0 + b * y 0| ≤ |a * x 0| + |b * y 0| := abs_add_le _ _
    _ = a * |x 0| + b * |y 0| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * ε + b * ε := by gcongr
    _ = ε := by rw [← add_mul, hab, one_mul]

theorem zSlab_isClosed (ε : ℝ) : IsClosed (zSlab ε) :=
  isClosed_le (continuous_abs.comp (continuous_apply 0)) continuous_const

/-- Markov's inequality on the slab: `P(√T Δ̄_T ∈ slab_ε) ≥ 1 − E|(√T Δ̄_T)(0)|/ε`. -/
theorem zLawProb_slab_ge {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : Fin 2 → ℝ) {T : ℕ}
    (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    1 - (Real.sqrt T)⁻¹ * ((zLyap V₀ + 1) / 2 * (1440 / (3 * η₀ / 16) ^ 6)) / ε ≤
      lawProb zMDP zPolicy zMu η₀ V₀ T (zSlab ε) := by
  have hpt : ∀ ω : Fin T → Tuple (Fin 2) (Fin 2),
      1 - (zSlab ε).indicator (fun _ ↦ (1 : ℝ)) (scaledError zMDP zPolicy η₀ V₀ ω) ≤
        |scaledError zMDP zPolicy η₀ V₀ ω 0| / ε := by
    intro ω
    by_cases h : scaledError zMDP zPolicy η₀ V₀ ω ∈ zSlab ε
    · rw [Set.indicator_of_mem h, sub_self]; positivity
    · rw [Set.indicator_of_notMem h, sub_zero, le_div_iff₀ hε, one_mul]
      simp only [zSlab, Set.mem_setOf_eq, not_le] at h
      exact h.le
  have hsum : 1 - lawProb zMDP zPolicy zMu η₀ V₀ T (zSlab ε) ≤
      (∑ ω : Fin T → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * |scaledError zMDP zPolicy η₀ V₀ ω 0|) / ε := by
    rw [← sum_pathWeight zMDP zPolicy zMu T, lawProb, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine sum_le_sum fun ω _ ↦ ?_
    have h := mul_le_mul_of_nonneg_left (hpt ω) (pathWeight_nonneg zMDP zPolicy zMu ω)
    rw [mul_sub, mul_one, ← mul_div_assoc] at h
    exact h
  have hE := zScaledError_expect_le h0 h1 V₀ hT
  have : (∑ ω : Fin T → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * |scaledError zMDP zPolicy η₀ V₀ ω 0|) / ε ≤
      (Real.sqrt T)⁻¹ * ((zLyap V₀ + 1) / 2 * (1440 / (3 * η₀ / 16) ^ 6)) / ε :=
    div_le_div_of_nonneg_right hE hε.le
  linarith

/-- `A⁻¹ = [[3, 1], [1, 3]]` at instance Z. -/
theorem zA_inv : (tdA zMDP zPolicy zMu)⁻¹ = !![3, 1; 1, 3] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, zA_apply] <;> norm_num

/-- The printed Gaussian gives the slab `{x : |x 0| ≤ 1/20}` mass at most `1/4`
(exactly `≤ 4/(15√π) ≈ 0.150`). -/
theorem zGauss_slab_le :
    (gaussCov (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu)).real (zSlab (1 / 20)) ≤
      1 / 4 := by
  have hΓ : printedGamma zMDP zPolicy zMu 0 = 1 / 128 := zPrintedGamma 0
  have hA : (tdA zMDP zPolicy zMu)⁻¹ 0 0 = 3 := by rw [zA_inv]; rfl
  have hq0 : 0 < Real.sqrt (1 / 128) := Real.sqrt_pos.2 (by norm_num)
  have hj : (tdA zMDP zPolicy zMu)⁻¹ 0 0 * Real.sqrt (printedGamma zMDP zPolicy zMu 0) ≠ 0 := by
    rw [hA, hΓ]; positivity
  have h := gaussCov_slab_le (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu) 0 0 hj 0
    (1 / 20)
  have hset : {x : Fin 2 → ℝ | |x 0 - 0| ≤ 1 / 20} = zSlab (1 / 20) := by
    ext x; simp [zSlab]
  rw [hset, hA, hΓ] at h
  have hπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set q := |3 * Real.sqrt (1 / 128)| * Real.sqrt (2 * Real.pi) with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  have hq2 : q ^ 2 = 9 * Real.pi / 64 := by
    rw [hq, mul_pow, sq_abs, mul_pow, Real.sq_sqrt (by norm_num),
      Real.sq_sqrt (by positivity)]
    ring
  have hqge : 2 / 5 ≤ q := by
    nlinarith [Real.two_le_pi]
  have hbound : 2 * (1 / 20 : ℝ) / q ≤ 1 / 4 := by
    rw [div_le_iff₀ hqpos]; linarith
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num)
    (h.trans (ENNReal.ofReal_le_ofReal hbound))

end ZeroNoise

open ZeroNoise in
/-- Instance-level refutation core for **every** initialization `V₀` and every step parameter
`η₀ ∈ (0, 1]`: for any constants `c, C̃` (even chosen after the instance and `V₀`), some `T ≥ 1`
and the closed convex slab `{x : |x 0| ≤ 1/20}` violate the printed bound of Theorem 7.11. -/
theorem anyInit_violates (V₀ : Fin 2 → ℝ) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (c Ct : ℝ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∃ C : Set (Fin 2 → ℝ), Convex ℝ C ∧ IsClosed C ∧
      c * printedRate zMDP zMu (printedGamma zMDP zPolicy zMu) η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
          Ct * (T : ℝ) ^ (-(1 / 2 : ℝ)) <
        |lawProb zMDP zPolicy zMu η₀ V₀ T C -
          (gaussCov (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu)).real C| := by
  set a := c * printedRate zMDP zMu (printedGamma zMDP zPolicy zMu) η₀
  set D := (zLyap V₀ + 1) / 2 * (1440 / (3 * η₀ / 16) ^ 6) / (1 / 20)
  obtain ⟨T, hT, hlt⟩ := exists_rhs_lt_one (4 / 3 * a) (4 / 3 * (Ct + D))
  refine ⟨T, hT, zSlab (1 / 20), zSlab_convex _, zSlab_isClosed _, ?_⟩
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hsq : (Real.sqrt T)⁻¹ = (T : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hT0]
  have hP := zLawProb_slab_ge h0 h1 V₀ hT (ε := 1 / 20) (by norm_num)
  have hD : (Real.sqrt T)⁻¹ * ((zLyap V₀ + 1) / 2 * (1440 / (3 * η₀ / 16) ^ 6)) / (1 / 20) =
      D * (T : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hsq]; ring
  rw [hD] at hP
  have hG := zGauss_slab_le
  have hgap : 3 / 4 - D * (T : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      |lawProb zMDP zPolicy zMu η₀ V₀ T (zSlab (1 / 20)) -
        (gaussCov (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu)).real (zSlab (1 / 20))| :=
    le_trans (by linarith) (le_abs_self _)
  have hrhs : a * (T : ℝ) ^ (-(1 / 3 : ℝ)) + Ct * (T : ℝ) ^ (-(1 / 2 : ℝ)) <
      3 / 4 - D * (T : ℝ) ^ (-(1 / 2 : ℝ)) := by
    nlinarith
  linarith

open ZeroNoise in
/-- **Theorem 7.11 is false even for one initialization per instance, under `r(s) = r_π(s)` with
action-dependent rewards** (`thm:Berry-Esseen-linear`, `inference.tex:132–141`; SOURCE-ISSUES C43),
with universal `c` and closed convex sets: at instance Z with `η₀ = 1/8`, whatever `V₀` is chosen
(e.g. `V₀ = 0`), the printed bound fails. -/
theorem not_thm7_11_printed_someInit : ¬ Thm7_11_printed_someInit := by
  rintro ⟨c, -, h⟩
  obtain ⟨V₀, Ct, -, hT⟩ := h (Fin 2) (Fin 2) zMDP zPolicy zMu (1 / 8) zMu_pos (by norm_num)
    (by norm_num) zPrintedGamma_pos
  obtain ⟨T, hT1, C, hCv, hCc, hlt⟩ := anyInit_violates V₀ (η₀ := 1 / 8) (by norm_num)
    (by norm_num) c Ct
  exact absurd (hT T hT1 C hCv hCc) (not_le.2 hlt)

open ZeroNoise in
/-- The some-`V₀` reading with instance-wise constants `c, C̃` is false as well (check fix F3). -/
theorem not_thm7_11_printed_someInit_instWise : ¬ Thm7_11_printed_someInit_instWise := by
  intro h
  obtain ⟨V₀, c, -, Ct, -, hT⟩ := h (Fin 2) (Fin 2) zMDP zPolicy zMu (1 / 8) zMu_pos
    (by norm_num) (by norm_num) zPrintedGamma_pos
  obtain ⟨T, hT1, C, hCv, hCc, hlt⟩ := anyInit_violates V₀ (η₀ := 1 / 8) (by norm_num)
    (by norm_num) c Ct
  exact absurd (hT T hT1 C hCv hCc) (not_le.2 hlt)

open ZeroNoise in
/-- The weakest reading, with `η₀ ∈ (0, 1/4)`, `V₀` and `c, C̃` all chosen per instance, is false
too (critic O1), under `r(s) = r_π(s)` with action-dependent rewards. -/
theorem not_thm7_11_printed_someEta_someInit : ¬ Thm7_11_printed_someEta_someInit := by
  intro h
  obtain ⟨η₀, hη₀, hη₁, V₀, c, -, Ct, -, hT⟩ :=
    h (Fin 2) (Fin 2) zMDP zPolicy zMu zMu_pos zPrintedGamma_pos
  obtain ⟨T, hT1, C, hCv, hCc, hlt⟩ := anyInit_violates V₀ hη₀ (by linarith) c Ct
  exact absurd (hT T hT1 C hCv hCc) (not_le.2 hlt)

end StatisticalRL.Ch7Rest.TDInference
