import Formalization.ModelFree.QLearningLowerBoundAuxMoments

/-!
# Second and fourth moments of `ζ_t = ξ_t(1) - ξ_t(2)`

`chapters/generative_model_model_free.tex:3707–3730` defines the martingale sum
`ζ_t = ∑_{k=1}^t η(1-η)^{t-k} γ (P_k(1∣1,1) - P_k(1∣1,2)) V̂_{k-1}`.
Here its partial sums `S_n` (`n ≤ t`, weights fixed by `t`) are tracked through the product law:
`E S_{n+1}² = E S_n² + c²·2p(1-p)·E V̂_n²` and a fourth-moment recursion.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-- Partial sums of `ζ_t`: `S_n = ∑_{k=1}^n η(1-η)^{t-k} γ D_k V̂_{k-1}`. -/
noncomputable def qLbZetaPartial (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) (t n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, η * (1 - η) ^ (t - k) * γ *
    qLbD (samples k 1 false) (samples k 1 true) * qLbAuxValue γ η samples (k - 1)

theorem qLbXi_sub (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) :
    qLbXi γ η samples t false - qLbXi γ η samples t true = qLbZetaPartial γ η samples t t := by
  unfold qLbXi qLbZetaPartial
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [qLbD, qLbInd, qLbStay]
  ring

theorem qLbZetaPartial_succ (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) (t n : ℕ) :
    qLbZetaPartial γ η samples t (n + 1) = qLbZetaPartial γ η samples t n +
      (η * (1 - η) ^ (t - (n + 1)) * γ) * qLbAuxValue γ η samples n *
        qLbD (samples (n + 1) 1 false) (samples (n + 1) 1 true) := by
  unfold qLbZetaPartial
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Nat.add_sub_cancel]
  ring

theorem qLbZetaPartial_congr (γ η : ℝ) (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ)
    (h : qLbAgree1 s s' n) (t m : ℕ) (hm : m ≤ n) :
    qLbZetaPartial γ η s t m = qLbZetaPartial γ η s' t m := by
  unfold qLbZetaPartial
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
  rw [h k hk1 (by omega) false, h k hk1 (by omega) true,
    qLbAuxValue_congr γ η s s' n h (k - 1) (by omega)]

section Moments
variable (M : DiscountedMDP (Fin 4) Bool) (N : ℕ) (γ η : ℝ)

/-- `E[F·D^j] = E[F]·E[D^j]` for `F` a function of the draws at times `≤ n`. -/
theorem qLb_integral_mul_Dpow (n : ℕ) (F : QSamples (Fin 4) Bool N → ℝ)
    (hF : ∀ d d', qLbAgree1 (qSamplesExtend M N d) (qSamplesExtend M N d') n → F d = F d')
    (j : ℕ) :
    ∫ d, F d * qLbD (qSamplesExtend M N d (n + 1) 1 false)
        (qSamplesExtend M N d (n + 1) 1 true) ^ j ∂qSamplingLaw M N =
      (∫ d, F d ∂qSamplingLaw M N) *
        ∫ d, qLbD (qSamplesExtend M N d (n + 1) 1 false)
          (qSamplesExtend M N d (n + 1) 1 true) ^ j ∂qSamplingLaw M N :=
  qLb_integral_mul_state1 M N n F hF (fun x y ↦ qLbD x y ^ j)

/-- Exact second-moment recursion. -/
theorem qLb_zeta_sq_succ (hrow : qLbRowSpec M (qHardP γ)) (t n : ℕ) (hn : n + 1 ≤ N) :
    ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t (n + 1) ^ 2 ∂qSamplingLaw M N =
      ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 ∂qSamplingLaw M N +
        (η * (1 - η) ^ (t - (n + 1)) * γ) ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) *
          ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N := by
  set c := η * (1 - η) ^ (t - (n + 1)) * γ
  have hpt : ∀ d : QSamples (Fin 4) Bool N,
      qLbZetaPartial γ η (qSamplesExtend M N d) t (n + 1) ^ 2 =
        qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 +
        (2 * c) * ((qLbZetaPartial γ η (qSamplesExtend M N d) t n *
          qLbAuxValue γ η (qSamplesExtend M N d) n) *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 1) +
        c ^ 2 * (qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2 *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 2) := by
    intro d; rw [qLbZetaPartial_succ]; ring
  simp_rw [hpt]
  rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_const_mul, integral_const_mul,
    qLb_integral_mul_Dpow M N n _ (fun d d' h ↦ by
      simp only [qLbZetaPartial_congr γ η _ _ n h t n le_rfl, qLbAuxValue_congr γ η _ _ n h n le_rfl]) 1,
    qLb_integral_mul_Dpow M N n _ (fun d d' h ↦ by
      simp only [qLbAuxValue_congr γ η _ _ n h n le_rfl]) 2]
  simp_rw [pow_one]
  rw [qLb_integral_D M N γ hrow (n + 1) (by omega) hn,
    qLb_integral_D_sq M N γ hrow (n + 1) (by omega) hn]
  ring

/-- Exact fourth-moment recursion (odd moments of `D` vanish, `D³ = D`, `D⁴ = D²`). -/
theorem qLb_zeta_four_succ (hrow : qLbRowSpec M (qHardP γ)) (t n : ℕ) (hn : n + 1 ≤ N) :
    ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t (n + 1) ^ 4 ∂qSamplingLaw M N =
      ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 4 ∂qSamplingLaw M N +
        6 * (η * (1 - η) ^ (t - (n + 1)) * γ) ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) *
          ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 *
            qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N +
        (η * (1 - η) ^ (t - (n + 1)) * γ) ^ 4 * (2 * (qHardP γ * (1 - qHardP γ))) *
          ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) n ^ 4 ∂qSamplingLaw M N := by
  set c := η * (1 - η) ^ (t - (n + 1)) * γ
  have hpt : ∀ d : QSamples (Fin 4) Bool N,
      qLbZetaPartial γ η (qSamplesExtend M N d) t (n + 1) ^ 4 =
        qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 4 +
        (4 * c) * ((qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 3 *
          qLbAuxValue γ η (qSamplesExtend M N d) n) *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 1) +
        (6 * c ^ 2) * ((qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 *
          qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2) *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 2) +
        (4 * c ^ 3) * ((qLbZetaPartial γ η (qSamplesExtend M N d) t n *
          qLbAuxValue γ η (qSamplesExtend M N d) n ^ 3) *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 1) +
        c ^ 4 * (qLbAuxValue γ η (qSamplesExtend M N d) n ^ 4 *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 2) := by
    intro d
    rw [qLbZetaPartial_succ]
    have h3 := qLbD_cube (qSamplesExtend M N d (n + 1) 1 false) (qSamplesExtend M N d (n + 1) 1 true)
    have h4 := qLbD_four (qSamplesExtend M N d (n + 1) 1 false) (qSamplesExtend M N d (n + 1) 1 true)
    set D := qLbD (qSamplesExtend M N d (n + 1) 1 false) (qSamplesExtend M N d (n + 1) 1 true)
    set S := qLbZetaPartial γ η (qSamplesExtend M N d) t n
    set V := qLbAuxValue γ η (qSamplesExtend M N d) n
    have e : (S + c * V * D) ^ 4 = S ^ 4 + 4 * c * S ^ 3 * V * D + 6 * c ^ 2 * S ^ 2 * V ^ 2 * D ^ 2
        + 4 * c ^ 3 * S * V ^ 3 * D ^ 3 + c ^ 4 * V ^ 4 * D ^ 4 := by ring
    rw [e, h3, h4]
    ring
  have hS : ∀ m, m ≤ n → ∀ d d' : QSamples (Fin 4) Bool N,
      qLbAgree1 (qSamplesExtend M N d) (qSamplesExtend M N d') n →
      qLbZetaPartial γ η (qSamplesExtend M N d) t m =
        qLbZetaPartial γ η (qSamplesExtend M N d') t m :=
    fun m hm d d' h ↦ qLbZetaPartial_congr γ η _ _ n h t m hm
  have hV : ∀ d d' : QSamples (Fin 4) Bool N,
      qLbAgree1 (qSamplesExtend M N d) (qSamplesExtend M N d') n →
      qLbAuxValue γ η (qSamplesExtend M N d) n = qLbAuxValue γ η (qSamplesExtend M N d') n :=
    fun d d' h ↦ qLbAuxValue_congr γ η _ _ n h n le_rfl
  simp_rw [hpt]
  rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    qLb_integral_mul_Dpow M N n
      (fun d ↦ qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 3 *
        qLbAuxValue γ η (qSamplesExtend M N d) n)
      (fun d d' h ↦ by simp only [hS n le_rfl d d' h, hV d d' h]) 1,
    qLb_integral_mul_Dpow M N n
      (fun d ↦ qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 *
        qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2)
      (fun d d' h ↦ by simp only [hS n le_rfl d d' h, hV d d' h]) 2,
    qLb_integral_mul_Dpow M N n
      (fun d ↦ qLbZetaPartial γ η (qSamplesExtend M N d) t n *
        qLbAuxValue γ η (qSamplesExtend M N d) n ^ 3)
      (fun d d' h ↦ by simp only [hS n le_rfl d d' h, hV d d' h]) 1,
    qLb_integral_mul_Dpow M N n
      (fun d ↦ qLbAuxValue γ η (qSamplesExtend M N d) n ^ 4)
      (fun d d' h ↦ by simp only [hV d d' h]) 2]
  simp_rw [pow_one]
  rw [qLb_integral_D M N γ hrow (n + 1) (by omega) hn,
    qLb_integral_D_sq M N γ hrow (n + 1) (by omega) hn]
  ring

end Moments

end StatisticalRL.QLearning
