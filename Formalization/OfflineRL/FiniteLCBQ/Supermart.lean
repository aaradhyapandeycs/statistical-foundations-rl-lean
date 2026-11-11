import Formalization.OfflineRL.FiniteLCBQ.Recursion
import Formalization.OfflineRL.FiniteVILCB.CountEvents
import Formalization.Probability.AzumaScalarChord
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential supermartingale on the finite product of trajectories (Step 2, lemma G)

On `Fin K → α` with the product weights `∏_k p(x_k)`: if `U_k(x)` depends only on `x_{≤k}` and
`Σ_a p(a) exp U_k(x[k ↦ a]) ≤ 1` for every `x`, then `Σ_x ∏ p · exp(Σ_k U_k) ≤ 1`, hence
`Σ_x ∏ p · 1{Σ_k U_k ≥ t} ≤ e^{-t}`. Also: the product law of `K` iid trajectories as finite
sums, the transfer from an abstract probability space, and the stage-triple law.
-/

namespace StatisticalRL.LCBQFinite

open Finset MeasureTheory ProbabilityTheory StatisticalRL.FiniteVILCB

section Generic

variable {α : Type*} [Fintype α] (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
include hp0 hp1

/-- **Lemma G**. -/
theorem lemmaG : ∀ (K : ℕ) (U : Fin K → (Fin K → α) → ℝ),
    (∀ k x y, (∀ j : Fin K, j ≤ k → x j = y j) → U k x = U k y) →
    (∀ k x, ∑ a, p a * Real.exp (U k (Function.update x k a)) ≤ 1) →
    ∑ x : Fin K → α, (∏ j, p (x j)) * Real.exp (∑ k, U k x) ≤ 1 := by
  intro K
  induction K with
  | zero => intro U _ _; simp
  | succ K ih =>
    intro U hdep hstep
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
    · simp
    let e := Fin.snocEquiv (fun _ : Fin (K + 1) ↦ α)
    rw [← e.sum_comp, Fintype.sum_prod_type, sum_comm]
    let U' : Fin K → (Fin K → α) → ℝ := fun k y ↦ U k.castSucc (Fin.snoc y a₀)
    have hU' : ∀ k (y : Fin K → α) a, U k.castSucc (Fin.snoc y a) = U' k y := by
      intro k y a
      refine hdep _ _ _ fun j hj ↦ ?_
      have hj' : j ≠ Fin.last K := by
        intro h; subst h
        exact absurd hj (not_le.2 (Fin.castSucc_lt_last k))
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
      simp
    have hdep' : ∀ k x y, (∀ j : Fin K, j ≤ k → x j = y j) → U' k x = U' k y := by
      intro k x y hxy
      refine hdep _ _ _ fun j hj ↦ ?_
      by_cases hj' : j = Fin.last K
      · subst hj'; simp
      · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
        simp only [Fin.snoc_castSucc]
        exact hxy i (Fin.castSucc_le_castSucc_iff.1 hj)
    have hstep' : ∀ k x, ∑ a, p a * Real.exp (U' k (Function.update x k a)) ≤ 1 := by
      intro k x
      have := hstep k.castSucc (Fin.snoc x a₀)
      refine le_trans (le_of_eq ?_) this
      refine sum_congr rfl fun a _ ↦ ?_
      simp only [U', Fin.snoc_update]
    have hih := ih U' hdep' hstep'
    refine le_trans (sum_le_sum fun y _ ↦ ?_) hih
    have hlast := hstep (Fin.last K) (Fin.snoc y a₀)
    simp only [Fin.update_snoc_last] at hlast
    have hP : 0 ≤ (∏ j : Fin K, p (y j)) * Real.exp (∑ k, U' k y) :=
      mul_nonneg (prod_nonneg fun j _ ↦ hp0 _) (Real.exp_pos _).le
    have hfac : ∀ a, (∏ j, p (Fin.snoc (α := fun _ ↦ α) y a j)) *
        Real.exp (∑ k, U k (Fin.snoc (α := fun _ ↦ α) y a)) =
        ((∏ j : Fin K, p (y j)) * Real.exp (∑ k, U' k y)) *
          (p a * Real.exp (U (Fin.last K) (Fin.snoc y a))) := by
      intro a
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, Real.exp_add]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hU']
      ring
    show ∑ a, (∏ j, p (Fin.snoc (α := fun _ ↦ α) y a j)) *
        Real.exp (∑ k, U k (Fin.snoc (α := fun _ ↦ α) y a)) ≤ _
    rw [sum_congr rfl fun a _ ↦ hfac a, ← mul_sum]
    calc _ ≤ ((∏ j : Fin K, p (y j)) * Real.exp (∑ k, U' k y)) * 1 :=
          mul_le_mul_of_nonneg_left hlast hP
      _ = _ := mul_one _

/-- **Markov** consequence of lemma G. -/
theorem markovG (K : ℕ) (U : Fin K → (Fin K → α) → ℝ)
    (hdep : ∀ k x y, (∀ j : Fin K, j ≤ k → x j = y j) → U k x = U k y)
    (hstep : ∀ k x, ∑ a, p a * Real.exp (U k (Function.update x k a)) ≤ 1) (t : ℝ) :
    ∑ x : Fin K → α, (∏ j, p (x j)) * (if t ≤ ∑ k, U k x then 1 else 0) ≤ Real.exp (-t) := by
  have hG := lemmaG p hp0 hp1 K U hdep hstep
  calc _ ≤ ∑ x : Fin K → α, (∏ j, p (x j)) * (Real.exp (∑ k, U k x) * Real.exp (-t)) := by
        refine sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun j _ ↦ hp0 _)
        split_ifs with h
        · rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
        · positivity
    _ = (∑ x : Fin K → α, (∏ j, p (x j)) * Real.exp (∑ k, U k x)) * Real.exp (-t) := by
        rw [sum_mul]; refine sum_congr rfl fun x _ ↦ by ring
    _ ≤ 1 * Real.exp (-t) := mul_le_mul_of_nonneg_right hG (Real.exp_pos _).le
    _ = _ := one_mul _

omit hp0 in
theorem sum_prod_eq_one (K : ℕ) : ∑ x : Fin K → α, ∏ j, p (x j) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin K) a ↦ p a)]
  simp [hp1]

end Generic

/-! ## Trajectory specialisation -/

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance smDecS : DecidableEq S := Classical.decEq S
noncomputable local instance smDecA : DecidableEq A := Classical.decEq A
local instance smMT (H : ℕ) : MeasurableSpace (Traj S A H) := ⊤

variable {H : ℕ} (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
  (ρb : FiniteDistribution S)

/-- **Stage-triple law**: `E[φ(s_h, a_h, s_{h+1})] = Σ_{s,a} d^b_h(s,a) Σ_{s'} P_h(s'|s,a) φ(s,a,s')`. -/
theorem sum_traj_triple (h : Fin H) (φ : S → A → S → ℝ) :
    ∑ τ, trajProb E πb ρb τ * φ (τ.1 h.castSucc) (τ.2 h) (τ.1 h.succ) =
      ∑ s, ∑ a, occupancy E πb ρb h s a * ∑ s', ((E h).transition s a).prob s' * φ s a s' := by
  rw [sum_traj_step, ← sum_stateMarg E πb ρb h.castSucc]
  refine sum_congr rfl fun s _ ↦ ?_
  unfold stepExp
  rw [mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [occupancy_eq]; ring

/-- The product law of `K` iid trajectories, as finite sums. -/
theorem pi_real_eq_sum {K : ℕ} (P : (Fin K → Traj S A H) → Prop) [DecidablePred P] :
    (Measure.pi (fun _ : Fin K ↦ trajMeasure E πb ρb)).real {x | P x} =
      ∑ x : Fin K → Traj S A H, (∏ j, trajProb E πb ρb (x j)) * (if P x then 1 else 0) := by
  classical
  have hsing : ∀ x : Fin K → Traj S A H,
      (Measure.pi (fun _ : Fin K ↦ trajMeasure E πb ρb)) {x} =
        ENNReal.ofReal (∏ j, trajProb E πb ρb (x j)) := by
    intro x
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    rw [ENNReal.ofReal_prod_of_nonneg fun j _ ↦ trajProb_nonneg E πb ρb (x j)]
    refine prod_congr rfl fun j _ ↦ ?_
    have := trajMeasure_apply_toReal E πb ρb (fun τ ↦ τ = x j)
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true,
      Set.setOf_eq_eq_singleton] at this
    rw [← this, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hset : {x | P x} = ((univ.filter P : Finset (Fin K → Traj S A H)) : Set _) := by
    ext x; simp
  rw [measureReal_def, hset, ← sum_measure_singleton, ENNReal.toReal_sum (fun x _ ↦ by
    rw [hsing]; exact ENNReal.ofReal_ne_top)]
  rw [sum_filter]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [hsing, ENNReal.toReal_ofReal (prod_nonneg fun j _ ↦ trajProb_nonneg E πb ρb (x j))]
  split_ifs <;> simp

/-- **Data transfer** for `K` iid trajectories. -/
theorem data_transfer' {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → Fin K → Traj S A H) (hX : Measurable X)
    (hind : iIndepFun (fun k ω ↦ X ω k) μ)
    (hlaw : ∀ k, μ.map (fun ω ↦ X ω k) = trajMeasure E πb ρb) (P : (Fin K → Traj S A H) → Prop)
    [DecidablePred P] :
    μ.real {ω | P (X ω)} =
      ∑ x : Fin K → Traj S A H, (∏ j, trajProb E πb ρb (x j)) * (if P x then 1 else 0) := by
  have hmeas : ∀ k, AEMeasurable (fun ω ↦ X ω k) μ :=
    fun k ↦ ((measurable_pi_apply k).comp hX).aemeasurable
  have hpi : μ.map X = Measure.pi (fun _ : Fin K ↦ trajMeasure E πb ρb) := by
    have := (iIndepFun_iff_map_fun_eq_pi_map hmeas).mp hind
    rw [show (fun ω k ↦ X ω k) = X from rfl] at this
    rw [this]
    congr 1
    funext k
    exact hlaw k
  have hset : {ω | P (X ω)} = X ⁻¹' {x | P x} := rfl
  rw [hset, ← map_measureReal_apply hX (Set.to_countable _).measurableSet, hpi, pi_real_eq_sum]

end StatisticalRL.LCBQFinite
