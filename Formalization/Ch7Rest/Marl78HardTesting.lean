import Formalization.Ch7Rest.Marl78Hard
import Formalization.Ch7Rest.Marl78Testing

/-!
# Corrected Theorem 7.8: adaptive testing for one coordinate of the hard family

For a coordinate `c = (x, h)` and a background parameter `θ`, the hypotheses `θ[c ↦ b]` differ only
in the generative model's answers to queries at state `x`, step `h + 1` with `a_istar` in the
changed positions. With the adaptive KL chain rule (`OnlineLowerBound.interactionLaw_finiteKLExpression`)
the history KL between `θ[c ↦ ref]` and `θ[c ↦ j]` is at most `κ` times the expected number of
queries at `(c, a_istar = j)` under `θ[c ↦ ref]`, `κ = 4λ²/H³`. `coord_bayes_le` then bounds the
prior-weighted success probability of the events `hit_b = {σ̂_c(b) > 1/2}`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL OnlineLowerBound AdaptiveKL GenerativeLowerBound

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- The coordinate `(state, step index)` of a query. -/
def qCoord (q : Query m S H A) : Fin S × Fin H := (q.2.1, q.1)

/-- Expected number of queries at coordinate `c` under the history law `P`. -/
noncomputable def expCount {N : ℕ} (P : FiniteDistribution (Fin N → Query m S H A × Fin S))
    (c : Fin S × Fin H) : ℝ :=
  ∑ hist, P.prob hist * ∑ t : Fin N, (if qCoord (hist t).1 = c then (1 : ℝ) else 0)

theorem expCount_nonneg {N : ℕ} (P : FiniteDistribution (Fin N → Query m S H A × Fin S))
    (c : Fin S × Fin H) : 0 ≤ expCount P c :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (P.prob_nonneg _)
    (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)

theorem sum_expCount {N : ℕ} (P : FiniteDistribution (Fin N → Query m S H A × Fin S)) :
    ∑ c, expCount P c = N := by
  unfold expCount
  rw [Finset.sum_comm]
  have : ∀ hist : Fin N → Query m S H A × Fin S,
      ∑ c, P.prob hist * ∑ t : Fin N, (if qCoord (hist t).1 = c then (1 : ℝ) else 0) =
        P.prob hist * N := by
    intro hist
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp
  simp_rw [this]
  rw [← Finset.sum_mul, P.sum_prob, one_mul]

section HardTesting

variable {istar : Fin m} {z : Fin S} {hH : 2 ≤ H} {lam : ℝ} {hl : 0 < lam}
  {hlH : lam ≤ (H : ℝ) / 2}

/-- Two reference/needle exit tables agree off the needle. -/
theorem onlineLBq_ref_eq {n : ℕ} (ref j b : Fin n) (href : (ref : ℕ) = 0) (hj : j ≠ ref)
    (hb : b ≠ j) : onlineLBq H lam ref b = onlineLBq H lam j b := by
  have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext (h.trans href.symm))
  unfold onlineLBq
  simp only [href, ne_eq, not_true_eq_false, if_false, hj0, not_false_eq_true, if_true, hb]
  by_cases hbr : b = ref
  · subst hbr; simp [href]
  · have : (b : ℕ) ≠ 0 := fun h => hbr (Fin.ext (h.trans href.symm))
    simp [hbr, this]

theorem genEnv_hard (cst : ℝ) (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (θ : Fin S × Fin H → Fin (A istar)) (t : ℕ) (hist : Fin t → Query m S H A × Fin S)
    (q : Query m S H A) :
    genEnv (hardGame istar z hH lam hl hlH cst rest θ) t hist q =
      hardTrans istar z hH lam hl hlH θ ((q.1 : ℕ) + 1) q.2.1 q.2.2 := rfl

theorem hard_env_ac (cst : ℝ) (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (θ θ' : Fin S × Fin H → Fin (A istar)) (t : ℕ) (hist : Fin t → Query m S H A × Fin S)
    (q : Query m S H A) (o : Fin S) :
    (genEnv (hardGame istar z hH lam hl hlH cst rest θ') t hist q).prob o = 0 →
      (genEnv (hardGame istar z hH lam hl hlH cst rest θ) t hist q).prob o = 0 := by
  rw [genEnv_hard, genEnv_hard]
  unfold hardTrans
  by_cases hs : q.2.1 = z
  · simp [hs]
  · simp only [hs, dite_false, exitRow]
    have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
    have hb := onlineLBq_bounds hH hl hlH (θ' (q.2.1, stepIdx hH ((q.1 : ℕ) + 1))) (q.2.2 istar)
    have h2H : 0 < 1 / (2 * (H : ℝ)) := by positivity
    have hhalf : 1 / (H : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    unfold exitQ
    split_ifs <;> intro h0 <;> first | rfl | linarith

theorem hard_trans_prob_eq (θ θ' : Fin S × Fin H → Fin (A istar)) (h : ℕ) (s : Fin S)
    (a : (i : Fin m) → Fin (A i))
    (he : exitQ istar hH lam θ h s (a istar) = exitQ istar hH lam θ' h s (a istar)) :
    (hardTrans istar z hH lam hl hlH θ h s a).prob = (hardTrans istar z hH lam hl hlH θ' h s a).prob := by
  unfold hardTrans
  by_cases hs : s = z
  · simp [hs]
  · simp only [hs, dite_false, exitRow, he]

/-- Per-query KL between the reference and the `j`-needle at coordinate `c`. -/
theorem hard_step_kl_le (cst : ℝ) (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (θ : Fin S × Fin H → Fin (A istar)) (c : Fin S × Fin H) (ref j : Fin (A istar))
    (href : (ref : ℕ) = 0) (hj : j ≠ ref) (t : ℕ) (hist : Fin t → Query m S H A × Fin S)
    (q : Query m S H A) :
    finiteKLExpression
        (genEnv (hardGame istar z hH lam hl hlH cst rest (Function.update θ c ref)) t hist q).prob
        (genEnv (hardGame istar z hH lam hl hlH cst rest (Function.update θ c j)) t hist q).prob ≤
      4 * lam ^ 2 / (H : ℝ) ^ 3 *
        (if qCoord q = c ∧ q.2.2 istar = j then 1 else 0) := by
  have hκ : 0 ≤ 4 * lam ^ 2 / (H : ℝ) ^ 3 := by positivity
  rw [genEnv_hard, genEnv_hard]
  have hidx : stepIdx hH ((q.1 : ℕ) + 1) = q.1 := stepIdx_succ hH q.1
  by_cases hmatch : qCoord q = c ∧ q.2.2 istar = j
  · rw [if_pos hmatch, mul_one]
    obtain ⟨hc, hb⟩ := hmatch
    by_cases hs : q.2.1 = z
    · have : (hardTrans istar z hH lam hl hlH (Function.update θ c ref) ((q.1 : ℕ) + 1) q.2.1 q.2.2).prob =
          (hardTrans istar z hH lam hl hlH (Function.update θ c j) ((q.1 : ℕ) + 1) q.2.1 q.2.2).prob := by
        unfold hardTrans; simp [hs]
      rw [this, finiteKLExpression_self]; exact hκ
    · unfold hardTrans
      simp only [hs, dite_false]
      rw [exitRow_finiteKLExpression]
      unfold exitQ
      rw [hidx]
      have hc' : (q.2.1, q.1) = c := hc
      rw [hc', Function.update_self, Function.update_self, hb]
      exact onlineLBq_bernoulliKL_le hH hl hlH ref j j
  · rw [if_neg hmatch, mul_zero]
    have heq : exitQ istar hH lam (Function.update θ c ref) ((q.1 : ℕ) + 1) q.2.1 (q.2.2 istar) =
        exitQ istar hH lam (Function.update θ c j) ((q.1 : ℕ) + 1) q.2.1 (q.2.2 istar) := by
      unfold exitQ
      rw [hidx]
      by_cases hc : (q.2.1, q.1) = c
      · rw [hc, Function.update_self, Function.update_self]
        have hb : q.2.2 istar ≠ j := fun hb => hmatch ⟨hc, hb⟩
        exact onlineLBq_ref_eq ref j _ href hj hb
      · rw [Function.update_of_ne hc, Function.update_of_ne hc]
    rw [hard_trans_prob_eq (hl := hl) (hlH := hlH) _ _ _ _ _ heq, finiteKLExpression_self]

/-- Expected number of queries at coordinate `c` with `a_istar = j`. -/
noncomputable def expCountJ {N : ℕ} (P : FiniteDistribution (Fin N → Query m S H A × Fin S))
    (c : Fin S × Fin H) (j : Fin (A istar)) : ℝ :=
  ∑ hist, P.prob hist * ∑ t : Fin N,
    (if qCoord (hist t).1 = c ∧ (hist t).1.2.2 istar = j then (1 : ℝ) else 0)

/-- History KL between the reference and the `j`-needle at `c`. -/
theorem hard_hist_kl_le (cst : ℝ) (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (θ : Fin S × Fin H → Fin (A istar)) (c : Fin S × Fin H) (ref j : Fin (A istar))
    (href : (ref : ℕ) = 0) (hj : j ≠ ref)
    (rule : (t : ℕ) → (Fin t → Query m S H A × Fin S) → FiniteDistribution (Query m S H A))
    (N : ℕ) :
    finiteKLExpression
        (interactionLaw rule (genEnv (hardGame istar z hH lam hl hlH cst rest
          (Function.update θ c ref))) N).prob
        (interactionLaw rule (genEnv (hardGame istar z hH lam hl hlH cst rest
          (Function.update θ c j))) N).prob ≤
      4 * lam ^ 2 / (H : ℝ) ^ 3 * expCountJ (istar := istar)
        (interactionLaw rule (genEnv (hardGame istar z hH lam hl hlH cst rest
          (Function.update θ c ref))) N) c j := by
  set e0 := genEnv (hardGame istar z hH lam hl hlH cst rest (Function.update θ c ref))
  set e1 := genEnv (hardGame istar z hH lam hl hlH cst rest (Function.update θ c j))
  set κ := 4 * lam ^ 2 / (H : ℝ) ^ 3
  rw [interactionLaw_finiteKLExpression rule e0 e1
    (fun t h a o => hard_env_ac cst rest _ _ t h a o) N]
  set g : (t : ℕ) → (Fin t → Query m S H A × Fin S) → Query m S H A → ℝ :=
    fun _ _ q => κ * (if qCoord q = c ∧ q.2.2 istar = j then 1 else 0)
  have hsteps := interactionLaw_sum_steps rule e0 N g
  have hrhs : κ * expCountJ (istar := istar) (interactionLaw rule e0 N) c j =
      ∑ hist, (interactionLaw rule e0 N).prob hist *
        ∑ t : Fin N, g t (fun i => hist (Fin.castLE t.isLt.le i)) (hist t).1 := by
    unfold expCountJ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun hist _ => ?_
    simp only [g]
    rw [← Finset.mul_sum]
    ring
  rw [hrhs, hsteps]
  refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun hist _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ ((interactionLaw rule e0 t).prob_nonneg hist)
  refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ?_ ((rule t hist).prob_nonneg q)
  exact hard_step_kl_le cst rest θ c ref j href hj t hist q

theorem sum_expCountJ_le {N : ℕ} (P : FiniteDistribution (Fin N → Query m S H A × Fin S))
    (c : Fin S × Fin H) (ref : Fin (A istar)) :
    ∑ j ∈ Finset.univ.erase ref, expCountJ (istar := istar) P c j ≤ expCount P c := by
  unfold expCountJ expCount
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun hist _ => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (P.prob_nonneg hist)
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  calc ∑ j ∈ Finset.univ.erase ref,
        (if qCoord (hist t).1 = c ∧ (hist t).1.2.2 istar = j then (1 : ℝ) else 0)
      ≤ ∑ j, (if qCoord (hist t).1 = c ∧ (hist t).1.2.2 istar = j then (1 : ℝ) else 0) :=
        Finset.sum_le_univ_sum_of_nonneg fun j => by split_ifs <;> norm_num
    _ = if qCoord (hist t).1 = c then 1 else 0 := by
        by_cases hc : qCoord (hist t).1 = c
        · simp [hc]
        · simp [hc]

/-- The event `σ̂_c(b) > 1/2` for the output joint policy: the `istar`-marginal at state `c.1`,
step `1 + c.2` gives probability more than `1/2` to `b`. -/
def hitEv {N : ℕ} (out : (Fin N → Query m S H A × Fin S) → JointPolicy m S A)
    (c : Fin S × Fin H) (b : Fin (A istar)) (hist : Fin N → Query m S H A × Fin S) : Prop :=
  1 / 2 < margProb (out hist (1 + (c.2 : ℕ)) c.1) istar b

noncomputable instance {N : ℕ} (out : (Fin N → Query m S H A × Fin S) → JointPolicy m S A)
    (c : Fin S × Fin H) (b : Fin (A istar)) : DecidablePred (hitEv out c b) := by
  unfold hitEv; infer_instance

/-- **One-coordinate testing bound for the hard family.** -/
theorem hard_coord_bayes (cst : ℝ) (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (hn : 2 ≤ A istar) (ref : Fin (A istar)) (href : (ref : ℕ) = 0)
    (rule : (t : ℕ) → (Fin t → Query m S H A × Fin S) → FiniteDistribution (Query m S H A))
    {N : ℕ} (out : (Fin N → Query m S H A × Fin S) → JointPolicy m S A)
    (θ : Fin S × Fin H → Fin (A istar)) (c : Fin S × Fin H) :
    ∑ b, wt ref b * evProb (interactionLaw rule (genEnv (hardGame istar z hH lam hl hlH cst rest
        (Function.update θ c b))) N) (hitEv out c b) ≤
      17 / 32 + 4 * lam ^ 2 / (H : ℝ) ^ 3 *
        expCount (interactionLaw rule (genEnv (hardGame istar z hH lam hl hlH cst rest
          (Function.update θ c ref))) N) c / ((A istar : ℝ) - 1) := by
  set P : Fin (A istar) → FiniteDistribution (Fin N → Query m S H A × Fin S) := fun b =>
    interactionLaw rule (genEnv (hardGame istar z hH lam hl hlH cst rest (Function.update θ c b))) N
  set κ := 4 * lam ^ 2 / (H : ℝ) ^ 3
  have hκ : 0 ≤ κ := by positivity
  have hn' : (2 : ℝ) ≤ A istar := by exact_mod_cast hn
  have hb := coord_bayes_le hn ref P (hitEv out c)
    (fun hist => sum_ite_half_lt_le_one _ (fun b => margProb_nonneg _ _ b) (sum_margProb _ _))
    (fun j x => interactionLaw_ac' rule _ _ (fun t h a o => hard_env_ac cst rest _ _ t h a o) N x)
    (fun j => κ * expCountJ (istar := istar) (P ref) c j)
    (fun j hj => hard_hist_kl_le cst rest θ c ref j href hj rule N)
  refine hb.trans ?_
  have hsum : ∑ j ∈ Finset.univ.erase ref, κ * expCountJ (istar := istar) (P ref) c j ≤
      κ * expCount (P ref) c := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_expCountJ_le (P ref) c ref) hκ
  have : (∑ j ∈ Finset.univ.erase ref, κ * expCountJ (istar := istar) (P ref) c j) /
      ((A istar : ℝ) - 1) ≤ κ * expCount (P ref) c / ((A istar : ℝ) - 1) :=
    div_le_div_of_nonneg_right hsum (by linarith)
  linarith

end HardTesting

end StatisticalRL.Ch7Rest.Marl
