import Formalization.Online.LowerBound.TestingTools

/-!
# Lemma 5.21: round-wise bandit testing lower bound

`lem:online-lb-testing` (`chapters/onlineRL.tex:2709–2721`, proof `:4938–5097`): for `A ≥ 3`,
`H ≥ 2`, `0 < ε₀ ≤ H/2` and every round `t ≤ H³A/(18ε₀²)`,
`inf_π̂ (1/A) ∑_i P_{B_i}(a_{t+1} ≠ i) ≥ 1/3`.

Proof (following the source): for a fixed seed the learner is a history-dependent randomized rule.
The KL divergence between the laws of `(x_t, a_{t+1})` under `B_1` (index `0`) and `B_i` equals that of
the histories `x_t` (`compLaw_finiteKLExpression`), which by the adaptive chain rule
(`eq:KL-factorize-bandit-lower-bound-online-proof`) is a sum of per-round reward KL divergences.
At each round only the alternative `i = a_τ` contributes, by at most `4ε₀²/H³`, so
`∑_{i ≥ 2} KL ≤ 4ε₀² t / H³ ≤ 2A/9`; reverse Fano (`lem:reverse-Fano-bound`) with the test `a_{t+1}`
gives `1 − 1/A − √((A−1)/(9A)) ≥ 1/3`. The seed is averaged at the end.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineLowerBound

open StatisticalRL AdaptiveKL GenerativeLowerBound

/-- Per-round KL: at arm `a`, the reward laws of `B_1` (index `0`) and of the alternatives
`B_{j+1}` differ only for `j + 1 = a`, by at most `4ε²/H³`. -/
theorem banditRow_sum_finiteKLExpression_le {H : ℕ} {ε : ℝ} (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {M : ℕ} (a : Fin (M + 1)) :
    ∑ j : Fin M, finiteKLExpression (banditRewardRow H ε hH hε hεH 0 a).prob
        (banditRewardRow H ε hH hε hεH j.succ a).prob ≤ 4 * ε ^ 2 / (H : ℝ) ^ 3 := by
  refine sum_succ_le_of_single a _ _ (by positivity) (fun j hj => ?_) (fun j _ => ?_)
  · have hrow : banditRewardRow H ε hH hε hεH 0 a = banditRewardRow H ε hH hε hεH j.succ a := by
      unfold banditRewardRow; simp_rw [onlineLBq_zero_eq_succ H ε j a hj]
    rw [hrow, AdaptiveKL.finiteKLExpression_self]
  · rw [banditRewardRow_finiteKLExpression]
    exact onlineLBq_bernoulliKL_le hH hε hεH _ _ _

/-- Lemma 5.21 for a learner without internal seed: a history-dependent randomized arm-selection rule
`π`. -/
theorem bandit_testing_policy (A H : ℕ) (hA : 3 ≤ A) (hH : 2 ≤ H) (ε : ℝ) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) (t : ℕ) (ht : (t : ℝ) ≤ (H : ℝ) ^ 3 * A / (18 * ε ^ 2))
    (π : (t : ℕ) → (Fin t → Fin A × Bool) → FiniteDistribution (Fin A)) :
    (1 : ℝ) / 3 ≤ (1 / (A : ℝ)) * ∑ i : Fin A,
      ∑ x, (compLaw (interactionLaw π (banditEnv H ε hH hε hεH i) t) (π t)).prob x *
        (if x.2 ≠ i then 1 else 0) := by
  obtain ⟨M, rfl⟩ : ∃ M, A = M + 1 := ⟨A - 1, by omega⟩
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  let d : Fin (M + 1) → FiniteDistribution ((Fin t → Fin (M + 1) × Bool) × Fin (M + 1)) :=
    fun j => compLaw (interactionLaw π (banditEnv H ε hH hε hεH j) t) (π t)
  have hacEnv : ∀ (j k : Fin (M + 1)) τ h a o,
      (banditEnv H ε hH hε hεH k τ h a).prob o = 0 → (banditEnv H ε hH hε hεH j τ h a).prob o = 0 :=
    fun j k τ h a o ho => absurd ho (banditRewardRow_pos hH hε hεH k a o).ne'
  have hac : ∀ (j : Fin M) x, (d j.succ).prob x = 0 → (d 0).prob x = 0 := fun j x =>
    compLaw_ac _ _ _ (interactionLaw_ac' π _ _ (hacEnv 0 j.succ) t) x
  set B : ℝ := t * (4 * ε ^ 2 / (H : ℝ) ^ 3) with hB
  have hB0 : 0 ≤ B := by positivity
  have hKL : ∑ j : Fin M, finiteKLExpression (d 0).prob (d j.succ).prob ≤ B := by
    have hrw : ∀ j : Fin M, finiteKLExpression (d 0).prob (d j.succ).prob =
        finiteKLExpression (interactionLaw π (banditEnv H ε hH hε hεH 0) t).prob
          (interactionLaw π (banditEnv H ε hH hε hεH j.succ) t).prob := fun j =>
      compLaw_finiteKLExpression _ _ _ (interactionLaw_ac' π _ _ (hacEnv 0 j.succ) t)
    have hδ : ∀ τ (h : Fin τ → Fin (M + 1) × Bool) (a : Fin (M + 1)),
        ∑ j : Fin M, finiteKLExpression (banditEnv H ε hH hε hεH 0 τ h a).prob
          (banditEnv H ε hH hε hεH j.succ τ h a).prob ≤ 4 * ε ^ 2 / (H : ℝ) ^ 3 :=
      fun τ h a => banditRow_sum_finiteKLExpression_le hH hε hεH a
    have hsum := interactionLaw_sum_finiteKLExpression_le (J := Fin M) π
      (banditEnv H ε hH hε hεH 0) (fun j => banditEnv H ε hH hε hεH j.succ)
      (fun j => hacEnv 0 j.succ) t (4 * ε ^ 2 / (H : ℝ) ^ 3) hδ
    rw [Finset.sum_congr rfl fun j _ => hrw j]
    exact hsum
  have hBle : B ≤ 2 * ((M : ℝ) + 1) / 9 := by
    have h := mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ 4 * ε ^ 2 / (H : ℝ) ^ 3)
    refine h.trans_eq ?_
    push_cast
    field_simp
    ring
  have hfano := finite_reverseFano M d (fun x => x.2) hac B hB0 hKL
  have hthird := fano_third M (by omega) B hBle
  push_cast
  exact hthird.trans hfano

/-- **Lemma 5.21** (`lem:online-lb-testing`, `chapters/onlineRL.tex:2709–2721`): for every online
bandit algorithm (possibly using an internal random seed), the average over the `A` instances of the
probability that the arm chosen after `t ≤ H³A/(18ε₀²)` rounds is suboptimal is at least `1/3`. -/
theorem bandit_testing (A H : ℕ) (hA : 3 ≤ A) (hH : 2 ≤ H) (ε : ℝ) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) (t : ℕ) (ht : (t : ℝ) ≤ (H : ℝ) ^ 3 * A / (18 * ε ^ 2))
    (L : BanditLearner A) :
    (1 : ℝ) / 3 ≤ (1 / (A : ℝ)) * ∑ i : Fin A, banditNextArmErrorProb L H ε hH hε hεH i t := by
  unfold banditNextArmErrorProb
  rw [Finset.sum_comm, Finset.mul_sum]
  calc (1 : ℝ) / 3 = ∑ σ, L.seedLaw.prob σ * (1 / 3) := by
        rw [← Finset.sum_mul, L.seedLaw.sum_prob, one_mul]
    _ ≤ ∑ σ, 1 / (A : ℝ) * ∑ i : Fin A, L.seedLaw.prob σ *
          ∑ x, (compLaw (interactionLaw (L.policy σ) (banditEnv H ε hH hε hεH i) t)
            (L.policy σ t)).prob x * (if x.2 ≠ i then 1 else 0) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [← Finset.mul_sum, mul_left_comm]
        exact mul_le_mul_of_nonneg_left
          (bandit_testing_policy A H hA hH ε hε hεH t ht (L.policy σ)) (L.seedLaw.prob_nonneg σ)

end StatisticalRL.OnlineLowerBound
