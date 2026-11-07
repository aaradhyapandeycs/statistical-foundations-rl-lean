import Formalization.Online.LowerBound.HistoryKL

/-!
# Theorem 5.19: the online minimax regret lower bound

`thm:minimax-lower-online` (`chapters/onlineRL.tex:2443–2456`): for `S ≥ 2`, `A ≥ 3`, `H ≥ 2`,
`K ≥ 1` there are a finite family of horizon-`H` MDPs with `S` states and `A` actions and an initial
law `ρ` such that every online learner has expected regret at least `c₀ min{√(H³SAK), HK}` on some
member of the family, for a universal `c₀ > 0` (here `c₀ = 1/1536`).

Route (differs from the printed proof, `:2733–2935` and `:3005–3294`):

* the family is the general-`S` family of `:3020–3075` with `m = ⌊S/2⌋` copies; for odd `S` the
  remaining state is absorbing with reward `0` and initial mass `0` (the source assumes `S` even,
  `:3015`);
* Lemma 5.20 at each copy and `ρ` uniform on the copies bound the per-episode suboptimality by
  `(1/m) ∑_{j,h} ε(H−h)/(16H²)(1 − π^k_h(i_{j,h} | j))`;
* for each coordinate `(j, h)` and episode `k`, the coordinatewise testing bound (`HistoryKL`) with
  KL budget `4ε² k/(m H³)` gives an average error `≥ 1/3` once `ε² ≤ m A H³/(18K)`; this replaces the
  conditioning on the initial-state sequence and the binomial tail computation of `:3125–3285`
  (Cases 1 and 2), since the expected number of visits of copy `j` before episode `k` is `k/m`;
* with `ε = min{√(mAH³/(18K)), H/2}` the averaged regret is at least `Kε(H−1)/(96H) ≥ Kε/192`, and
  `m ≥ S/3` gives the stated rate.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineLowerBound

open StatisticalRL AdaptiveKL GenerativeLowerBound EnvironmentStage DecisionStage

section Helpers

theorem sum_fin_lt_eq (S m : ℕ) (hm : m ≤ S) (g : Fin S → ℝ) :
    ∑ s : Fin S, (if (s : ℕ) < m then g s else 0) = ∑ j : Fin m, g (Fin.castLE hm j) := by
  rw [← Finset.sum_filter]
  refine (Finset.sum_bij (fun (j : Fin m) _ => Fin.castLE hm j) (fun j _ => by simp)
    (fun a _ b _ hab => Fin.castLE_injective hm hab)
    (fun s hs => ⟨⟨s, by simpa using hs⟩, Finset.mem_univ _, rfl⟩) (fun j _ => rfl)).symm

theorem sum_prob_mul_ne {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (d : FiniteDistribution Ω)
    (a : Ω) : ∑ b, d.prob b * (if b ≠ a then 1 else 0) = 1 - d.prob a := by
  have : ∀ b, d.prob b * (if b ≠ a then 1 else 0) = d.prob b - (if b = a then d.prob b else 0) := by
    intro b; by_cases hb : b = a <;> simp [hb]
  simp_rw [this]
  rw [Finset.sum_sub_distrib, d.sum_prob, Finset.sum_ite_eq']
  simp

theorem compLaw_error {W Ω : Type*} [Fintype W] [Fintype Ω] [DecidableEq Ω]
    (P : FiniteDistribution W) (κ : W → FiniteDistribution Ω) (a : Ω) :
    ∑ x, (compLaw P κ).prob x * (if x.2 ≠ a then 1 else 0) = ∑ w, P.prob w * (1 - (κ w).prob a) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sum_prob_mul_ne (κ w) a, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  change P.prob w * (κ w).prob b * _ = _
  ring

/-- `∑_{h<H} ε(H − (h+1))/(16H²) = ε(H − 1)/(32H)`. -/
theorem sum_gap_weights (H : ℕ) (hH : 1 ≤ H) (ε : ℝ) :
    ∑ h : Fin H, ε * ((H : ℝ) - ((h : ℕ) + 1)) / (16 * (H : ℝ) ^ 2) =
      ε * ((H : ℝ) - 1) / (32 * H) := by
  have hgen : ∀ n : ℕ, ∑ h ∈ Finset.range n, ((H : ℝ) - ((h : ℝ) + 1)) =
      n * H - n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have h1 : ∑ h : Fin H, ε * ((H : ℝ) - ((h : ℕ) + 1)) / (16 * (H : ℝ) ^ 2) =
      (∑ h ∈ Finset.range H, ((H : ℝ) - ((h : ℝ) + 1))) * (ε / (16 * (H : ℝ) ^ 2)) := by
    have h0 := Fin.sum_univ_eq_sum_range
      (fun n : ℕ => ε * ((H : ℝ) - ((n : ℝ) + 1)) / (16 * (H : ℝ) ^ 2)) H
    simp only at h0
    rw [h0, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  rw [h1, hgen]
  field_simp
  ring

end Helpers

section Family

variable {S H M : ℕ} {ε : ℝ}

/-- The suboptimality of any policy in the general-`S` family is at least the `ρ`-average over the
copies of the Lemma 5.20 bound. -/
theorem policySuboptimality_ge (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    {A : ℕ} (i : Fin (S / 2) × Fin H → Fin A) (π : ℕ → StationaryPolicy (Fin S) (Fin A)) :
    ∑ jh : Fin (S / 2) × Fin H, (1 / ((S / 2 : ℕ) : ℝ)) *
        (ε * ((H : ℝ) - ((jh.2 : ℕ) + 1)) / (16 * (H : ℝ) ^ 2)) *
        (1 - (π jh.2 ⟨jh.1, by have := jh.1.isLt; omega⟩).prob (i jh)) ≤
      policySuboptimality (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS) π := by
  have hm : S / 2 ≤ S := Nat.div_le_self S 2
  unfold policySuboptimality
  have hrho : ∀ s : Fin S, (onlineLBRho S hS).prob s *
      (optimalValue (List.ofFn (onlineLBStages S H ε hS hH hε hεH i)) s -
        trajectoryValue (controlled (List.ofFn (onlineLBStages S H ε hS hH hε hεH i)) π) s) =
      if (s : ℕ) < S / 2 then (1 / ((S / 2 : ℕ) : ℝ)) *
        (optimalValue (List.ofFn (onlineLBStages S H ε hS hH hε hεH i)) s -
          trajectoryValue (controlled (List.ofFn (onlineLBStages S H ε hS hH hε hεH i)) π) s)
      else 0 := by
    intro s
    unfold onlineLBRho
    dsimp only
    split_ifs <;> ring
  simp_rw [hrho]
  rw [sum_fin_lt_eq S (S / 2) hm, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun j _ => ?_
  have hgap := onlineLBStages_value_gap S H A hS hH ε hε hεH i π j
  have hc : (0 : ℝ) ≤ 1 / ((S / 2 : ℕ) : ℝ) := by positivity
  calc ∑ h : Fin H, 1 / ((S / 2 : ℕ) : ℝ) * (ε * ((H : ℝ) - ((h : ℕ) + 1)) / (16 * (H : ℝ) ^ 2)) *
        (1 - (π h ⟨j, by have := j.isLt; omega⟩).prob (i (j, h)))
      = 1 / ((S / 2 : ℕ) : ℝ) * ∑ h : Fin H, ε * ((H : ℝ) - ((h : ℕ) + 1)) /
          (16 * (H : ℝ) ^ 2) * (1 - (π h ⟨j, by have := j.isLt; omega⟩).prob (i (j, h))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap hc

/-- **Coordinatewise testing** (`eq:coordinatewise-testing-lower-bound-online`, general `S`): with the
optimal actions off `(j, h)` fixed to `r`, the average over the `A = M + 1` values at `(j, h)` of the
probability that the counterfactual action `ã^k_h ∼ π^k_h(· | j)` misses `i_{j,h}` is at least `1/3`,
provided the KL budget `k · 4ε²/(⌊S/2⌋H³)` is at most `2A/9`. -/
theorem coordinate_testing (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    (hM : 2 ≤ M)
    (pol : (τ : ℕ) → (Fin τ → OnlineEpisode (Fin S) (Fin (M + 1)) H) →
      ℕ → StationaryPolicy (Fin S) (Fin (M + 1))) (k : ℕ)
    (hk : (k : ℝ) * (4 * ε ^ 2 / (H : ℝ) ^ 3 / ((S / 2 : ℕ) : ℝ)) ≤ 2 * ((M : ℝ) + 1) / 9)
    (j : Fin (S / 2)) (h : Fin H) (r : {c : Fin (S / 2) × Fin H // c ≠ (j, h)} → Fin (M + 1)) :
    (1 : ℝ) / 3 ≤ (1 / ((M : ℝ) + 1)) * ∑ a : Fin (M + 1),
      ∑ p, (hardHistoryLaw S H ε hS hH hε hεH
          ((Equiv.funSplitAt (j, h) (Fin (M + 1))).symm (a, r)) pol k).prob p *
        (1 - (pol k p h ⟨j, by have := j.isLt; omega⟩).prob a) := by
  classical
  set inst : Fin (M + 1) → Fin (S / 2) × Fin H → Fin (M + 1) :=
    fun a => (Equiv.funSplitAt (j, h) (Fin (M + 1))).symm (a, r) with hinst
  have hjh : ∀ a, inst a (j, h) = a := by
    intro a; simp [hinst, Equiv.funSplitAt, Equiv.piSplitAt]
  have hoff : ∀ a b c, c ≠ (j, h) → inst a c = inst b c := by
    intro a b c hc; simp [hinst, Equiv.funSplitAt, Equiv.piSplitAt, hc]
  set B : ℝ := (k : ℝ) * (4 * ε ^ 2 / (H : ℝ) ^ 3 / ((S / 2 : ℕ) : ℝ)) with hB
  have hB0 : 0 ≤ B := by positivity
  let jS : Fin S := ⟨j, by have := j.isLt; omega⟩
  let d : Fin (M + 1) → FiniteDistribution
      ((Fin k → OnlineEpisode (Fin S) (Fin (M + 1)) H) × Fin (M + 1)) :=
    fun a => compLaw (hardHistoryLaw S H ε hS hH hε hεH (inst a) pol k) (fun p => pol k p h jS)
  have hpathac : ∀ (a b : Fin (M + 1)) (π : ℕ → StationaryPolicy (Fin S) (Fin (M + 1))) s z,
      (episodePathLaw (onlineLBStages S H ε hS hH hε hεH (inst b)) π s).prob z = 0 →
        (episodePathLaw (onlineLBStages S H ε hS hH hε hεH (inst a)) π s).prob z = 0 :=
    fun a b π s z => interactionLaw_ac' _ _ _
      (fun t y c o => stepRow_onlineLBStages_ac hS hH hε hεH (inst a) (inst b) t _ o c) H z
  have hhistac : ∀ (a b : Fin (M + 1)) p,
      (hardHistoryLaw S H ε hS hH hε hεH (inst b) pol k).prob p = 0 →
        (hardHistoryLaw S H ε hS hH hε hεH (inst a) pol k).prob p = 0 :=
    fun a b => seqLaw_ac _ _ (fun τ q _ z hz => compLaw_ac_right _ _ _
      (fun s z => hpathac a b (pol τ q) s z) z hz) k
  have hac : ∀ (a' : Fin M) x, (d a'.succ).prob x = 0 → (d 0).prob x = 0 := fun a' x =>
    compLaw_ac _ _ _ (hhistac 0 a'.succ) x
  have hKL : ∑ a' : Fin M, finiteKLExpression (d 0).prob (d a'.succ).prob ≤ B := by
    have hrw : ∀ a' : Fin M, finiteKLExpression (d 0).prob (d a'.succ).prob =
        finiteKLExpression (hardHistoryLaw S H ε hS hH hε hεH (inst 0) pol k).prob
          (hardHistoryLaw S H ε hS hH hε hεH (inst a'.succ) pol k).prob := fun a' =>
      compLaw_finiteKLExpression _ _ _ (hhistac 0 a'.succ)
    rw [Finset.sum_congr rfl fun a' _ => hrw a']
    exact history_sum_KL_le hS hH hε hεH (inst 0) (fun a' => inst a'.succ) j h (hjh 0)
      (fun a' => hjh a'.succ) (fun a' c hc => hoff a'.succ 0 c hc) pol k
  have hfano := finite_reverseFano M d (fun x => x.2) hac B hB0 hKL
  have hthird := fano_third M hM B hk
  refine hthird.trans (hfano.trans_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  exact compLaw_error _ _ a

/-- Summing the coordinatewise bound over all instances: `∑_i E_i[1 − π^k_h(i_{j,h} | j)] ≥ |I|/3`. -/
theorem coordinate_sum_ge (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    (hM : 2 ≤ M)
    (pol : (τ : ℕ) → (Fin τ → OnlineEpisode (Fin S) (Fin (M + 1)) H) →
      ℕ → StationaryPolicy (Fin S) (Fin (M + 1))) (k : ℕ)
    (hk : (k : ℝ) * (4 * ε ^ 2 / (H : ℝ) ^ 3 / ((S / 2 : ℕ) : ℝ)) ≤ 2 * ((M : ℝ) + 1) / 9)
    (j : Fin (S / 2)) (h : Fin H) :
    (Fintype.card (Fin (S / 2) × Fin H → Fin (M + 1)) : ℝ) / 3 ≤
      ∑ i : Fin (S / 2) × Fin H → Fin (M + 1),
        ∑ p, (hardHistoryLaw S H ε hS hH hε hεH i pol k).prob p *
          (1 - (pol k p h ⟨j, by have := j.isLt; omega⟩).prob (i (j, h))) := by
  classical
  set e := Equiv.funSplitAt (j, h) (Fin (M + 1)) with he
  set F : (Fin (S / 2) × Fin H → Fin (M + 1)) → ℝ := fun i =>
    ∑ p, (hardHistoryLaw S H ε hS hH hε hεH i pol k).prob p *
      (1 - (pol k p h ⟨j, by have := j.isLt; omega⟩).prob (i (j, h))) with hF
  have hcard : (Fintype.card (Fin (S / 2) × Fin H → Fin (M + 1)) : ℝ) =
      ((M : ℝ) + 1) * Fintype.card ({c : Fin (S / 2) × Fin H // c ≠ (j, h)} → Fin (M + 1)) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin]
    push_cast; ring
  rw [← Equiv.sum_comp e.symm F, Fintype.sum_prod_type, Finset.sum_comm, hcard]
  have hrow : ∀ r : {c : Fin (S / 2) × Fin H // c ≠ (j, h)} → Fin (M + 1),
      ((M : ℝ) + 1) / 3 ≤ ∑ a : Fin (M + 1), F (e.symm (a, r)) := by
    intro r
    have hct := coordinate_testing hS hH hε hεH hM pol k hk j h r
    have hjh : ∀ a, e.symm (a, r) (j, h) = a := by
      intro a; simp [he, Equiv.funSplitAt, Equiv.piSplitAt]
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hsum : ∑ a : Fin (M + 1), F (e.symm (a, r)) = ∑ a : Fin (M + 1),
        ∑ p, (hardHistoryLaw S H ε hS hH hε hεH (e.symm (a, r)) pol k).prob p *
          (1 - (pol k p h ⟨j, by have := j.isLt; omega⟩).prob a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hF, hjh a]
    rw [hsum]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have := mul_le_mul_of_nonneg_left hct hpos.le
    rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] at this
    linarith
  calc ((M : ℝ) + 1) * (Fintype.card ({c : Fin (S / 2) × Fin H // c ≠ (j, h)} → Fin (M + 1)) : ℝ)
        / 3 = ∑ _r : {c : Fin (S / 2) × Fin H // c ≠ (j, h)} → Fin (M + 1), ((M : ℝ) + 1) / 3 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun r _ => hrow r

/-- **Averaged regret of the hard family.** If the KL budget after `K` episodes is at most `2A/9`,
then the sum over all instances of the expected regret is at least `|I| · K ε(H−1)/(96H)`. -/
theorem hard_family_sum_regret (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    (hM : 2 ≤ M) (K : ℕ)
    (hK : (K : ℝ) * (4 * ε ^ 2 / (H : ℝ) ^ 3 / ((S / 2 : ℕ) : ℝ)) ≤ 2 * ((M : ℝ) + 1) / 9)
    (L : OnlineLearner (Fin S) (Fin (M + 1)) H) :
    (Fintype.card (Fin (S / 2) × Fin H → Fin (M + 1)) : ℝ) *
        (K * (ε * ((H : ℝ) - 1) / (32 * H)) / 3) ≤
      ∑ i : Fin (S / 2) × Fin H → Fin (M + 1),
        onlineExpectedRegret (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS) L K := by
  classical
  set I := Fin (S / 2) × Fin H → Fin (M + 1)
  set C : ℝ := ε * ((H : ℝ) - 1) / (32 * H) with hC
  have hm0 : (0 : ℝ) < ((S / 2 : ℕ) : ℝ) := by
    have : 0 < S / 2 := by omega
    exact_mod_cast this
  -- the per-seed bound
  have hseed : ∀ σ : L.Seed, (Fintype.card I : ℝ) * (K * C / 3) ≤
      ∑ i : I, ∑ τ, (onlineHistoryLaw (onlineLBStages S H ε hS hH hε hεH i)
        (onlineLBRho S hS) L σ K).prob τ *
        ∑ k : Fin K, policySuboptimality (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS)
          (L.policy σ k (fun i => τ (Fin.castLE k.isLt.le i))) := by
    intro σ
    set pol := L.policy σ
    -- regret as a sum over episodes of prefix expectations
    have hdecomp : ∀ i : I, ∑ τ, (onlineHistoryLaw (onlineLBStages S H ε hS hH hε hεH i)
        (onlineLBRho S hS) L σ K).prob τ *
        ∑ k : Fin K, policySuboptimality (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS)
          (pol k (fun i => τ (Fin.castLE k.isLt.le i))) =
        ∑ k : Fin K, ∑ p, (hardHistoryLaw S H ε hS hH hε hεH i pol k).prob p *
          policySuboptimality (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS) (pol k p) := by
      intro i
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact seqLaw_sum_prefix _ k.isLt.le
        (fun p => policySuboptimality (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS)
          (pol k p))
    simp_rw [hdecomp]
    rw [Finset.sum_comm]
    -- each episode contributes at least `|I| C / 3`
    have hk : ∀ k : Fin K, (Fintype.card I : ℝ) * (C / 3) ≤
        ∑ i : I, ∑ p, (hardHistoryLaw S H ε hS hH hε hεH i pol k).prob p *
          policySuboptimality (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS) (pol k p) := by
      intro k
      have hkK : (k : ℝ) * (4 * ε ^ 2 / (H : ℝ) ^ 3 / ((S / 2 : ℕ) : ℝ)) ≤ 2 * ((M : ℝ) + 1) / 9 := by
        refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) hK
        exact_mod_cast k.isLt.le
      set w : Fin (S / 2) × Fin H → ℝ := fun jh => (1 / ((S / 2 : ℕ) : ℝ)) *
        (ε * ((H : ℝ) - ((jh.2 : ℕ) + 1)) / (16 * (H : ℝ) ^ 2)) with hw
      have hw0 : ∀ jh, 0 ≤ w jh := by
        intro jh
        have : ((jh.2 : ℕ) : ℝ) + 1 ≤ H := by exact_mod_cast jh.2.isLt
        have : (0 : ℝ) < H := by linarith
        simp only [hw]
        exact mul_nonneg (by positivity) (div_nonneg (mul_nonneg hε.le (by linarith)) (by positivity))
      calc (Fintype.card I : ℝ) * (C / 3)
          = ∑ jh : Fin (S / 2) × Fin H, w jh * ((Fintype.card I : ℝ) / 3) := by
            rw [← Finset.sum_mul, Fintype.sum_prod_type]
            simp only [hw]
            simp_rw [← Finset.mul_sum]
            rw [sum_gap_weights H (by omega) ε, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, hC]
            field_simp
        _ ≤ ∑ jh : Fin (S / 2) × Fin H, w jh * ∑ i : I, ∑ p,
              (hardHistoryLaw S H ε hS hH hε hεH i pol k).prob p *
              (1 - (pol k p jh.2 ⟨jh.1, by have := jh.1.isLt; omega⟩).prob (i jh)) :=
            Finset.sum_le_sum fun jh _ => mul_le_mul_of_nonneg_left
              (coordinate_sum_ge hS hH hε hεH hM pol k hkK jh.1 jh.2) (hw0 jh)
        _ = ∑ i : I, ∑ p, (hardHistoryLaw S H ε hS hH hε hεH i pol k).prob p *
              ∑ jh : Fin (S / 2) × Fin H, w jh *
                (1 - (pol k p jh.2 ⟨jh.1, by have := jh.1.isLt; omega⟩).prob (i jh)) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun jh _ => ?_
            ring
        _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (policySuboptimality_ge hS hH hε hεH i (pol k p))
              ((hardHistoryLaw S H ε hS hH hε hεH i pol k).prob_nonneg p)
    calc (Fintype.card I : ℝ) * (K * C / 3) = ∑ _k : Fin K, (Fintype.card I : ℝ) * (C / 3) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hk k
  unfold onlineExpectedRegret
  rw [Finset.sum_comm]
  calc (Fintype.card I : ℝ) * (K * C / 3)
      = ∑ σ, L.seedLaw.prob σ * ((Fintype.card I : ℝ) * (K * C / 3)) := by
        rw [← Finset.sum_mul, L.seedLaw.sum_prob, one_mul]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hseed σ) (L.seedLaw.prob_nonneg σ)

end Family

/-- **Theorem 5.19** (`thm:minimax-lower-online`, `chapters/onlineRL.tex:2443–2456`), with
`c₀ = 1/1536`. -/
theorem minimax_lower_online :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (S A H K : ℕ), 2 ≤ S → 3 ≤ A → 2 ≤ H → 1 ≤ K →
      ∃ (I : Type) (_ : Fintype I) (E : I → Fin H → EnvironmentStage (Fin S) (Fin A))
        (ρ : FiniteDistribution (Fin S)),
        ∀ L : OnlineLearner (Fin S) (Fin A) H, ∃ i : I,
          c₀ * min (Real.sqrt ((H : ℝ) ^ 3 * S * A * K)) ((H : ℝ) * K) ≤
            onlineExpectedRegret (E i) ρ L K := by
  refine ⟨1 / 1536, by norm_num, fun S A H K hS hA hH hK => ?_⟩
  obtain ⟨M, rfl⟩ : ∃ M, A = M + 1 := ⟨A - 1, by omega⟩
  have hM : 2 ≤ M := by omega
  set m : ℕ := S / 2 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hS3 : (S : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast (by omega : S ≤ 3 * (S / 2))
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  set x : ℝ := Real.sqrt ((m : ℝ) * ((M : ℝ) + 1) * (H : ℝ) ^ 3 / (18 * K)) with hx
  have hxpos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  set ε : ℝ := min x ((H : ℝ) / 2) with hεdef
  have hε : 0 < ε := lt_min hxpos (by positivity)
  have hεH : ε ≤ (H : ℝ) / 2 := min_le_right _ _
  have hεx : ε ≤ x := min_le_left _ _
  have hε2 : ε ^ 2 ≤ (m : ℝ) * ((M : ℝ) + 1) * (H : ℝ) ^ 3 / (18 * K) := by
    calc ε ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hε.le hεx 2
      _ = _ := Real.sq_sqrt (by positivity)
  have hKB : (K : ℝ) * (4 * ε ^ 2 / (H : ℝ) ^ 3 / ((S / 2 : ℕ) : ℝ)) ≤ 2 * ((M : ℝ) + 1) / 9 := by
    rw [← hmdef]
    have h1 : (K : ℝ) * (4 * ε ^ 2 / (H : ℝ) ^ 3 / (m : ℝ)) =
        4 * K / ((H : ℝ) ^ 3 * m) * ε ^ 2 := by field_simp
    rw [h1]
    calc 4 * K / ((H : ℝ) ^ 3 * m) * ε ^ 2 ≤
          4 * K / ((H : ℝ) ^ 3 * m) * ((m : ℝ) * ((M : ℝ) + 1) * (H : ℝ) ^ 3 / (18 * K)) :=
          mul_le_mul_of_nonneg_left hε2 (by positivity)
      _ = 2 * ((M : ℝ) + 1) / 9 := by field_simp; ring
  refine ⟨Fin (S / 2) × Fin H → Fin (M + 1), inferInstance,
    fun i => onlineLBStages S H ε hS hH hε hεH i, onlineLBRho S hS, fun L => ?_⟩
  have hsum := hard_family_sum_regret hS hH hε hεH hM K hKB L
  -- the averaged bound dominates `c₀ min{…}`
  have hfinal : 1 / 1536 * min (Real.sqrt ((H : ℝ) ^ 3 * S * ((M + 1 : ℕ) : ℝ) * K)) ((H : ℝ) * K) ≤
      K * (ε * ((H : ℝ) - 1) / (32 * H)) / 3 := by
    have hhalf : (K : ℝ) * ε / 192 ≤ K * (ε * ((H : ℝ) - 1) / (32 * H)) / 3 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      have : (K : ℝ) * (ε * ((H : ℝ) - 1) / (32 * H)) =
          K * ε * (((H : ℝ) - 1) / H) / 32 := by field_simp
      rw [this]
      have hHH : (1 : ℝ) / 2 ≤ ((H : ℝ) - 1) / H := by
        rw [div_le_div_iff₀ (by norm_num) hHpos]; linarith
      have hKε : 0 ≤ (K : ℝ) * ε := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hHH hKε]
    refine le_trans ?_ hhalf
    by_cases hxH : x ≤ (H : ℝ) / 2
    · have hεeq : ε = x := min_eq_left hxH
      have hsq : Real.sqrt ((H : ℝ) ^ 3 * S * ((M + 1 : ℕ) : ℝ) * K) ≤ 8 * K * x := by
        have h8 : (0 : ℝ) ≤ 8 * K * x := by positivity
        rw [← Real.sqrt_sq h8]
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow, mul_pow, hx, Real.sq_sqrt (by positivity)]
        push_cast
        have hpos : (0 : ℝ) ≤ (H : ℝ) ^ 3 * ((M : ℝ) + 1) * K := by positivity
        have h64 : (8 : ℝ) ^ 2 * (K : ℝ) ^ 2 *
            ((m : ℝ) * ((M : ℝ) + 1) * (H : ℝ) ^ 3 / (18 * K)) =
            (64 / 18 * (m : ℝ)) * ((H : ℝ) ^ 3 * ((M : ℝ) + 1) * K) := by
          field_simp; norm_num
        rw [h64]
        calc (H : ℝ) ^ 3 * S * ((M : ℝ) + 1) * K = (S : ℝ) * ((H : ℝ) ^ 3 * ((M : ℝ) + 1) * K) := by
              ring
          _ ≤ (64 / 18 * (m : ℝ)) * ((H : ℝ) ^ 3 * ((M : ℝ) + 1) * K) :=
              mul_le_mul_of_nonneg_right (by linarith) hpos
      calc 1 / 1536 * min (Real.sqrt ((H : ℝ) ^ 3 * S * ((M + 1 : ℕ) : ℝ) * K)) ((H : ℝ) * K)
          ≤ 1 / 1536 * Real.sqrt ((H : ℝ) ^ 3 * S * ((M + 1 : ℕ) : ℝ) * K) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
        _ ≤ 1 / 1536 * (8 * K * x) := mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = (K : ℝ) * ε / 192 := by rw [hεeq]; ring
    · have hεeq : ε = (H : ℝ) / 2 := min_eq_right (le_of_lt (not_le.mp hxH))
      calc 1 / 1536 * min (Real.sqrt ((H : ℝ) ^ 3 * S * ((M + 1 : ℕ) : ℝ) * K)) ((H : ℝ) * K)
          ≤ 1 / 1536 * ((H : ℝ) * K) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ ≤ (K : ℝ) * ε / 192 := by rw [hεeq]; nlinarith
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ i : Fin (S / 2) × Fin H → Fin (M + 1),
      onlineExpectedRegret (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS) L K <
      ∑ _i : Fin (S / 2) × Fin H → Fin (M + 1),
        1 / 1536 * min (Real.sqrt ((H : ℝ) ^ 3 * S * ((M + 1 : ℕ) : ℝ) * K)) ((H : ℝ) * K) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hcon i
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have hcard : (0 : ℝ) < Fintype.card (Fin (S / 2) × Fin H → Fin (M + 1)) := by
    exact_mod_cast Fintype.card_pos
  have := mul_le_mul_of_nonneg_left hfinal hcard.le
  linarith

end StatisticalRL.OnlineLowerBound
