import Formalization.Online.RegretToPAC.StartState
import Formalization.MDP.FiniteOptimal
import Formalization.MDP.Basic

/-! Corrected and restricted regret-to-PAC conversion, `eq:PAC-from-regret-conversion`,
`chapters/onlineRL.tex:113–141`. The printed constant `C_{S,A,H+1}` is false
(`PrintedRefutation.lean`). Proof route: start-state independence from the protocol
(`chapters/onlineRL.tex:17–41`), then Markov's inequality on the uniform mixture over episodes.
The printed proof (:145–183) instead runs the algorithm on an augmented MDP; that is not needed
here and not formalized. -/

open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.OnlineRL.RegretToPAC

universe u v

section Finite
variable {Ω : Type*} [Fintype Ω]

local instance regPacMeasurable : MeasurableSpace Ω := ⊤

/-- Real mass of a set under the row measure of a finite distribution. -/
theorem rowMeasure_real_eq_sum (d : FiniteDistribution Ω) (S : Set Ω) :
    d.rowMeasure.real S = ∑ x, d.prob x * S.indicator 1 x := by
  classical
  rw [Measure.real, FiniteDistribution.rowMeasure, PMF.toMeasure_apply_fintype,
    ENNReal.toReal_sum (fun x _ ↦ by
      by_cases hx : x ∈ S
      · simp [hx, PMF.apply_ne_top]
      · simp [hx])]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : x ∈ S
  · simp [hx, FiniteDistribution.toPMF, PMF.ofFintype_apply,
      ENNReal.toReal_ofReal (d.prob_nonneg x)]
  · simp [hx]

/-- Finite Markov inequality with the degenerate thresholds handled: if the weighted sum of a
nonnegative variable is at most `t * m` with `m > 0`, the weight of `{t < X}` is at most `m`. -/
theorem sum_mul_ite_lt_le {ι : Type*} [Fintype ι] (w X : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hX : ∀ i, 0 ≤ X i) (t m : ℝ) (hm : 0 < m) (hsum : ∑ i, w i * X i ≤ t * m) :
    ∑ i, w i * (if t < X i then 1 else 0) ≤ m := by
  have h0 : 0 ≤ ∑ i, w i * X i := Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (hX i)
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have : t * m < 0 := mul_neg_of_neg_of_pos ht hm
    linarith
  · subst ht
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ mul_nonneg (hw i) (hX i))).mp (le_antisymm (by simpa using hsum) h0)
    have hz : ∑ i, w i * (if (0 : ℝ) < X i then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      split_ifs with h
      · rcases mul_eq_zero.mp (hall i hi) with h' | h'
        · simp [h']
        · linarith
      · simp
    linarith
  · have hmul : t * ∑ i, w i * (if t < X i then 1 else 0) ≤ ∑ i, w i * X i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      split_ifs with h
      · nlinarith [hw i]
      · nlinarith [hw i, hX i]
    exact le_of_mul_le_mul_left (hmul.trans hsum) ht

end Finite

section Values
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]

theorem controlled_ofFn_eq {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (π : ℕ → StationaryPolicy State Action) :
    EnvironmentStage.controlled (List.ofFn E) π =
      List.ofFn (fun h ↦ (E h).withPolicy (π h.val)) := by
  induction H generalizing π with
  | zero => rfl
  | succ H ih =>
    rw [List.ofFn_succ, EnvironmentStage.controlled, ih, List.ofFn_succ]
    rfl

/-- Every deterministic Markov policy is dominated by the backward-induction optimum. -/
theorem trajectoryValue_pointMass_le_greedy {H : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (f : Fin H → State → Action) (s : State) :
    DecisionStage.trajectoryValue
        (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
        s ≤
      DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) s := by
  let π : ℕ → StationaryPolicy State Action := fun n t ↦
    if hn : n < H then EnvironmentStage.pointMass (f ⟨n, hn⟩ t)
    else EnvironmentStage.pointMass (f ⟨0, hH⟩ t)
  have h := EnvironmentStage.greedy_dominates (List.ofFn E) π s
  rw [controlled_ofFn_eq] at h
  have hπ : (fun h : Fin H ↦ (E h).withPolicy (π h.val)) =
      (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))) := by
    funext h
    simp [π, h.isLt]
  rwa [hπ] at h

end Values

theorem expectation_finset_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (d : FiniteDistribution Ω) (f : ι → Ω → ℝ) :
    d.expectation (fun x ↦ ∑ k, f k x) = ∑ k, d.expectation (f k) := by
  simp only [FiniteDistribution.expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- Corrected regret-to-PAC conversion, `eq:PAC-from-regret-conversion` with
`eq:uniform-policy-pihat`, `chapters/onlineRL.tex:113–141`: the bound holds with the regret
constant `C` at the actual `(S, A, H)` in place of the printed `C_{S,A,H+1}`. The regret
hypothesis is assumed only at the given instance `(H, K, E, ρ)` (weaker than "for any MDP").
Algorithm class: finite seed, deployed policies deterministic Markov given seed and completed
history. `0 < H`, `0 < K`, `0 < δ`; `α ∈ [0,1]` as printed (unused). Direct proof, no
augmented MDP. -/
theorem eq_PAC_from_regret_conversion_corrected :
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (Seed : Type) [Fintype Seed] (H K : ℕ) (hH : 0 < H), 0 < K →
    ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
      (fallback : State) (ν : FiniteDistribution Seed)
      (planner : Seed → OnlineEpisodePlanner State Action H) (C α δ : ℝ),
    0 ≤ α → α ≤ 1 → 0 < δ →
    let law : Seed →
        FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
      fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
    let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
        Fin K → Fin H → State → Action :=
      fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
          (k.val * H))
    let V : (Fin H → State → Action) → State → ℝ := fun f ↦
      DecisionStage.trajectoryValue
        (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
    let Vstar : State → ℝ :=
      DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
    ν.expectation (fun ω ↦ (law ω).expectation (fun sample ↦
        ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k)))) ≤
      C * (K : ℝ) ^ (1 - α) →
    1 - δ ≤ ν.expectation (fun ω ↦ (1 / (K : ℝ)) * ∑ k : Fin K,
      (law ω).rowMeasure.real {sample |
        ρ.expectation Vstar - ρ.expectation (V (πk ω sample k)) ≤ C * (K : ℝ) ^ (-α) / δ}) := by
  intro State Action _ _ Seed _ H K hH hK E ρ fallback ν planner C α δ _ _ hδ law πk V Vstar hreg
  classical
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  let t : ℝ := C * (K : ℝ) ^ (-α) / δ
  let X : Seed → ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) → Fin K → ℝ :=
    fun ω sample k ↦ ρ.expectation Vstar - ρ.expectation (V (πk ω sample k))
  have hX : ∀ ω sample k, 0 ≤ X ω sample k := by
    intro ω sample k
    have := ρ.expectation_mono (fun s ↦ trajectoryValue_pointMass_le_greedy hH E (πk ω sample k) s)
    simp only [X]
    linarith
  -- start-state independence turns realized regret into ρ-averaged gaps
  have hregk : ∀ ω, (law ω).expectation (fun sample ↦
      ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k))) =
      ∑ k : Fin K, (law ω).expectation (fun sample ↦ X ω sample k) := by
    intro ω
    rw [expectation_finset_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hind := onlineEpisode_startState_independent H K hH E ρ fallback (planner ω) k
      (fun f s ↦ Vstar s - V f s)
    refine hind.trans ?_
    congr 1
    funext sample
    exact FiniteDistribution.expectation_sub _ _ _
  -- flattened weights over (seed, episode, run)
  let w : Seed × Fin K × ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) → ℝ :=
    fun p ↦ ν.prob p.1 * (law p.1).prob p.2.2
  let Xf : Seed × Fin K × ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) → ℝ :=
    fun p ↦ X p.1 p.2.2 p.2.1
  have hw : ∀ p, 0 ≤ w p := fun p ↦ mul_nonneg (ν.prob_nonneg _) ((law p.1).prob_nonneg _)
  have hTot : ∑ p, w p * Xf p = ν.expectation (fun ω ↦ (law ω).expectation (fun sample ↦
      ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k)))) := by
    simp_rw [hregk]
    simp only [FiniteDistribution.expectation, Fintype.sum_prod_type, Finset.mul_sum, w, Xf]
    refine Finset.sum_congr rfl fun ω _ ↦ Finset.sum_congr rfl fun k _ ↦
      Finset.sum_congr rfl fun sample _ ↦ ?_
    ring_nf
  have hscale : t * (δ * K) = C * (K : ℝ) ^ (1 - α) := by
    have : (K : ℝ) ^ (1 - α) = (K : ℝ) * (K : ℝ) ^ (-α) := by
      rw [sub_eq_add_neg, Real.rpow_add hKpos, Real.rpow_one]
    rw [this]
    simp only [t]
    field_simp
  have hbad := sum_mul_ite_lt_le w Xf hw (fun p ↦ hX _ _ _) t (δ * K)
    (mul_pos hδ hKpos) (by rw [hTot, hscale]; exact hreg)
  -- the target probability is one minus the flattened bad mass divided by K
  have hrow : ∀ ω k, (law ω).rowMeasure.real {sample | X ω sample k ≤ t} =
      1 - ∑ sample, (law ω).prob sample * (if t < X ω sample k then 1 else 0) := by
    intro ω k
    rw [rowMeasure_real_eq_sum]
    have hpt : ∀ sample, (law ω).prob sample * Set.indicator {sample | X ω sample k ≤ t} 1 sample =
        (law ω).prob sample - (law ω).prob sample * (if t < X ω sample k then 1 else 0) := by
      intro sample
      by_cases h : t < X ω sample k
      · simp [Set.indicator, h, not_le.mpr h]
      · simp [Set.indicator, h, le_of_not_gt h]
    simp_rw [hpt, Finset.sum_sub_distrib, FiniteDistribution.sum_prob]
  have hflat : ∀ F : Seed × Fin K × ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) → ℝ,
      ∑ p, F p = ∑ ω, ∑ k : Fin K, ∑ sample, F (ω, k, sample) := by
    intro F
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hgoal : ν.expectation (fun ω ↦ (1 / (K : ℝ)) * ∑ k : Fin K,
      (law ω).rowMeasure.real {sample | X ω sample k ≤ t}) =
      1 - (1 / (K : ℝ)) * ∑ p, w p * (if t < Xf p then 1 else 0) := by
    have hpt : ∀ ω, ν.prob ω * ((1 / (K : ℝ)) * ∑ k : Fin K,
        (law ω).rowMeasure.real {sample | X ω sample k ≤ t}) =
        ν.prob ω - (1 / (K : ℝ)) * ∑ k : Fin K, ∑ sample,
          w (ω, k, sample) * (if t < Xf (ω, k, sample) then 1 else 0) := by
      intro ω
      simp_rw [hrow]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hin : ∑ k : Fin K, ∑ sample,
          w (ω, k, sample) * (if t < Xf (ω, k, sample) then 1 else 0) =
          ν.prob ω * ∑ k : Fin K, ∑ sample, (law ω).prob sample *
            (if t < X ω sample k then 1 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun sample _ ↦ ?_
        simp only [w, Xf, mul_assoc]
      rw [hin]
      field_simp
    rw [FiniteDistribution.expectation, Finset.sum_congr rfl (fun ω _ ↦ hpt ω),
      Finset.sum_sub_distrib, ν.sum_prob, hflat, Finset.mul_sum]
  have hfinal : 1 - δ ≤ 1 - (1 / (K : ℝ)) * ∑ p, w p * (if t < Xf p then 1 else 0) := by
    have : (1 / (K : ℝ)) * ∑ p, w p * (if t < Xf p then 1 else 0) ≤ δ := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hKpos]
      exact hbad
    linarith
  exact hfinal.trans_eq hgoal.symm

/-- Restricted regret-to-PAC conversion with the printed constant `C_{S,A,H+1}`,
`chapters/onlineRL.tex:113–141`, under the added premise `C_{S,A,H} ≤ C_{S,A,H+1}` at the
instance's `(S, A)` (`C` nondecreasing in `H`). Same algorithm class as
`eq_PAC_from_regret_conversion_corrected`. -/
theorem eq_PAC_from_regret_conversion_restricted :
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (Seed : Type) [Fintype Seed] (ν : ℕ → ℕ → FiniteDistribution Seed)
    (alg : (H : ℕ) → ℕ → (Fin H → State → Action → ℝ) → Seed →
      OnlineEpisodePlanner State Action H)
    (C : ℕ → ℕ → ℕ → ℝ) (α : ℝ), 0 ≤ α → α ≤ 1 →
    (∀ H : ℕ, C (Fintype.card State) (Fintype.card Action) H ≤
      C (Fintype.card State) (Fintype.card Action) (H + 1)) →
    (∀ (H K : ℕ) (hH : 0 < H), 0 < K →
      ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State),
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let planner : Seed → OnlineEpisodePlanner State Action H :=
        alg H K (fun h ↦ (E h).reward)
      let law : Seed →
          FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
        fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
      let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
          Fin K → Fin H → State → Action :=
        fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
            (k.val * H))
      let V : (Fin H → State → Action) → State → ℝ := fun f ↦
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
      let Vstar : State → ℝ :=
        DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
      (ν H K).expectation (fun ω ↦ (law ω).expectation (fun sample ↦
          ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k)))) ≤
        C (Fintype.card State) (Fintype.card Action) H * (K : ℝ) ^ (1 - α)) →
    ∀ (H K : ℕ) (hH : 0 < H), 0 < K →
      ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State) (δ : ℝ),
      0 < δ →
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let planner : Seed → OnlineEpisodePlanner State Action H :=
        alg H K (fun h ↦ (E h).reward)
      let law : Seed →
          FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
        fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
      let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
          Fin K → Fin H → State → Action :=
        fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
            (k.val * H))
      let V : (Fin H → State → Action) → State → ℝ := fun f ↦
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
      let Vstar : State → ℝ :=
        DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
      1 - δ ≤ (ν H K).expectation (fun ω ↦ (1 / (K : ℝ)) * ∑ k : Fin K,
        (law ω).rowMeasure.real {sample |
          ρ.expectation Vstar - ρ.expectation (V (πk ω sample k)) ≤
            C (Fintype.card State) (Fintype.card Action) (H + 1) * (K : ℝ) ^ (-α) / δ}) := by
  intro State Action _ _ Seed _ ν alg C α hα0 hα1 hmono hreg H K hH hK E ρ δ hδ
    fallback planner law πk V Vstar
  have hcorr := eq_PAC_from_regret_conversion_corrected State Action Seed H K hH hK E ρ
    fallback (ν H K) planner (C (Fintype.card State) (Fintype.card Action) H) α δ hα0 hα1 hδ
    (hreg H K hH hK E ρ)
  refine hcorr.trans (FiniteDistribution.expectation_mono _ fun ω ↦ ?_)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ ?_) (by positivity)
  refine measureReal_mono (fun sample hs ↦ ?_)
    (by rw [FiniteDistribution.rowMeasure]; exact measure_ne_top _ _)
  simp only [Set.mem_setOf_eq] at hs ⊢
  refine hs.trans ?_
  have hKα : 0 ≤ (K : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg K) _
  have := hmono H
  gcongr

end StatisticalRL.OnlineRL.RegretToPAC
