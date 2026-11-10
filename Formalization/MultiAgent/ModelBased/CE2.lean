import Formalization.MultiAgent.ModelBased.CE2Game

/-!
# Counterexample CE2: refutation of printed Theorem 7.6

On the almost-sure event `Good` (every step-1 sample from `s₀` lies in the support of its true
row), the oracle plays risky at `s₀`, and its true gap is at least `1/2 − |B|/(S−2) ≥ 1/2 − N/(S−2)`
because `|B| ≤ N`. With `S = 8N`, `H = 2`, `ε = 1/4`, `δ = 1/2` the printed threshold
`N ≥ C₁ H³ ε⁻² log(SHN∏A_i/δ) = 128 C₁ log(128 N²)` holds for large `N`, for every `C₁ > 0`,
while `P(gap ≤ 1/4) = 0 < 1/2`. Hence `¬ Thm7_6_printed`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.FiniteHorizonGenerative

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- A coordinate event of probability `0` under the sampling law. -/
theorem gameSamplingLaw_coord_null (G : MarkovGame m S H A) (hS : 0 < S) (hA : ∀ i, 0 < A i)
    (N : ℕ) (i : SampleIndex (Fin S) (JointAction m A) H N) (T : Set (Fin S))
    (hT : ∀ x ∈ T, (G.transition ((i.1.1 : ℕ) + 1) i.1.2.1 i.1.2.2).prob x = 0) :
    (gameSamplingLaw G hS hA N) {data | data i ∈ T} = 0 := by
  have hm : Measurable (fun data : GameSamples m S H A N => data i) := measurable_pi_apply i
  have hmap := samplingLaw_marginal (gameStages G hS hA) N i
  change samplingLaw (gameStages G hS hA) N ((fun data => data i) ⁻¹' T) = 0
  rw [← Measure.map_apply hm ((Set.to_countable T).measurableSet), hmap]
  unfold FiniteDistribution.rowMeasure
  rw [PMF.toMeasure_apply_eq_zero_iff _ ((Set.to_countable T).measurableSet), Set.disjoint_left]
  intro x hx hxT
  rw [PMF.mem_support_iff] at hx
  apply hx
  have h0 := hT x hxT
  simp only [FiniteDistribution.toPMF, PMF.ofFintype_apply]
  change ENNReal.ofReal ((G.transition ((i.1.1 : ℕ) + 1) i.1.2.1 i.1.2.2).prob x) = 0
  rw [h0, ENNReal.ofReal_zero]

theorem empiricalRow_prob_pos_iff {T : Type*} [Fintype T] (N : ℕ) (hN : 0 < N) (ω : Fin N → T)
    (x : T) : 0 < (FiniteDistribution.empiricalRow N hN ω).prob x ↔ ∃ n, ω n = x := by
  constructor
  · intro hpos
    by_contra hne
    push_neg at hne
    unfold FiniteDistribution.empiricalRow at hpos
    simp only at hpos
    rw [Finset.sum_eq_zero (fun n _ => if_neg (hne n)), mul_zero] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨n, rfl⟩
    unfold FiniteDistribution.empiricalRow
    simp only
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    apply mul_pos (inv_pos.mpr hN')
    exact Finset.sum_pos' (fun k _ => by split_ifs <;> norm_num)
      ⟨n, Finset.mem_univ n, by rw [if_pos rfl]; norm_num⟩

theorem card_support_empiricalRow_le {T : Type*} [Fintype T] [DecidableEq T] (N : ℕ) (hN : 0 < N)
    (ω : Fin N → T) :
    (Finset.univ.filter fun x => 0 < (FiniteDistribution.empiricalRow N hN ω).prob x).card ≤ N := by
  calc _ ≤ (Finset.univ.image ω).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨n, hn⟩ := (empiricalRow_prob_pos_iff N hN ω x).mp (Finset.mem_filter.mp hx).2
        exact Finset.mem_image.mpr ⟨n, Finset.mem_univ n, hn⟩
    _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
    _ = N := by simp

namespace CE2

variable {S : ℕ}

theorem game_trans_s0 (hS : 3 ≤ S) (a : JA) :
    (game hS).transition 1 (s0 hS) a =
      if a 0 = 1 then unifHigh hS else EnvironmentStage.pointMass (sSafe hS) := by
  show (if (1 : ℕ) = 1 ∧ s0 hS = s0 hS then
      (if a 0 = 1 then unifHigh hS else EnvironmentStage.pointMass (sSafe hS))
    else EnvironmentStage.pointMass (s0 hS)) = _
  rw [if_pos (show (1 : ℕ) = 1 ∧ s0 hS = s0 hS from ⟨rfl, rfl⟩)]

/-- The step-1 empirical row at `s₀`. -/
theorem empirical_row_one (hS : 3 ≤ S) (N : ℕ) (hN : 0 < N) (data : GameSamples 2 S 2 A2 N)
    (s : Fin S) (a : JA) :
    (empiricalGame (game hS) N hN data).transition 1 s a =
      FiniteDistribution.empiricalRow N hN (fun n => data ((⟨0, by norm_num⟩, s, a), n)) := by
  simp only [empiricalGame]
  rw [dif_pos ⟨le_rfl, by norm_num⟩]

/-- Every step-1 sample from `s₀` lies in the support of its true row. -/
def Good (hS : 3 ≤ S) (N : ℕ) (data : GameSamples 2 S 2 A2 N) : Prop :=
  ∀ (a : JA) (n : Fin N),
    (a 0 = 1 → t2 hS ≤ data ((⟨0, by norm_num⟩, s0 hS, a), n)) ∧
    (a 0 ≠ 1 → data ((⟨0, by norm_num⟩, s0 hS, a), n) = sSafe hS)

theorem good_ae (hS : 3 ≤ S) (hS0 : 0 < S) (N : ℕ) :
    (gameSamplingLaw (game hS) hS0 (fun _ => by norm_num) N).real {data | ¬ Good hS N data} = 0 := by
  classical
  let Bad : JA → Set (Fin S) := fun a =>
    {x | (a 0 = 1 ∧ ¬ t2 hS ≤ x) ∨ (a 0 ≠ 1 ∧ x ≠ sSafe hS)}
  have hsub : {data | ¬ Good hS N data} ⊆ ⋃ p : JA × Fin N,
      {data : GameSamples 2 S 2 A2 N | data ((⟨0, by norm_num⟩, s0 hS, p.1), p.2) ∈ Bad p.1} := by
    intro data hd
    simp only [Good, not_forall] at hd
    obtain ⟨a, n, hn⟩ := hd
    refine Set.mem_iUnion.mpr ⟨(a, n), ?_⟩
    simp only [Set.mem_setOf_eq, Bad]
    by_cases ha : a 0 = 1
    · left; refine ⟨ha, ?_⟩
      intro h; exact hn ⟨fun _ => h, fun h' => absurd ha h'⟩
    · right; refine ⟨ha, ?_⟩
      intro h; exact hn ⟨fun h' => absurd h' ha, fun _ => h⟩
  have hnull : (gameSamplingLaw (game hS) hS0 (fun _ => by norm_num) N) (⋃ p : JA × Fin N,
      {data : GameSamples 2 S 2 A2 N | data ((⟨0, by norm_num⟩, s0 hS, p.1), p.2) ∈ Bad p.1}) = 0 := by
    refine measure_iUnion_null fun p => ?_
    refine gameSamplingLaw_coord_null (game hS) hS0 _ N _ _ fun x hx => ?_
    change ((game hS).transition 1 (s0 hS) p.1).prob x = 0
    rw [game_trans_s0]
    rcases hx with ⟨ha, hx⟩ | ⟨ha, hx⟩
    · simp only [ha, if_true, unifHigh]
      rw [if_neg]
      simpa using hx
    · simp only [ha, if_false]
      exact pointMass_prob_ne hx
  have := measure_mono_null hsub hnull
  simp [Measure.real, this]

/-- On good data the oracle plays risky at `s₀`. -/
theorem stage1_risky (hS : 3 ≤ S) (N : ℕ) (hN : 0 < N) (data : GameSamples 2 S 2 A2 N)
    (hg : Good hS N data) : stage1 hS (empiricalGame (game hS) N hN data) (s0 hS) 0 = 1 := by
  set Gh := empiricalGame (game hS) N hN data
  set W := contW hS (selB hS Gh)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsafe_ne : ∀ x : Fin S, t2 hS ≤ x → x ≠ sSafe hS := by
    intro x hx he
    rw [he] at hx
    simp [t2, sSafe, Fin.le_def] at hx
  -- `u(1,0) = 1`
  have hu10 : (Gh.transition 1 (s0 hS) a10).expectation W = 1 := by
    rw [empirical_row_one, FiniteDistribution.empiricalRow_expectation]
    have hterm : ∀ n, W (data ((⟨0, by norm_num⟩, s0 hS, a10), n)) = 1 := by
      intro n
      have ht2 := (hg a10 n).1 (by simp [a10])
      have hB : data ((⟨0, by norm_num⟩, s0 hS, a10), n) ∈ selB hS Gh := by
        simp only [selB, Finset.mem_filter, Finset.mem_univ, true_and, Gh]
        rw [empirical_row_one, empiricalRow_prob_pos_iff]
        exact ⟨n, rfl⟩
      simp only [W, contW, if_neg (hsafe_ne _ ht2), if_pos (And.intro ht2 hB)]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  -- `u(a) = 1/2` when player 1 plays safe
  have husafe : ∀ a : JA, a 0 ≠ 1 → (Gh.transition 1 (s0 hS) a).expectation W = 1 / 2 := by
    intro a ha
    rw [empirical_row_one, FiniteDistribution.empiricalRow_expectation]
    have hterm : ∀ n, W (data ((⟨0, by norm_num⟩, s0 hS, a), n)) = 1 / 2 := by
      intro n
      rw [(hg a n).2 ha]
      simp [W, contW]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  by_contra hne
  have h1 := stage1_spec hS Gh (s0 hS) a10
  rw [hu10, husafe _ hne] at h1
  norm_num at h1

/-- Values at step 2 of the oracle policy in any game with the CE2 rewards. -/
theorem valueJ_two (hS : 3 ≤ S) (G' G'' : MarkovGame 2 S 2 A2)
    (hrew : G'.reward = (game hS).reward) (i : Fin 2) :
    valueJ G' (toJoint (oracle hS G'')) i 2 1 = contW hS (selB hS G'') := by
  funext s'
  rw [valueJ_pure_succ G' _ i 2 0 s' (cst (stage2 hS G'' s')) (oracle_two hS G'' s'), hrew,
    reward_two_stage2, valueJ_zero_fun, FiniteDistribution.expectation_const, add_zero]

/-- The true gap of the oracle output on good data. -/
theorem gap_ge (hS : 3 ≤ S) (N : ℕ) (hN : 0 < N) (data : GameSamples 2 S 2 A2 N)
    (hg : Good hS N data) :
    1 / 2 - (N : ℝ) / ((S : ℝ) - 2) ≤ gap (game hS) (oracle hS (empiricalGame (game hS) N hN data)) := by
  classical
  set Gh := empiricalGame (game hS) N hN data
  set σ := oracle hS Gh
  set B := selB hS Gh
  set W := contW hS B
  have hS3 : (3 : ℝ) ≤ S := by exact_mod_cast hS
  have hK : (0 : ℝ) < (S : ℝ) - 2 := by linarith
  have hrisky := stage1_risky hS N hN data hg
  have hr1 : ∀ i a, (game hS).reward i 1 (s0 hS) a = 0 := by intro i a; simp [game]
  -- the true value of player 1 at `s₀` is at most `|B| / (S − 2)`
  have hV : valueJ (game hS) (toJoint σ) 0 1 2 (s0 hS) ≤ (B.card : ℝ) / ((S : ℝ) - 2) := by
    rw [valueJ_pure_succ _ σ 0 1 1 (s0 hS) (stage1 hS Gh (s0 hS)) (oracle_one hS Gh (s0 hS)),
      hr1, zero_add, valueJ_two hS (game hS) Gh rfl]
    have htr : (game hS).transition 1 (s0 hS) (stage1 hS Gh (s0 hS)) = unifHigh hS := by
      rw [game_trans_s0, if_pos hrisky]
    rw [htr]
    unfold FiniteDistribution.expectation
    calc ∑ s, (unifHigh hS).prob s * W s ≤ ∑ s, (if s ∈ B then 1 / ((S : ℝ) - 2) else 0) := by
          refine Finset.sum_le_sum fun s _ => ?_
          simp only [unifHigh, W, contW]
          by_cases hs : s ∈ Finset.Ici (t2 hS)
          · have ht : t2 hS ≤ s := Finset.mem_Ici.mp hs
            have hne : s ≠ sSafe hS := by
              intro he; rw [he] at ht; simp [t2, sSafe, Fin.le_def] at ht
            rw [if_pos hs, if_neg hne]
            by_cases hB : s ∈ B
            · rw [if_pos ⟨ht, hB⟩, if_pos hB, mul_one]
            · rw [if_neg (fun h => hB h.2), if_neg hB, mul_zero]
          · rw [if_neg hs, zero_mul]; split_ifs <;> positivity
      _ = (B.card : ℝ) / ((S : ℝ) - 2) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; ring
  -- the deviation of player 1 to `safe` earns `1/2`
  let π' : PlayerPolicy S (A2 0) := fun _ _ => EnvironmentStage.pointMass 0
  have hD : valueJ (game hS) (deviate (toJoint σ) 0 π') 0 1 2 (s0 hS) = 1 / 2 := by
    rw [valueJ_deviate_pure_succ _ σ 0 π' 1 1 (s0 hS) (stage1 hS Gh (s0 hS))
      (oracle_one hS Gh (s0 hS))]
    rw [pointMass_sum (0 : Fin 2)]
    have htr : (game hS).transition 1 (s0 hS) (Function.update (stage1 hS Gh (s0 hS)) 0 0) =
        EnvironmentStage.pointMass (sSafe hS) := by
      rw [game_trans_s0, if_neg (by simp)]
    rw [hr1, zero_add, htr, pointMass_expectation,
      valueJ_deviate_pure_succ _ σ 0 π' 2 0 (sSafe hS) (cst (stage2 hS Gh (sSafe hS)))
        (oracle_two hS Gh (sSafe hS)), pointMass_sum (0 : Fin 2), valueJ_zero_fun,
      FiniteDistribution.expectation_const, add_zero]
    simp [game]
  have hgap := gapJ_ge (game hS) (toJoint σ) 0 (fun h s a => (game_reward_mem hS 0 h s a).2) π'
    (s0 hS)
  rw [gapJ_toJoint] at hgap
  have hB : (B.card : ℝ) ≤ N := by
    have := card_support_empiricalRow_le N hN (fun n => data ((⟨0, by norm_num⟩, s0 hS, a10), n))
    have hBeq : B = Finset.univ.filter fun x => 0 < (FiniteDistribution.empiricalRow N hN
        (fun n => data ((⟨0, by norm_num⟩, s0 hS, a10), n))).prob x := by
      simp only [B, selB, Gh]
      rw [empirical_row_one]
    rw [hBeq]
    exact_mod_cast this
  have hBK : (B.card : ℝ) / ((S : ℝ) - 2) ≤ (N : ℝ) / ((S : ℝ) - 2) :=
    div_le_div_of_nonneg_right hB hK.le
  linarith

/-- The printed threshold can be met for every constant. -/
theorem exists_large_N (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, 1 ≤ N ∧ 128 * C * Real.log (128 * (N : ℝ) ^ 2) ≤ N := by
  set n : ℕ := ⌈896 * C⌉₊ + 1
  have hn1 : (1 : ℝ) ≤ n := by simp [n]
  have hnC : 896 * C ≤ n := by
    have := Nat.le_ceil (896 * C)
    simp only [n]; push_cast; linarith
  refine ⟨n ^ 2, Nat.one_le_pow 2 n (Nat.succ_pos _), ?_⟩
  push_cast
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log (128 * ((n : ℝ) ^ 2) ^ 2) ≤ 7 * n := by
    have h128 : Real.log 128 ≤ 7 := by
      have : (128 : ℝ) = 2 ^ 7 := by norm_num
      rw [this, Real.log_pow]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      push_cast
      linarith
    have hlogn : Real.log n ≤ n - 1 := Real.log_le_sub_one_of_pos hn0
    rw [Real.log_mul (by norm_num) (by positivity), ← pow_mul, Real.log_pow]
    push_cast
    linarith
  calc 128 * C * Real.log (128 * ((n : ℝ) ^ 2) ^ 2) ≤ 128 * C * (7 * n) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 896 * C * n := by ring
    _ ≤ n * n := mul_le_mul_of_nonneg_right hnC hn0.le
    _ = (n : ℝ) ^ 2 := by ring

end CE2

end StatisticalRL.Ch7Rest.Marl76
