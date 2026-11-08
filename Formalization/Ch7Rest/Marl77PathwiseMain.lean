import Formalization.Ch7Rest.Marl77Pathwise

/-!
# Theorem 7.7: the gap of the output on the good event

`Alg.gapJ_le_of_good`: on `Good G η L x`, with `1 ≤ H`, `η H ≤ 1/4`, `0 ≤ L` and
`log A_i ≤ L` for all `i`,

  `gapJ G (out x) ≤ 40ηH² + 16H²L/T + 3HL/(ηT) + ηH³L/T`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge StatisticalRL.AdaptiveKL

variable {m S H : ℕ} {A : Fin m → ℕ}

theorem Alg.out_eq (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (t : ℕ) (h1 : 1 ≤ t)
    (h2 : t ≤ H) (s : Fin S) :
    al.out x t s = al.outStage x ⟨H - t, by omega⟩ s := by
  simp only [Alg.out, dif_pos (show H - t < H by omega)]

theorem Alg.sBell_le_stage (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew)
    (hr : al.RewOK) (hη : 0 < al.η) (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S)
    (i : Fin m) (μ : FiniteDistribution (JointAction m A)) :
    sBell G i (al.fV x i) (H - c) s μ ≤ (c : ℝ) + 1 := by
  unfold sBell
  rw [al.fV_succ, hGr]
  calc ∑ a, μ.prob a * (al.rew i (H - c) s a + (G.transition (H - c) s a).expectation (al.vb x c i))
      ≤ ∑ a, μ.prob a * ((c : ℝ) + 1) := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (by
        have h1 := (al.rew_stage hr c i s a).2
        have h2 : (G.transition (H - c) s a).expectation (al.vb x c i) ≤ (c : ℝ) :=
          FiniteDistribution.expectation_le_const _ fun s' => (al.vb_mem hr hη x c i s').2
        linarith) (μ.prob_nonneg a)
    _ = (c : ℝ) + 1 := by rw [← sum_mul, μ.sum_prob, one_mul]

section Main

variable (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew) (hr : al.RewOK)
  (hη : 0 < al.η) {L : ℝ} {x : Fin al.N → Entry m S H A} (hg : al.Good G al.η L x)
include hGr hr hη hg

/-- Upper step for a deterministic deviation. -/
theorem Alg.upper_step (hηH : al.η * H ≤ 1) (hL : 0 ≤ L) (i : Fin m) (β : ℕ → Fin S → Fin (A i))
    (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ H) (s : Fin S) :
    bellJ G (deviate (al.out x) i (fun h s => EnvironmentStage.pointMass (β h s))) i (al.fV x i) t s -
        al.fV x i t s ≤
      al.η * jvarJ G (deviate (al.out x) i (fun h s => EnvironmentStage.pointMass (β h s))) i
        (al.fV x i) t s + L / (al.η * al.T) := by
  set c : Fin H := ⟨H - t, by omega⟩ with hc
  have hct : H - (c : ℕ) = t := by simp only [hc]; omega
  rw [bellJ_eq_sBell, jvarJ_eq_sJvar, deviate_pointMass_eq, al.out_eq x t h1 h2 s]
  have hup := al.stage_up G hGr hr hη hg c s i hηH (β t s)
  have hle := al.sBell_le_stage G hGr hr hη x c s i (devDist (al.outStage x c s) i (β t s))
  have hf := al.fV_stage x i c s
  rw [hct] at hup hle hf
  have hE : 0 ≤ al.η * sJvar G i (al.fV x i) t s (devDist (al.outStage x c s) i (β t s)) +
      L / (al.η * al.T) :=
    add_nonneg (mul_nonneg hη.le (sSec_nonneg _ _ _ _ _ _ _))
      (div_nonneg hL (mul_nonneg hη.le (Nat.cast_nonneg _)))
  rw [hf]
  have : sBell G i (al.fV x i) t s (devDist (al.outStage x c s) i (β t s)) -
      (al.η * sJvar G i (al.fV x i) t s (devDist (al.outStage x c s) i (β t s)) +
        L / (al.η * al.T)) ≤ al.stageV (al.vb x c) x c i s := le_min (by linarith) (by linarith)
  linarith

/-- Lower step for the output policy. -/
theorem Alg.lower_step (hlog : ∀ i, Real.log (A i) ≤ L) (i : Fin m) (t : ℕ) (h1 : 1 ≤ t)
    (h2 : t ≤ H) (s : Fin S) :
    al.fV x i t s - bellJ G (al.out x) i (al.fV x i) t s ≤
      3 * al.η * jvarJ G (al.out x) i (al.fV x i) t s +
        (2 * (L / (al.η * al.T)) + al.η * (H : ℝ) ^ 2 * L / al.T) := by
  set c : Fin H := ⟨H - t, by omega⟩ with hc
  have hct : H - (c : ℕ) = t := by simp only [hc]; omega
  rw [bellJ_eq_sBell, jvarJ_eq_sJvar, al.out_eq x t h1 h2 s]
  have hm := al.stage_mean_le G hGr hr hη hg c s i
  have hb := al.stage_bonus G hGr hr hη hg c s i (hlog i)
  have hf := al.fV_stage x i c s
  rw [hct] at hm hb hf
  rw [hf]
  have hU : al.stageV (al.vb x c) x c i s ≤ al.optU (al.vb x c) x c s i := min_le_right _ _
  unfold Alg.optU at hU
  linarith

/-- Lower bound on `f − bellJ` for the output policy. -/
theorem Alg.lower_delta (hL : 0 ≤ L) (i : Fin m) (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ H) (s : Fin S) :
    max (-(al.fV x i t s - bellJ G (al.out x) i (al.fV x i) t s)) 0 ≤
      al.η * jvarJ G (al.out x) i (al.fV x i) t s + L / (al.η * al.T) := by
  set c : Fin H := ⟨H - t, by omega⟩ with hc
  have hct : H - (c : ℕ) = t := by simp only [hc]; omega
  rw [bellJ_eq_sBell, jvarJ_eq_sJvar, al.out_eq x t h1 h2 s]
  have hm := al.stage_mean_ge G hGr hr hη hg c s i
  have hle := al.sBell_le_stage G hGr hr hη x c s i (al.outStage x c s)
  have hf := al.fV_stage x i c s
  rw [hct] at hm hle hf
  rw [hf]
  have hE : 0 ≤ al.η * sJvar G i (al.fV x i) t s (al.outStage x c s) + L / (al.η * al.T) :=
    add_nonneg (mul_nonneg hη.le (sSec_nonneg _ _ _ _ _ _ _))
      (div_nonneg hL (mul_nonneg hη.le (Nat.cast_nonneg _)))
  have hb := al.bonus_nonneg hη (al.vb x c) x c s i
  have hUge : sBell G i (al.fV x i) t s (al.outStage x c s) -
      (al.η * sJvar G i (al.fV x i) t s (al.outStage x c s) + L / (al.η * al.T)) ≤
      al.stageV (al.vb x c) x c i s := by
    refine le_min (by linarith) ?_
    unfold Alg.optU
    linarith
  refine max_le (by linarith) hE

theorem Alg.rew_window (i : Fin m) :
    ∀ t, 1 ≤ t → t ≤ H → ∀ s a, 0 ≤ G.reward i t s a ∧ G.reward i t s a ≤ 1 := by
  intro t h1 h2 s a
  rw [hGr]; exact hr i t s a h1 h2

theorem Alg.fV_window (i : Fin m) :
    ∀ t, 1 ≤ t → t ≤ H → ∀ s, 0 ≤ al.fV x i t s ∧ al.fV x i t s ≤ H := by
  intro t h1 h2 s
  have := al.fV_mem hr hη x i t (by omega) s
  refine ⟨this.1, this.2.trans ?_⟩
  have : (1 : ℝ) ≤ t := by exact_mod_cast h1
  linarith

/-- The per-player gap bound. -/
theorem Alg.player_gap_le (hH : 1 ≤ H) (hηH : al.η * H ≤ 1 / 4) (hL : 0 ≤ L)
    (hlog : ∀ i, Real.log (A i) ≤ L) (i : Fin m) (s : Fin S) :
    bestResponseValueJ G (al.out x) i s - valueJ G (al.out x) i 1 H s ≤
      40 * al.η * (H : ℝ) ^ 2 + 16 * (H : ℝ) ^ 2 * L / al.T + 3 * H * L / (al.η * al.T) +
        al.η * (H : ℝ) ^ 3 * L / al.T := by
  have hT : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hηH1 : al.η * H ≤ 1 := by linarith
  set κ := L / (al.η * al.T) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg hL (by positivity)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → Fin S → Fin (A i),
      brPolicy G (al.out x) i (al.hA i) = fun h s => EnvironmentStage.pointMass (β h s) := ⟨_, rfl⟩
  rw [bestResponseValueJ_eq_brPolicy G (al.out x) i (al.hA i) s, hβ]
  set ρ := deviate (al.out x) i (fun h s => EnvironmentStage.pointMass (β h s))
  set f := al.fV x i
  have hfH : ∀ s, f (H + 1) s = 0 := al.fV_last x i
  -- upper side
  have hup := valueJ_sub_le_evalJ G ρ i f (fun t s => al.η * jvarJ G ρ i f t s + κ) hfH
    (fun t h1 h2 s => al.upper_step G hGr hr hη hg hηH1 hL i β t h1 h2 s) H 1 (by omega) le_rfl s
  have hupE := evalJ_le_affine G ρ (fun t s _ => jvarJ G ρ i f t s)
    (fun t s _ => al.η * jvarJ G ρ i f t s + κ) al.η κ H 1 (fun _ _ _ _ _ => le_rfl) s
  have hW := evalJ_jvarJ_self_bound G ρ i f hH (al.fV_window G hGr hr hη hg i) hfH
    (al.rew_window G hGr hr hη hg i) hη.le hηH (κ := κ) (fun t h1 h2 s => max_le (by
      have := al.upper_step G hGr hr hη hg hηH1 hL i β t h1 h2 s; linarith) (by
        have : 0 ≤ jvarJ G ρ i f t s := jvarJ_nonneg G ρ i f t s
        positivity)) s
  -- lower side
  have hlow := sub_valueJ_le_evalJ G (al.out x) i f
    (fun t s => 3 * al.η * jvarJ G (al.out x) i f t s +
      (2 * κ + al.η * (H : ℝ) ^ 2 * L / al.T)) hfH
    (fun t h1 h2 s => al.lower_step G hGr hr hη hg hlog i t h1 h2 s) H 1 (by omega) le_rfl s
  have hlowE := evalJ_le_affine G (al.out x) (fun t s _ => jvarJ G (al.out x) i f t s)
    (fun t s _ => 3 * al.η * jvarJ G (al.out x) i f t s + (2 * κ + al.η * (H : ℝ) ^ 2 * L / al.T))
    (3 * al.η) (2 * κ + al.η * (H : ℝ) ^ 2 * L / al.T) H 1 (fun _ _ _ _ _ => le_rfl) s
  have hW' := evalJ_jvarJ_self_bound G (al.out x) i f hH (al.fV_window G hGr hr hη hg i) hfH
    (al.rew_window G hGr hr hη hg i) hη.le hηH (κ := κ)
    (fun t h1 h2 s => al.lower_delta G hGr hr hη hg hL i t h1 h2 s) s
  -- combine
  set W := evalJ G ρ (fun t s _ => jvarJ G ρ i f t s) 1 H s
  set W' := evalJ G (al.out x) (fun t s _ => jvarJ G (al.out x) i f t s) 1 H s
  have hηκ : al.η * κ = L / al.T := by rw [hκ]; field_simp
  have hHκ : (H : ℝ) * κ = H * L / (al.η * al.T) := by rw [hκ]; ring
  have e1 : al.η * W ≤ al.η * (10 * (H : ℝ) ^ 2 + 4 * H * (H * κ)) :=
    mul_le_mul_of_nonneg_left hW hη.le
  have e2 : 3 * al.η * W' ≤ 3 * al.η * (10 * (H : ℝ) ^ 2 + 4 * H * (H * κ)) :=
    mul_le_mul_of_nonneg_left hW' (by positivity)
  have e3 : al.η * (10 * (H : ℝ) ^ 2 + 4 * H * (H * κ)) = 10 * al.η * H ^ 2 + 4 * H ^ 2 * (L / al.T) := by
    rw [← hηκ]; ring
  have e4 : al.η * (H : ℝ) ^ 2 * L / al.T * H = al.η * (H : ℝ) ^ 3 * L / al.T := by ring
  have e5 : 16 * (H : ℝ) ^ 2 * L / al.T = 16 * H ^ 2 * (L / al.T) := by ring
  have e6 : 3 * (H : ℝ) * L / (al.η * al.T) = 3 * (H * κ) := by rw [hHκ]; ring
  rw [e5, e6]
  nlinarith

/-- The gap of the output on the good event. -/
theorem Alg.gapJ_le_of_good (hH : 1 ≤ H) (hηH : al.η * H ≤ 1 / 4) (hL : 0 ≤ L)
    (hlog : ∀ i, Real.log (A i) ≤ L) :
    gapJ G (al.out x) ≤
      40 * al.η * (H : ℝ) ^ 2 + 16 * (H : ℝ) ^ 2 * L / al.T + 3 * H * L / (al.η * al.T) +
        al.η * (H : ℝ) ^ 3 * L / al.T := by
  have hT : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  have h0 : 0 ≤ 40 * al.η * (H : ℝ) ^ 2 + 16 * (H : ℝ) ^ 2 * L / al.T + 3 * H * L / (al.η * al.T) +
      al.η * (H : ℝ) ^ 3 * L / al.T := by positivity
  unfold gapJ
  refine Real.iSup_le (fun s => Real.iSup_le (fun i => ?_) h0) h0
  exact al.player_gap_le G hGr hr hη hg hH hηH hL hlog i s

end Main

end StatisticalRL.Ch7Rest.Marl77
