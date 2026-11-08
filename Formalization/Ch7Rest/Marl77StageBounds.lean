import Formalization.Ch7Rest.Marl77GoodBounds

/-!
# Theorem 7.7: stage inequalities on the good event

For stage `c` (game step `h = H − c`), state `s`, player `i`, with `O = outStage x c s` and
`f = fV x i` (the algorithm's values as a function of the step):
* `stage_up`: for every `b`, `sBell(devDist O i b) ≤ U + λ·sJvar(devDist O i b) + L/(λT)`;
* `stage_mean_le`, `stage_mean_ge`: `|(1/T)∑_t ⟨π^t, q̂^t⟩ − sBell(O)| ≤ λ·sJvar(O) + L/(λT)`;
* `stage_bonus`: `β ≤ L/(λT) + 2λ·sJvar(O) + λH²L/T`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge StatisticalRL.AdaptiveKL

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- The algorithm's values as a function of the game step: `fV x i h = V̄_{i,h} = vb x (H+1−h)`. -/
noncomputable def Alg.fV (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (i : Fin m) :
    ℕ → Fin S → ℝ := fun h s => al.vb x (H + 1 - h) i s

theorem Alg.fV_succ (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (i : Fin m) (c : Fin H) :
    al.fV x i (H - c + 1) = al.vb x c i := by
  funext s
  simp only [Alg.fV]
  congr 2
  have := c.isLt; omega

theorem Alg.fV_stage (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (i : Fin m) (c : Fin H)
    (s : Fin S) : al.fV x i (H - c) s = al.stageV (al.vb x c) x c i s := by
  simp only [Alg.fV]
  have h1 : H + 1 - (H - c) = (c : ℕ) + 1 := by have := c.isLt; omega
  rw [h1]
  simp only [Alg.vb, dif_pos c.isLt]

theorem Alg.fV_last (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (i : Fin m) (s : Fin S) :
    al.fV x i (H + 1) s = 0 := by
  simp [Alg.fV, Alg.vb]

theorem Alg.fV_mem (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η)
    (x : Fin al.N → Entry m S H A) (i : Fin m) (h : ℕ) (hh : h ≤ H + 1) (s : Fin S) :
    0 ≤ al.fV x i h s ∧ al.fV x i h s ≤ (H : ℝ) + 1 - h := by
  have := al.vb_mem hr hη x (H + 1 - h) i s
  refine ⟨this.1, this.2.trans ?_⟩
  rw [Nat.cast_sub hh]; push_cast; linarith

theorem Alg.qtil_eq (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) (b : Fin (A i)) :
    al.qtil G x c s t i b = sBell G i (al.fV x i) (H - c) s (devDist (al.stageProd x c s t) i b) := by
  unfold Alg.qtil sBell
  rw [al.fV_succ, hGr]
  refine sum_congr rfl fun a _ => ?_
  congr 1
  unfold Alg.gz FiniteDistribution.expectation
  simp only [mul_add, sum_add_distrib]
  rw [← sum_mul, (G.transition (H - c) s a).sum_prob, one_mul]

theorem Alg.csec_eq (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) (b : Fin (A i))
    (μ : ℝ) :
    al.csec G x c s t i b μ =
      sSec G i (al.fV x i) (H - c) s (devDist (al.stageProd x c s t) i b) μ := by
  unfold Alg.csec sSec
  rw [al.fV_succ, hGr]
  rfl

theorem Alg.mbar_eq (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) :
    al.mbar G x c s t i = sBell G i (al.fV x i) (H - c) s (al.stageProd x c s t) := by
  unfold Alg.mbar
  simp_rw [al.qtil_eq G hGr]
  exact (sBell_prod G i _ _ s (fun j => al.hedgeAt x c s j t)).symm

/-- `∑_b π(b)·csec(b, m) = sJvar(⊗π^t)`. -/
theorem Alg.sum_csec_mbar (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) :
    ∑ b, (al.hedgeAt x c s i t).prob b * al.csec G x c s t i b (al.mbar G x c s t i) =
      sJvar G i (al.fV x i) (H - c) s (al.stageProd x c s t) := by
  simp_rw [al.csec_eq G hGr]
  rw [sJvar, ← al.mbar_eq G hGr]
  exact (sSec_prod G i _ _ s (fun j => al.hedgeAt x c s j t) _).symm

theorem Alg.csec_qtil_le (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) (b : Fin (A i)) :
    al.csec G x c s t i b (al.qtil G x c s t i b) ≤ al.csec G x c s t i b (al.mbar G x c s t i) := by
  rw [al.csec_eq G hGr, al.csec_eq G hGr, al.qtil_eq G hGr]
  exact sJvar_le_sSec G i _ _ s _ _

theorem Alg.csec_nonneg (al : Alg m S H A) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) (b : Fin (A i))
    (μ : ℝ) : 0 ≤ al.csec G x c s t i b μ :=
  sum_nonneg fun a _ => mul_nonneg ((devDist _ i b).prob_nonneg a)
    (sum_nonneg fun s' _ => mul_nonneg ((G.transition _ s a).prob_nonneg s') (sq_nonneg _))

theorem prob_le_one {n : ℕ} (p : FiniteDistribution (Fin n)) (b : Fin n) : p.prob b ≤ 1 := by
  rw [← p.sum_prob]; exact single_le_sum (fun c _ => p.prob_nonneg c) (mem_univ _)

/-- The averaged round variances are dominated by the variance of the output stage law. -/
theorem Alg.avg_sJvar_le (al : Alg m S H A) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (i : Fin m) :
    ∑ t : Fin al.T, sJvar G i (al.fV x i) (H - c) s (al.stageProd x c s t) ≤
      al.T * sJvar G i (al.fV x i) (H - c) s (al.outStage x c s) := by
  have h := sJvar_avg_ge al.hT G i (al.fV x i) (H - c) s (fun t => al.stageProd x c s t)
  have hT : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  rw [div_le_iff₀ hT] at h
  unfold Alg.outStage
  linarith

section Bounds

variable (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew) (hr : al.RewOK)
  (hη : 0 < al.η) {L : ℝ} {x : Fin al.N → Entry m S H A} (hg : al.Good G al.η L x)
  (c : Fin H) (s : Fin S) (i : Fin m)
include hGr hr hη hg

theorem Alg.stage_up (hηH : al.η * H ≤ 1) (b : Fin (A i)) :
    sBell G i (al.fV x i) (H - c) s (devDist (al.outStage x c s) i b) ≤
      al.optU (al.vb x c) x c s i +
        (al.η * sJvar G i (al.fV x i) (H - c) s (devDist (al.outStage x c s) i b) +
          L / (al.η * al.T)) := by
  have hT : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  have hcH : ((c : ℕ) : ℝ) + 1 ≤ H := by have := c.isLt; exact_mod_cast this
  -- Hedge regret
  have hreg := hedge_second_order_regret (al.hA i) hη (R := (c : ℝ) + 1)
    (by nlinarith [(Nat.cast_nonneg (c : ℕ) : (0 : ℝ) ≤ c)]) (al.gain (al.vb x c) x c s i) al.T
    (fun t ht b => by
      rw [show al.gain (al.vb x c) x c s i t b = al.gain (al.vb x c) x c s i ((⟨t, ht⟩ : Fin al.T) : ℕ) b
        from rfl, al.gain_fin]
      exact (al.gz_mem hr hη x c s i _).1)
    (fun t ht b => by
      rw [show al.gain (al.vb x c) x c s i t b = al.gain (al.vb x c) x c s i ((⟨t, ht⟩ : Fin al.T) : ℕ) b
        from rfl, al.gain_fin]
      exact (al.gz_mem hr hη x c s i _).2) b
  have hU : (∑ t ∈ range al.T, al.gain (al.vb x c) x c s i t b) / al.T ≤ al.optU (al.vb x c) x c s i := by
    rw [div_le_iff₀ hT]
    unfold Alg.optU Alg.bonus
    have : ((∑ t ∈ range al.T, wmean (hedgeIter (al.hA i) al.η (al.gain (al.vb x c) x c s i) t)
        (al.gain (al.vb x c) x c s i t)) / al.T + (Real.log (A i) / (al.η * al.T) +
        al.η / al.T * ∑ t ∈ range al.T, wvar (hedgeIter (al.hA i) al.η (al.gain (al.vb x c) x c s i) t)
          (al.gain (al.vb x c) x c s i t))) * al.T =
        Real.log (A i) / al.η + ∑ t ∈ range al.T, wmean (hedgeIter (al.hA i) al.η
          (al.gain (al.vb x c) x c s i) t) (al.gain (al.vb x c) x c s i t) +
        al.η * ∑ t ∈ range al.T, wvar (hedgeIter (al.hA i) al.η (al.gain (al.vb x c) x c s i) t)
          (al.gain (al.vb x c) x c s i t) := by
      field_simp
      ring
    simp only [Alg.hedge]
    rw [this]
    exact hreg
  -- E1
  have hE := al.good_E1 G hg c s i b
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib] at hE
  have hq : ∑ t : Fin al.T, al.qtil G x c s t i b =
      al.T * sBell G i (al.fV x i) (H - c) s (devDist (al.outStage x c s) i b) := by
    simp_rw [al.qtil_eq G hGr]
    unfold Alg.outStage
    rw [sBell_devDist_avg al.hT]
    field_simp
  have hv : ∑ t : Fin al.T, al.csec G x c s t i b (al.qtil G x c s t i b) ≤
      al.T * sJvar G i (al.fV x i) (H - c) s (devDist (al.outStage x c s) i b) := by
    have h := sJvar_devDist_avg_ge al.hT G i (al.fV x i) (H - c) s (fun t => al.stageProd x c s t) b
    rw [div_le_iff₀ hT] at h
    have e : ∀ t : Fin al.T, al.csec G x c s t i b (al.qtil G x c s t i b) =
        sJvar G i (al.fV x i) (H - c) s (devDist (al.stageProd x c s t) i b) := by
      intro t; rw [al.csec_eq G hGr, al.qtil_eq G hGr]; rfl
    simp_rw [e]
    unfold Alg.outStage
    linarith
  have hgsum : ∑ t : Fin al.T, al.gain (al.vb x c) x c s i t b =
      ∑ t ∈ range al.T, al.gain (al.vb x c) x c s i t b :=
    Fin.sum_univ_eq_sum_range (fun t => al.gain (al.vb x c) x c s i t b) al.T
  rw [hq, hgsum] at hE
  -- combine
  set B := sBell G i (al.fV x i) (H - c) s (devDist (al.outStage x c s) i b)
  set J := sJvar G i (al.fV x i) (H - c) s (devDist (al.outStage x c s) i b)
  set Q := ∑ t ∈ range al.T, al.gain (al.vb x c) x c s i t b
  set Vs := ∑ t : Fin al.T, al.csec G x c s t i b (al.qtil G x c s t i b)
  have h1 : al.η * (al.T * B - Q) < L + al.η ^ 2 * Vs := by linarith
  have h2 : al.η * (al.T * B - Q) < L + al.η ^ 2 * (al.T * J) :=
    lt_of_lt_of_le h1 (by nlinarith [sq_nonneg al.η])
  have h3 : al.T * B - Q < L / al.η + al.η * (al.T * J) := by
    rw [div_add' _ _ _ hη.ne', lt_div_iff₀ hη]; nlinarith
  have h4 : B < Q / al.T + (L / (al.η * al.T) + al.η * J) := by
    have : B * al.T < Q + (L / al.η + al.η * (al.T * J)) := by linarith
    rw [← lt_div_iff₀ hT] at this
    calc B < (Q + (L / al.η + al.η * (al.T * J))) / al.T := this
      _ = Q / al.T + (L / (al.η * al.T) + al.η * J) := by field_simp
  have := hU
  linarith

end Bounds

/-- Shared bookkeeping for E2: `∑_t mbar = T·sBell(O)` and the variance term. -/
theorem Alg.sum_mbar (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (i : Fin m) :
    ∑ t : Fin al.T, al.mbar G x c s t i = al.T * sBell G i (al.fV x i) (H - c) s (al.outStage x c s) := by
  simp_rw [al.mbar_eq G hGr]
  unfold Alg.outStage
  rw [sBell_avg al.hT]
  have hT : (al.T : ℝ) ≠ 0 := by exact_mod_cast al.hT.ne'
  field_simp

theorem Alg.sum_wsq_csec_le (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (i : Fin m) :
    ∑ t : Fin al.T, ∑ b, (al.hedgeAt x c s i t).prob b ^ 2 * al.csec G x c s t i b (al.qtil G x c s t i b) ≤
      al.T * sJvar G i (al.fV x i) (H - c) s (al.outStage x c s) := by
  refine le_trans ?_ (al.avg_sJvar_le G x c s i)
  refine sum_le_sum fun t _ => ?_
  rw [← al.sum_csec_mbar G hGr]
  refine sum_le_sum fun b _ => ?_
  have hw0 := (al.hedgeAt x c s i t).prob_nonneg b
  have hw1 := prob_le_one (al.hedgeAt x c s i t) b
  have h1 := al.csec_qtil_le G hGr x c s t i b
  have h0 := al.csec_nonneg G x c s t i b (al.qtil G x c s t i b)
  calc (al.hedgeAt x c s i t).prob b ^ 2 * al.csec G x c s t i b (al.qtil G x c s t i b)
      ≤ (al.hedgeAt x c s i t).prob b * al.csec G x c s t i b (al.qtil G x c s t i b) := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hw0 hw1) h0
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hw0

theorem Alg.sum_wmean_fin (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S)
    (i : Fin m) :
    ∑ t ∈ range al.T, wmean (al.hedge (al.vb x c) x c s i t) (al.gain (al.vb x c) x c s i t) =
      ∑ t : Fin al.T, ∑ b, (al.hedgeAt x c s i t).prob b * al.gain (al.vb x c) x c s i t b :=
  (Fin.sum_univ_eq_sum_range (fun t => wmean (al.hedge (al.vb x c) x c s i t)
    (al.gain (al.vb x c) x c s i t)) al.T).symm

section Bounds2

variable (al : Alg m S H A) (G : MarkovGame m S H A) (hGr : G.reward = al.rew) (hr : al.RewOK)
  (hη : 0 < al.η) {L : ℝ} {x : Fin al.N → Entry m S H A} (hg : al.Good G al.η L x)
  (c : Fin H) (s : Fin S) (i : Fin m)
include hGr hr hη hg

theorem Alg.stage_mean_le :
    (∑ t ∈ range al.T, wmean (al.hedge (al.vb x c) x c s i t) (al.gain (al.vb x c) x c s i t)) / al.T ≤
      sBell G i (al.fV x i) (H - c) s (al.outStage x c s) +
        (al.η * sJvar G i (al.fV x i) (H - c) s (al.outStage x c s) + L / (al.η * al.T)) := by
  have hT : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  have hE := al.good_E2a G hg c s i
  have key : ∀ t : Fin al.T, ∑ b, (al.η * (al.hedgeAt x c s i t).prob b *
      (al.gain (al.vb x c) x c s i t b - al.qtil G x c s t i b) -
      al.η ^ 2 * (al.hedgeAt x c s i t).prob b ^ 2 * al.csec G x c s t i b (al.qtil G x c s t i b)) =
      al.η * (∑ b, (al.hedgeAt x c s i t).prob b * al.gain (al.vb x c) x c s i t b -
        al.mbar G x c s t i) -
      al.η ^ 2 * ∑ b, (al.hedgeAt x c s i t).prob b ^ 2 *
        al.csec G x c s t i b (al.qtil G x c s t i b) := by
    intro t
    simp only [Alg.mbar, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => by ring
  simp_rw [key] at hE
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, al.sum_mbar G hGr] at hE
  rw [al.sum_wmean_fin]
  have hZ := al.sum_wsq_csec_le G hGr x c s i
  set W := ∑ t : Fin al.T, ∑ b, (al.hedgeAt x c s i t).prob b * al.gain (al.vb x c) x c s i t b
  set B := sBell G i (al.fV x i) (H - c) s (al.outStage x c s)
  set J := sJvar G i (al.fV x i) (H - c) s (al.outStage x c s)
  set Z := ∑ t : Fin al.T, ∑ b, (al.hedgeAt x c s i t).prob b ^ 2 *
    al.csec G x c s t i b (al.qtil G x c s t i b)
  have h1 : al.η * (W - al.T * B) < L + al.η ^ 2 * (al.T * J) := by
    nlinarith [sq_nonneg al.η]
  have h2 : W - al.T * B < L / al.η + al.η * (al.T * J) := by
    rw [div_add' _ _ _ hη.ne', lt_div_iff₀ hη]; nlinarith
  rw [div_le_iff₀ hT]
  have : (B + (al.η * J + L / (al.η * al.T))) * al.T = al.T * B + al.η * (al.T * J) + L / al.η := by
    field_simp; ring
  rw [this]; linarith

theorem Alg.stage_mean_ge :
    sBell G i (al.fV x i) (H - c) s (al.outStage x c s) -
        (al.η * sJvar G i (al.fV x i) (H - c) s (al.outStage x c s) + L / (al.η * al.T)) ≤
      (∑ t ∈ range al.T, wmean (al.hedge (al.vb x c) x c s i t) (al.gain (al.vb x c) x c s i t)) /
        al.T := by
  have hT : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  have hE := al.good_E2b G hg c s i
  have key : ∀ t : Fin al.T, ∑ b, (al.η * (al.hedgeAt x c s i t).prob b *
      (al.qtil G x c s t i b - al.gain (al.vb x c) x c s i t b) -
      al.η ^ 2 * (al.hedgeAt x c s i t).prob b ^ 2 * al.csec G x c s t i b (al.qtil G x c s t i b)) =
      al.η * (al.mbar G x c s t i -
        ∑ b, (al.hedgeAt x c s i t).prob b * al.gain (al.vb x c) x c s i t b) -
      al.η ^ 2 * ∑ b, (al.hedgeAt x c s i t).prob b ^ 2 *
        al.csec G x c s t i b (al.qtil G x c s t i b) := by
    intro t
    simp only [Alg.mbar, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => by ring
  simp_rw [key] at hE
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, al.sum_mbar G hGr] at hE
  rw [al.sum_wmean_fin]
  have hZ := al.sum_wsq_csec_le G hGr x c s i
  set W := ∑ t : Fin al.T, ∑ b, (al.hedgeAt x c s i t).prob b * al.gain (al.vb x c) x c s i t b
  set B := sBell G i (al.fV x i) (H - c) s (al.outStage x c s)
  set J := sJvar G i (al.fV x i) (H - c) s (al.outStage x c s)
  set Z := ∑ t : Fin al.T, ∑ b, (al.hedgeAt x c s i t).prob b ^ 2 *
    al.csec G x c s t i b (al.qtil G x c s t i b)
  have h1 : al.η * (al.T * B - W) < L + al.η ^ 2 * (al.T * J) := by
    nlinarith [sq_nonneg al.η]
  have h2 : al.T * B - W < L / al.η + al.η * (al.T * J) := by
    rw [div_add' _ _ _ hη.ne', lt_div_iff₀ hη]; nlinarith
  rw [le_div_iff₀ hT]
  have : (B - (al.η * J + L / (al.η * al.T))) * al.T = al.T * B - al.η * (al.T * J) - L / al.η := by
    field_simp; ring
  rw [this]; linarith

theorem Alg.stage_bonus (hlog : Real.log (A i) ≤ L) :
    al.bonus (al.vb x c) x c s i ≤
      L / (al.η * al.T) + 2 * al.η * sJvar G i (al.fV x i) (H - c) s (al.outStage x c s) +
        al.η * (H : ℝ) ^ 2 * L / al.T := by
  have hT : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  have hH : (0 : ℝ) < H := by have := c.isLt; exact_mod_cast (by omega : 0 < H)
  have hE := al.good_E3 G hg c s i
  -- variance about the predictable point `m`
  have hvar : ∀ t : Fin al.T, wvar (al.hedge (al.vb x c) x c s i t) (al.gain (al.vb x c) x c s i t) ≤
      ∑ b, (al.hedgeAt x c s i t).prob b * (al.gain (al.vb x c) x c s i t b - al.mbar G x c s t i) ^ 2 :=
    fun t => sum_sq_sub_mean_le (fun b => (al.hedgeAt x c s i t).prob b)
      (al.gain (al.vb x c) x c s i t) (al.hedgeAt x c s i t).sum_prob _
  have key : ∀ t : Fin al.T, ∑ b, ((al.hedgeAt x c s i t).prob b *
      (al.gain (al.vb x c) x c s i t b - al.mbar G x c s t i) ^ 2 / (H : ℝ) ^ 2 -
      2 * ((al.hedgeAt x c s i t).prob b / (H : ℝ) ^ 2 *
        al.csec G x c s t i b (al.mbar G x c s t i))) =
      (∑ b, (al.hedgeAt x c s i t).prob b *
        (al.gain (al.vb x c) x c s i t b - al.mbar G x c s t i) ^ 2) / (H : ℝ) ^ 2 -
      2 * sJvar G i (al.fV x i) (H - c) s (al.stageProd x c s t) / (H : ℝ) ^ 2 := by
    intro t
    rw [← al.sum_csec_mbar G hGr, sum_sub_distrib, sum_div, mul_div_assoc, sum_div, mul_sum]
    congr 1
    refine sum_congr rfl fun b _ => by ring
  simp_rw [key] at hE
  rw [sum_sub_distrib, ← sum_div] at hE
  have e2 : ∑ t : Fin al.T, 2 * sJvar G i (al.fV x i) (H - c) s (al.stageProd x c s t) / (H : ℝ) ^ 2 =
      (2 * ∑ t : Fin al.T, sJvar G i (al.fV x i) (H - c) s (al.stageProd x c s t)) / (H : ℝ) ^ 2 := by
    rw [← sum_div, ← mul_sum]
  rw [e2, ← sub_div, div_lt_iff₀ (by positivity)] at hE
  have hJ := al.avg_sJvar_le G x c s i
  set Y := ∑ t : Fin al.T, ∑ b, (al.hedgeAt x c s i t).prob b *
    (al.gain (al.vb x c) x c s i t b - al.mbar G x c s t i) ^ 2
  set J := sJvar G i (al.fV x i) (H - c) s (al.outStage x c s)
  have hY : Y < (H : ℝ) ^ 2 * L + 2 * (al.T * J) := by nlinarith
  have hV : ∑ t ∈ range al.T, wvar (al.hedge (al.vb x c) x c s i t) (al.gain (al.vb x c) x c s i t) ≤ Y := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => wvar (al.hedge (al.vb x c) x c s i t)
      (al.gain (al.vb x c) x c s i t)) al.T]
    exact sum_le_sum fun t _ => hvar t
  unfold Alg.bonus
  have hA : Real.log (A i) / (al.η * al.T) ≤ L / (al.η * al.T) :=
    div_le_div_of_nonneg_right hlog (by positivity)
  have hB : al.η / al.T * ∑ t ∈ range al.T, wvar (al.hedge (al.vb x c) x c s i t)
      (al.gain (al.vb x c) x c s i t) ≤ al.η / al.T * ((H : ℝ) ^ 2 * L + 2 * (al.T * J)) :=
    mul_le_mul_of_nonneg_left (hV.trans hY.le) (by positivity)
  have hC : al.η / al.T * ((H : ℝ) ^ 2 * L + 2 * (al.T * J)) =
      2 * al.η * J + al.η * (H : ℝ) ^ 2 * L / al.T := by
    field_simp; ring
  linarith

end Bounds2

end StatisticalRL.Ch7Rest.Marl77
