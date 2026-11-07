import Formalization.Online.LowerBound.TestingTools

/-!
# Corrected Theorem 7.8: abstract one-coordinate testing bound

* `finite_event_pinsker`: `2 (P(E) − Q(E))² ≤ KL(P ‖ Q)` for finite laws (from
  `PrelimFano.event_sq_gap_le_klDiv`).
* `coord_bayes_le`: for laws `P_b` (`b ∈ Fin n`, `n ≥ 2`) with a reference `ref`, disjoint events
  `hit_b`, and `KL(P_ref ‖ P_j) ≤ K_j`, the prior-weighted success probability with weights
  `w(ref) = 1/2`, `w(j) = 1/(2(n−1))` is at most `17/32 + (∑_{j ≠ ref} K_j)/(n − 1)`. Pinsker is
  linearised as `d ≤ 2 KL + 1/16`, so no square roots appear.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL AdaptiveKL GenerativeLowerBound

/-- Event probability under a finite law. -/
noncomputable def evProb {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω) (E : Ω → Prop)
    [DecidablePred E] : ℝ :=
  ∑ x, d.prob x * (if E x then 1 else 0)

theorem evProb_nonneg {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω) (E : Ω → Prop)
    [DecidablePred E] : 0 ≤ evProb d E :=
  Finset.sum_nonneg fun x _ => mul_nonneg (d.prob_nonneg x) (by split_ifs <;> norm_num)

theorem finiteKLExpression_nonneg' {Ω : Type*} [Fintype Ω] (d d' : FiniteDistribution Ω)
    (hac : ∀ x, d'.prob x = 0 → d.prob x = 0) : 0 ≤ finiteKLExpression d.prob d'.prob := by
  letI : MeasurableSpace Ω := ⊤
  haveI : MeasurableSingletonClass Ω := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  rw [← (toMeasure_klDiv d d' hac).2]
  exact ENNReal.toReal_nonneg

/-- Event form of Pinsker's inequality for finite laws. -/
theorem finite_event_pinsker {Ω : Type*} [Fintype Ω] (d d' : FiniteDistribution Ω)
    (hac : ∀ x, d'.prob x = 0 → d.prob x = 0) (E : Ω → Prop) [DecidablePred E] :
    2 * (evProb d E - evProb d' E) ^ 2 ≤ finiteKLExpression d.prob d'.prob := by
  classical
  letI : MeasurableSpace Ω := ⊤
  haveI : MeasurableSingletonClass Ω := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hreal : ∀ e : FiniteDistribution Ω, e.toPMF.toMeasure.real {x | E x} = evProb e E := by
    intro e
    have hset : {x | E x} = ((Finset.univ.filter fun x => E x : Finset Ω) : Set Ω) := by
      ext x; simp
    rw [hset, ← sum_measureReal_singleton, Finset.sum_filter]
    unfold evProb
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [toMeasure_real_singleton]
    split_ifs <;> simp
  have h := PrelimFano.event_sq_gap_le_klDiv d.toPMF.toMeasure d'.toPMF.toMeasure
    (A := {x | E x}) MeasurableSpace.measurableSet_top
  rw [hreal, hreal] at h
  obtain ⟨hne, heq⟩ := toMeasure_klDiv d d' hac
  rw [← ENNReal.ofReal_toReal hne, heq] at h
  exact (ENNReal.ofReal_le_ofReal_iff (finiteKLExpression_nonneg' d d' hac)).1 h

/-- Prior weights on `Fin n`: `1/2` on the reference, `1/(2(n−1))` on each alternative. -/
noncomputable def wt {n : ℕ} (ref b : Fin n) : ℝ :=
  if b = ref then 1 / 2 else 1 / (2 * ((n : ℝ) - 1))

theorem wt_nonneg {n : ℕ} (hn : 2 ≤ n) (ref b : Fin n) : 0 ≤ wt ref b := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold wt; split_ifs
  · norm_num
  · exact div_nonneg zero_le_one (by linarith)

theorem sum_wt {n : ℕ} (hn : 2 ≤ n) (ref : Fin n) : ∑ b, wt ref b = 1 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ref)]
  have : ∀ b ∈ Finset.univ.erase ref, wt ref b = 1 / (2 * ((n : ℝ) - 1)) := by
    intro b hb
    simp [wt, Finset.ne_of_mem_erase hb]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
  simp only [wt, if_true, Nat.cast_one]
  have : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **One-coordinate Bayes bound** (linearised Le Cam/Pinsker over `n − 1` needles). -/
theorem coord_bayes_le {Ω : Type*} [Fintype Ω] {n : ℕ} (hn : 2 ≤ n) (ref : Fin n)
    (P : Fin n → FiniteDistribution Ω) (hit : Fin n → Ω → Prop) [∀ b, DecidablePred (hit b)]
    (hdisj : ∀ x, ∑ b, (if hit b x then (1 : ℝ) else 0) ≤ 1)
    (hac : ∀ j x, (P j).prob x = 0 → (P ref).prob x = 0)
    (K : Fin n → ℝ) (hK : ∀ j, j ≠ ref → finiteKLExpression (P ref).prob (P j).prob ≤ K j) :
    ∑ b, wt ref b * evProb (P b) (hit b) ≤
      17 / 32 + (∑ j ∈ Finset.univ.erase ref, K j) / ((n : ℝ) - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set M : ℝ := (n : ℝ) - 1 with hM
  have hM1 : 1 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  -- per-needle linearised Pinsker
  have hneedle : ∀ j, j ≠ ref →
      evProb (P j) (hit j) ≤ evProb (P ref) (hit j) + 2 * K j + 1 / 16 := by
    intro j hj
    have hp := finite_event_pinsker (P ref) (P j) (hac j) (hit j)
    have hk := hK j hj
    nlinarith [sq_nonneg (2 * (evProb (P j) (hit j) - evProb (P ref) (hit j)) - 1 / 4)]
  -- total reference success
  have htot : evProb (P ref) (hit ref) + ∑ j ∈ Finset.univ.erase ref, evProb (P ref) (hit j) ≤ 1 := by
    rw [Finset.add_sum_erase _ (fun b => evProb (P ref) (hit b)) (Finset.mem_univ ref)]
    unfold evProb
    rw [Finset.sum_comm]
    calc ∑ x, ∑ b, (P ref).prob x * (if hit b x then (1 : ℝ) else 0)
        ≤ ∑ x, (P ref).prob x * 1 := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hdisj x) ((P ref).prob_nonneg x)
      _ = 1 := by simp_rw [mul_one]; exact (P ref).sum_prob
  have hcard : ((Finset.univ.erase ref).card : ℝ) = M := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]
    simp [hM]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ref)]
  have hw : ∀ j ∈ Finset.univ.erase ref, wt ref j = 1 / (2 * M) := by
    intro j hj
    simp [wt, Finset.ne_of_mem_erase hj, hM]
  rw [Finset.sum_congr rfl fun j hj => by rw [hw j hj]]
  simp only [wt, if_true]
  have hsum : ∑ j ∈ Finset.univ.erase ref, 1 / (2 * M) * evProb (P j) (hit j) ≤
      1 / (2 * M) * (∑ j ∈ Finset.univ.erase ref, evProb (P ref) (hit j) +
        2 * ∑ j ∈ Finset.univ.erase ref, K j + M / 16) := by
    have : 1 / (2 * M) * (∑ j ∈ Finset.univ.erase ref, evProb (P ref) (hit j) +
        2 * ∑ j ∈ Finset.univ.erase ref, K j + M / 16) =
        ∑ j ∈ Finset.univ.erase ref, 1 / (2 * M) * (evProb (P ref) (hit j) + 2 * K j + 1 / 16) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard,
        ← Finset.mul_sum]
      ring
    rw [this]
    exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
      (hneedle j (Finset.ne_of_mem_erase hj)) (by positivity)
  set p0 := evProb (P ref) (hit ref)
  set R := ∑ j ∈ Finset.univ.erase ref, evProb (P ref) (hit j)
  set Ks := ∑ j ∈ Finset.univ.erase ref, K j
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => evProb_nonneg _ _
  have hp0 : 0 ≤ p0 := evProb_nonneg _ _
  have hfrac : 1 / (2 * M) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have e1 : 1 / (2 * M) * (R + 2 * Ks + M / 16) = 1 / (2 * M) * R + Ks / M + 1 / 32 := by
    field_simp; ring
  have h2 : 1 / (2 * M) * R ≤ 1 / 2 * R := mul_le_mul_of_nonneg_right hfrac hR0
  linarith

/-- At most one value can carry probability more than `1/2`. -/
theorem sum_ite_half_lt_le_one {n : ℕ} (d : Fin n → ℝ) (hd : ∀ b, 0 ≤ d b) (hs : ∑ b, d b = 1) :
    ∑ b, (if 1 / 2 < d b then (1 : ℝ) else 0) ≤ 1 := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter fun b => 1 / 2 < d b).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have : d a + d b ≤ ∑ c, d c := by
      rw [← Finset.sum_pair hab]
      exact Finset.sum_le_univ_sum_of_nonneg hd
    linarith
  exact_mod_cast hcard

end StatisticalRL.Ch7Rest.Marl
