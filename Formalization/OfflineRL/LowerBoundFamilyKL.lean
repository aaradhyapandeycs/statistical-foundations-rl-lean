import Formalization.OfflineRL.LowerBoundFamilyDefinitions
import Formalization.Probability.EmpiricalRow
import Formalization.Generative.GenerativeLowerBoundKLAffinity
import Formalization.Generative.GenerativeLowerBoundBernoulli

/-!
# Transition KL bound for the offline hard family (`lem:transition-KL-bound-infinite`)

`chapters/offlineRL.tex:2835–2865`, proof `:5680ff`. At a positive state the two candidate
rows differ only in the self-loop probability, so their KL divergence equals a Bernoulli KL
divergence, which Lemma 2.13 (clause 1) bounds quadratically. The resulting universal constant
is `c₃ = 16 · 336²`.

The printed proof bounds `KL(Bern(u) ‖ Bern(v))` by `(u-v)²/(u(1-v))`, which is not one of the two
quadratic bounds of Lemma 2.13; this formalization instead uses `(u-v)²/(v(1-v))` (clause 1),
which yields the same final form with the stated constant.
-/

open MeasureTheory
open scoped BigOperators ENNReal
namespace StatisticalRL.OfflineRL.LowerBound

local instance lbStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

local instance lbStateSingleton (m : ℕ) : MeasurableSingletonClass (Option (Fin m)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem lb_rowMeasure_real_singleton {m : ℕ} (d : FiniteDistribution (Option (Fin m)))
    (x : Option (Fin m)) : d.rowMeasure.real {x} = d.prob x := by
  rw [measureReal_def, FiniteDistribution.rowMeasure,
    d.toPMF.toMeasure_apply_singleton x (measurableSet_singleton x)]
  simp [FiniteDistribution.toPMF_apply, ENNReal.toReal_ofReal, d.prob_nonneg x]

theorem lbMu_pos {C : ℝ} {m : ℕ} (hC : 2 < C) (hm : 1 ≤ m) (t : Option (Fin m)) :
    0 < lbMu C m t := by
  cases t with
  | none =>
    simp only [lbMu]
    have : 1 / C < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  | some _ =>
    simp only [lbMu]
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (0 : ℝ) < C := by linarith
    positivity

theorem lbMu_sum {C : ℝ} {m : ℕ} (hC : 2 < C) (hm : 1 ≤ m) : ∑ t, lbMu C m t = 1 := by
  have hmR : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    exact this.ne'
  have hC0 : C ≠ 0 := by intro h; rw [h] at hC; norm_num at hC
  simp only [Fintype.sum_option, lbMu, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

theorem lbMu_some_lt_one {C : ℝ} {m : ℕ} (hC : 2 < C) (hm : 1 ≤ m) (i : Fin m) :
    lbMu C m (some i) < 1 := by
  simp only [lbMu]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [div_lt_one (by positivity)]
  nlinarith

/-- KL between two mixed rows at a positive state is a Bernoulli KL divergence. -/
theorem lbRow_klDiv_eq {C : ℝ} {m : ℕ} (hC : 2 < C) (hm : 1 ≤ m) (i : Fin m) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    let μo := lbMu C m (some i)
    InformationTheory.klDiv (lbRow C m hC hm (some i) x hx0 hx1).rowMeasure
        (lbRow C m hC hm (some i) y hy0 hy1.le).rowMeasure ≠ ∞ ∧
    (InformationTheory.klDiv (lbRow C m hC hm (some i) x hx0 hx1).rowMeasure
        (lbRow C m hC hm (some i) y hy0 hy1.le).rowMeasure).toReal =
      StatisticalRL.GenerativeLowerBound.bernoulliKLExpression (x + (1 - x) * μo)
        (y + (1 - y) * μo) := by
  intro μo
  set rx := lbRow C m hC hm (some i) x hx0 hx1
  set ry := lbRow C m hC hm (some i) y hy0 hy1.le
  have hμpos := lbMu_pos hC hm
  have hry : ∀ t, 0 < ry.prob t := by
    intro t
    change 0 < y * (if t = some i then 1 else 0) + (1 - y) * lbMu C m t
    have h1 : 0 < (1 - y) * lbMu C m t := mul_pos (by linarith) (hμpos t)
    have h2 : 0 ≤ y * (if t = some i then (1 : ℝ) else 0) := by
      apply mul_nonneg hy0; split <;> norm_num
    linarith
  have hν : ∀ t, ry.rowMeasure {t} ≠ 0 := by
    intro t h
    have := lb_rowMeasure_real_singleton ry t
    rw [measureReal_def, h] at this
    simp at this
    linarith [hry t]
  have hac := StatisticalRL.GenerativeLowerBound.finite_fullSupport_ac rx.rowMeasure
    ry.rowMeasure hν
  refine ⟨InformationTheory.klDiv_ne_top_iff.mpr ⟨hac, Integrable.of_finite⟩, ?_⟩
  rw [StatisticalRL.GenerativeLowerBound.finite_klDiv_eq_expression _ _ hν]
  unfold StatisticalRL.GenerativeLowerBound.finiteKLExpression
  simp only [lb_rowMeasure_real_singleton]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (some i))]
  have hsplit : ∀ t ∈ Finset.univ.erase (some i),
      rx.prob t * Real.log (rx.prob t / ry.prob t) =
        lbMu C m t * ((1 - x) * Real.log ((1 - x) / (1 - y))) := by
    intro t ht
    have hne : t ≠ some i := Finset.ne_of_mem_erase ht
    change (x * (if t = some i then 1 else 0) + (1 - x) * lbMu C m t) *
        Real.log ((x * (if t = some i then 1 else 0) + (1 - x) * lbMu C m t) /
          (y * (if t = some i then 1 else 0) + (1 - y) * lbMu C m t)) = _
    simp only [hne, if_false, mul_zero, zero_add]
    have hμ := (hμpos t).ne'
    rw [mul_div_mul_right _ _ hμ]
    ring
  rw [Finset.sum_congr rfl hsplit, ← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ _),
    lbMu_sum hC hm]
  change (x * (if some i = some i then 1 else 0) + (1 - x) * μo) *
      Real.log ((x * (if some i = some i then 1 else 0) + (1 - x) * μo) /
        (y * (if some i = some i then 1 else 0) + (1 - y) * μo)) +
      (1 - μo) * ((1 - x) * Real.log ((1 - x) / (1 - y))) = _
  simp only [if_true, mul_one]
  unfold StatisticalRL.GenerativeLowerBound.bernoulliKLExpression
  have hμo1 : μo < 1 := lbMu_some_lt_one hC hm i
  have hfac : (1 - (x + (1 - x) * μo)) / (1 - (y + (1 - y) * μo)) = (1 - x) / (1 - y) := by
    have h1 : 1 - (x + (1 - x) * μo) = (1 - x) * (1 - μo) := by ring
    have h2 : 1 - (y + (1 - y) * μo) = (1 - y) * (1 - μo) := by ring
    rw [h1, h2, mul_div_mul_right _ _ (by linarith : (1 : ℝ) - μo ≠ 0)]
  rw [hfac]
  ring

/-- Quadratic bound for the Bernoulli KL of two mixed rows. -/
theorem lb_bernoulli_mixed_le {μo x y γ : ℝ} (hμ0 : 0 < μo) (hμ1 : μo < 1)
    (hx0 : 0 < x) (hx1 : x < 1) (hy : 1 / 2 ≤ y) (hγ1 : γ < 1) (hyγ : (1 - γ) / 2 ≤ 1 - y) :
    StatisticalRL.GenerativeLowerBound.bernoulliKLExpression (x + (1 - x) * μo)
        (y + (1 - y) * μo) ≤ 4 * (x - y) ^ 2 / (1 - γ) := by
  set u := x + (1 - x) * μo
  set v := y + (1 - y) * μo
  have hy1 : y < 1 := by linarith
  have hu0 : 0 < u := by have : 0 < (1 - x) * μo := mul_pos (by linarith) hμ0; linarith
  have hu1 : u < 1 := by
    have : u = 1 - (1 - x) * (1 - μo) := by ring
    rw [this]; have : 0 < (1 - x) * (1 - μo) := mul_pos (by linarith) (by linarith); linarith
  have hv0 : 1 / 2 ≤ v := by have : 0 ≤ (1 - y) * μo := mul_nonneg (by linarith) hμ0.le; linarith
  have hv1 : v < 1 := by
    have : v = 1 - (1 - y) * (1 - μo) := by ring
    rw [this]; have : 0 < (1 - y) * (1 - μo) := mul_pos (by linarith) (by linarith); linarith
  have h1 := StatisticalRL.GenerativeLowerBound.bernoulliKLExpression_le_quadratic u v
    (by linarith) hv1 hu0 hu1
  have huv : u - v = (x - y) * (1 - μo) := by ring
  have h1v : 1 - v = (1 - y) * (1 - μo) := by ring
  have hden : 0 < v * (1 - v) := mul_pos (by linarith) (by linarith)
  have h2 : (u - v) ^ 2 / (v * (1 - v)) = (x - y) ^ 2 * (1 - μo) / (v * (1 - y)) := by
    rw [huv, h1v]
    have : (1 : ℝ) - μo ≠ 0 := by linarith
    have : v ≠ 0 := by linarith
    have : (1 : ℝ) - y ≠ 0 := by linarith
    field_simp
    try ring
  have h3 : (x - y) ^ 2 * (1 - μo) / (v * (1 - y)) ≤ (x - y) ^ 2 / (v * (1 - y)) := by
    apply div_le_div_of_nonneg_right _ (mul_pos (by linarith) (by linarith)).le
    exact mul_le_of_le_one_right (sq_nonneg _) (by linarith)
  have h4 : (x - y) ^ 2 / (v * (1 - y)) ≤ (x - y) ^ 2 / ((1 / 2) * ((1 - γ) / 2)) := by
    have hg' : 0 < 1 - γ := by linarith
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact mul_le_mul hv0 hyγ (by positivity) (by linarith)
  have h5 : (x - y) ^ 2 / ((1 / 2) * ((1 - γ) / 2)) = 4 * (x - y) ^ 2 / (1 - γ) := by
    have : (1 : ℝ) - γ ≠ 0 := by linarith
    field_simp
    try ring
  calc _ ≤ (u - v) ^ 2 / (v * (1 - v)) := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ ≤ _ := h4
    _ = _ := h5

/-- `lem:transition-KL-bound-infinite` with the explicit constant `c₃ = 16 · 336²`. -/
theorem lb_transition_kl (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C)
    (θ θ' : Fin m → Bool) (i : Fin m) (a : Bool) :
    let M := lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ
    let M' := lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ'
    (θ i = θ' i →
      InformationTheory.klDiv (M.transition (some i) a).rowMeasure
        (M'.transition (some i) a).rowMeasure = 0) ∧
    (θ i ≠ θ' i →
      InformationTheory.klDiv (M.transition (some i) a).rowMeasure
        (M'.transition (some i) a).rowMeasure ≤
          ENNReal.ofReal (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2)) := by
  intro M M'
  have hγ0 : 0 < γ := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : M.transition (some i) a = M'.transition (some i) a := by
      simp only [M, M', lbMDP, h]
    rw [this]
    exact InformationTheory.klDiv_self _
  · have hg0 : 0 ≤ lbGap γ ε := by unfold lbGap; exact div_nonneg (by positivity) hγ0.le
    have hg1 : lbGap γ ε ≤ (1 - γ) / 2 := by
      have e : lbGap γ ε = (1 - γ) * (224 * (1 - γ) * ε / γ) := by unfold lbGap; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hεmax h1γ.le
      linarith
    have hgδ : lbGap γ ε ≤ 336 * (1 - γ) ^ 2 * ε := by
      unfold lbGap
      rw [div_le_iff₀ hγ0]
      have : 0 ≤ (1 - γ) ^ 2 * ε := by positivity
      nlinarith
    have hμ0 := lbMu_pos hC hm (some i)
    have hμ1 := lbMu_some_lt_one hC hm i
    have hp0 : 0 ≤ lbP γ ε := by simp only [lbP]; linarith
    have hp1 : lbP γ ε ≤ 1 := by simp only [lbP]; linarith
    have hq0 : 0 ≤ lbQ γ ε := by simp only [lbQ]; linarith
    have hq1 : lbQ γ ε ≤ 1 := by simp only [lbQ]; linarith
    have hpq : lbP γ ε - lbQ γ ε = 2 * lbGap γ ε := by simp only [lbP, lbQ]; ring
    have hbound : 4 * (2 * lbGap γ ε) ^ 2 ≤ 16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 * (1 - γ) := by
      have hsq : lbGap γ ε ^ 2 ≤ (336 * (1 - γ) ^ 2 * ε) ^ 2 := pow_le_pow_left₀ hg0 hgδ 2
      have e1 : 4 * (2 * lbGap γ ε) ^ 2 = 16 * lbGap γ ε ^ 2 := by ring
      have e2 : 16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 * (1 - γ) = 16 * (336 * (1 - γ) ^ 2 * ε) ^ 2 := by
        ring
      rw [e1, e2]
      linarith
    have key : ∀ (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1),
        0 < x → x < 1 → 1 / 2 ≤ y → (1 - γ) / 2 ≤ 1 - y → (x - y) ^ 2 = (2 * lbGap γ ε) ^ 2 →
        InformationTheory.klDiv (lbRow C m hC hm (some i) x hx0 hx1).rowMeasure
          (lbRow C m hC hm (some i) y hy0 hy1).rowMeasure ≤
            ENNReal.ofReal (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2) := by
      intro x y hx0 hx1 hy0 hy1 hxpos hxlt hyhalf hyγ hxy
      have hylt : y < 1 := by linarith
      obtain ⟨hne, heq⟩ := lbRow_klDiv_eq hC hm i x y hx0 hx1 hy0 hylt
      rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity), heq]
      refine (lb_bernoulli_mixed_le hμ0 hμ1 hxpos hxlt hyhalf hγ1 hyγ).trans ?_
      rw [div_le_iff₀ h1γ, hxy]
      exact hbound
    have hProw : ∀ (ϑ : Fin m → Bool), ϑ i = a →
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC ϑ).transition (some i) a =
          lbRow C m hC hm (some i) (lbP γ ε) hp0 hp1 := by
      intro ϑ hϑ
      simp only [lbMDP, hϑ, if_true]
    have hQrow : ∀ (ϑ : Fin m → Bool), ϑ i ≠ a →
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC ϑ).transition (some i) a =
          lbRow C m hC hm (some i) (lbQ γ ε) hq0 hq1 := by
      intro ϑ hϑ
      have : ¬ a = ϑ i := fun h' => hϑ h'.symm
      simp only [lbMDP, this, if_false]
    have hpq_lt : 0 < lbP γ ε := by simp only [lbP]; linarith
    have hq_lt : lbQ γ ε < 1 := by simp only [lbQ]; linarith
    have hp_lt : lbP γ ε < 1 := by simp only [lbP]; linarith
    have hq_pos : 0 < lbQ γ ε := by simp only [lbQ]; linarith
    have hq_half : 1 / 2 ≤ lbQ γ ε := by simp only [lbQ]; linarith
    have hp_half : 1 / 2 ≤ lbP γ ε := by simp only [lbP]; linarith
    have hq_γ : (1 - γ) / 2 ≤ 1 - lbQ γ ε := by simp only [lbQ]; linarith
    have hp_γ : (1 - γ) / 2 ≤ 1 - lbP γ ε := by simp only [lbP]; linarith
    by_cases ha : θ i = a
    · have ha' : θ' i ≠ a := by rw [← ha]; exact fun h' => h h'.symm
      change InformationTheory.klDiv
        ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition (some i) a).rowMeasure
        ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition (some i) a).rowMeasure ≤ _
      rw [hProw θ ha, hQrow θ' ha']
      exact key _ _ _ _ _ _ hpq_lt hp_lt hq_half hq_γ (by rw [hpq])
    · have ha' : θ' i = a := by
        have hb : ∀ x y z : Bool, x ≠ y → x ≠ z → y = z := by decide
        exact hb _ _ _ h ha
      change InformationTheory.klDiv
        ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition (some i) a).rowMeasure
        ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition (some i) a).rowMeasure ≤ _
      rw [hQrow θ ha, hProw θ' ha']
      exact key _ _ _ _ _ _ hq_pos hq_lt hp_half hp_γ
        (by rw [show lbQ γ ε - lbP γ ε = -(lbP γ ε - lbQ γ ε) by ring, hpq]; ring)

end StatisticalRL.OfflineRL.LowerBound
