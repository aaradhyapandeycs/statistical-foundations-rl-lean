import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalBernsteinRandomFamily
import Formalization.Probability.SelfBoundingConcentration

/-!
# Lemma 6.18: Bernstein bounds for one offline transition row

Source: arXiv:2610.41903v1, `chapters/offlineRL.tex`, Lemma 6.18
(`lem:Bernstein-infinite-proof`, lines 3635–3662; proof lines 4339–4405).

Fix a pair `(s,a)` with `N_{s,a} = n > 0`. Conditionally on the visitation counts, `P̂_{s,a}`
is the empirical row of `n` independent draws from `P_{s,a}` (`offlineRL.tex:1126–1128`). The
theorems below hold on any probability space carrying such draws (`draw`, with law
`d.sampleMeasure n`, where `d = P_{s,a}`) and a random vector `V` that is independent of the
empirical row and satisfies `0 ≤ V ≤ 1/(1-γ)`.

The proof is the printed one. The small-count case of (a) is deterministic. The large-count case
applies the empirical Bernstein inequality (Lemma 2.6) at confidence `4δ`. Part (b) applies
Bernstein (Lemma 2.5) at confidence `4δ` to the centered square, then uses the nonnegative case of
`lemma:sqv`, the variance identity and AM-GM. A union bound gives `1 - 8δ`.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineVILCB.BernsteinInfinite

open StatisticalRL StatisticalRL.FiniteDistribution

variable {S : Type*} [Fintype S]

theorem continuous_expectation (q : FiniteDistribution S) :
    Continuous fun c : S → ℝ ↦ q.expectation c := by
  unfold FiniteDistribution.expectation
  exact continuous_finset_sum _ fun s _ ↦ continuous_const.mul (continuous_apply s)

theorem continuous_variance (q : FiniteDistribution S) :
    Continuous fun c : S → ℝ ↦ q.variance c := by
  unfold FiniteDistribution.variance FiniteDistribution.expectation
  exact (continuous_finset_sum _ fun s _ ↦ continuous_const.mul ((continuous_apply s).pow 2)).sub
    ((continuous_finset_sum _ fun s _ ↦ continuous_const.mul (continuous_apply s)).pow 2)

omit [Fintype S] in
/-- A set in `(S → ℝ) × X` with countable discrete `X` is measurable when its sections are. -/
theorem measurableSet_of_sections {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {E : Set ((S → ℝ) × X)}
    (h : ∀ x, MeasurableSet {c | (c, x) ∈ E}) : MeasurableSet E := by
  have heq : E = ⋃ x : X, {c | (c, x) ∈ E} ×ˢ {x} := by
    ext ⟨c, x⟩
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun x ↦ (h x).prod (measurableSet_singleton x)

omit [Fintype S] in
/-- Union bound for two events of probability greater than `1 - 4δ`. -/
theorem inter_gt_of_gt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B : Set Ω} {δ : ℝ} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hA : 1 - 4 * δ < μ.real A) (hB : 1 - 4 * δ < μ.real B) :
    1 - 8 * δ < μ.real (A ∩ B) := by
  have hAc := measureReal_compl (μ := μ) hAm
  have hBc := measureReal_compl (μ := μ) hBm
  have hABc := measureReal_compl (μ := μ) (hAm.inter hBm)
  rw [probReal_univ] at hAc hBc hABc
  have hu : μ.real (A ∩ B)ᶜ ≤ μ.real Aᶜ + μ.real Bᶜ := by
    rw [Set.compl_inter]
    exact measureReal_union_le _ _
  linarith

/-- The printed inequality `eq:bonus-Bernstein-infinite-proof` for a vector `c` and sample `x`. -/
def DeviationBound (d : FiniteDistribution S) (γ δ : ℝ) (n : ℕ) (hn : 0 < n) (c : S → ℝ)
    (x : Fin n → S) : Prop :=
  |(empiricalRow n hn x).expectation c - d.expectation c| ≤
    Real.sqrt (4 * (empiricalRow n hn x).variance c * Real.log (1 / δ) / n) +
      5 * Real.log (1 / δ) / ((1 - γ) * n)

/-- The printed inequality `eq:empirical-var-infinite-proof` for a vector `c` and sample `x`. -/
def VarianceBound (d : FiniteDistribution S) (γ δ : ℝ) (n : ℕ) (hn : 0 < n) (c : S → ℝ)
    (x : Fin n → S) : Prop :=
  (empiricalRow n hn x).variance c ≤
    2 * d.variance c + 5 * Real.log (1 / δ) / (3 * (1 - γ) ^ 2 * n)

/-- Scalar part of (b): Bernstein on the centered square, `lemma:sqv`, and AM-GM. -/
theorem variance_scalar {vhat ehat e v vw r L n C : ℝ} (hn : 0 < n) (hL : 0 ≤ L)
    (hv : 0 ≤ v) (hvhat : vhat ≤ ehat) (he : e = v) (hr : r ≤ C ^ 2)
    (hvw : vw ≤ C ^ 2 * v)
    (hdev : |ehat - e| ≤ Real.sqrt (2 * L * vw / n) + 2 * r * L / (3 * n)) :
    vhat ≤ 2 * v + 5 * L * C ^ 2 / (3 * n) := by
  have hy0 : 0 ≤ L * C ^ 2 / n := div_nonneg (mul_nonneg hL (sq_nonneg C)) hn.le
  have e1 : 2 * L * (C ^ 2 * v) / n = 2 * v * (L * C ^ 2 / n) := by ring
  have e2 : 2 * C ^ 2 * L / (3 * n) = 2 / 3 * (L * C ^ 2 / n) := by ring
  have e3 : 5 * L * C ^ 2 / (3 * n) = 5 / 3 * (L * C ^ 2 / n) := by ring
  have hsq1 : Real.sqrt (2 * L * vw / n) ≤ Real.sqrt (2 * L * (C ^ 2 * v) / n) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvw (by linarith)) hn.le)
  have hsq2 : Real.sqrt (2 * L * (C ^ 2 * v) / n) ≤ v + (L * C ^ 2 / n) / 2 := by
    rw [e1]
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [sq_nonneg (v - (L * C ^ 2 / n) / 2)]
  have hr' : 2 * r * L / (3 * n) ≤ 2 * C ^ 2 * L / (3 * n) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr (by norm_num)) hL) (by linarith)
  have habs := le_abs_self (ehat - e)
  rw [e2] at hr'
  rw [e3]
  linarith

/-- Scalar part of (a), large-count case: `n - 1 ≥ n/2` turns the empirical Bernstein radius
into the printed one. -/
theorem deviation_scalar {dev vhat L n C nrm : ℝ} (hn : 2 ≤ n) (hL : 0 ≤ L)
    (hvhat : 0 ≤ vhat) (hC : 0 ≤ C) (hnrm : nrm ≤ C)
    (h : dev ≤ Real.sqrt (2 * vhat * L / (n - 1)) + 7 * nrm * L / (3 * (n - 1))) :
    dev ≤ Real.sqrt (4 * vhat * L / n) + 5 * L * C / n := by
  have hn1 : 0 < n - 1 := by linarith
  have hn0 : 0 < n := by linarith
  have hvl : 0 ≤ vhat * L := mul_nonneg hvhat hL
  have hs : Real.sqrt (2 * vhat * L / (n - 1)) ≤ Real.sqrt (4 * vhat * L / n) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hn1 hn0]
    nlinarith
  have hl : 7 * nrm * L / (3 * (n - 1)) ≤ 5 * L * C / n := by
    rw [div_le_div_iff₀ (by linarith) hn0]
    have h1 : nrm * L ≤ C * L := mul_le_mul_of_nonneg_right hnrm hL
    have hCL : 0 ≤ C * L := mul_nonneg hC hL
    nlinarith
  linarith

section Events

local instance bernsteinInfiniteStateMeasurable : MeasurableSpace S := ⊤
local instance bernsteinInfiniteRowMeasurable : MeasurableSpace (FiniteDistribution S) := ⊤

theorem measurableSet_deviationBound (d : FiniteDistribution S) (γ δ : ℝ) (n : ℕ)
    (hn : 0 < n) :
    MeasurableSet {p : (S → ℝ) × (Fin n → S) | DeviationBound d γ δ n hn p.1 p.2} := by
  apply measurableSet_of_sections
  intro x
  have h : MeasurableSet {c : S → ℝ |
      |(empiricalRow n hn x).expectation c - d.expectation c| ≤
        Real.sqrt (4 * (empiricalRow n hn x).variance c * Real.log (1 / δ) / n) +
          5 * Real.log (1 / δ) / ((1 - γ) * n)} :=
    measurableSet_le
      (((continuous_expectation _).sub (continuous_expectation d)).abs.measurable)
      (((((continuous_const.mul (continuous_variance _)).mul continuous_const).div_const
        _).sqrt.add continuous_const).measurable)
  exact h

theorem measurableSet_varianceBound (d : FiniteDistribution S) (γ δ : ℝ) (n : ℕ)
    (hn : 0 < n) :
    MeasurableSet {p : (S → ℝ) × (Fin n → S) | VarianceBound d γ δ n hn p.1 p.2} := by
  apply measurableSet_of_sections
  intro x
  have h : MeasurableSet {c : S → ℝ | (empiricalRow n hn x).variance c ≤
      2 * d.variance c + 5 * Real.log (1 / δ) / (3 * (1 - γ) ^ 2 * n)} :=
    measurableSet_le (continuous_variance _).measurable
      ((continuous_const.mul (continuous_variance d)).add continuous_const).measurable
  exact h

variable {Ω : Type*} [MeasurableSpace Ω]

omit [Fintype S] in
/-- An event defined by a jointly measurable predicate of `(V, draw)` is measurable. -/
theorem measurableSet_event {n : ℕ} {V : Ω → S → ℝ} (hV : Measurable V) {draw : Ω → Fin n → S}
    (hdraw : Measurable draw) {P : (S → ℝ) → (Fin n → S) → Prop}
    (hP : MeasurableSet {p : (S → ℝ) × (Fin n → S) | P p.1 p.2}) :
    MeasurableSet {ω | P (V ω) (draw ω)} :=
  hP.preimage (hV.prodMk hdraw)

/-- Part (b) at confidence `4δ` (`offlineRL.tex:4375–4405`). -/
theorem varianceBound_event_gt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution S) (γ : ℝ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ < 1 / 8)
    (n : ℕ) (hn : 0 < n) (draw : Ω → Fin n → S) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure n)
    (V : Ω → S → ℝ) (hV : Measurable V)
    (hindep : IndepFun V (fun ω ↦ empiricalRow n hn (draw ω)) μ)
    (hrange : ∀ ω s, 0 ≤ V ω s ∧ V ω s ≤ 1 / (1 - γ)) :
    1 - 4 * δ < μ.real {ω | VarianceBound d γ δ n hn (V ω) (draw ω)} := by
  classical
  have hγ' : 0 < 1 - γ := sub_pos.mpr hγ1
  have hδ4 : 0 < 4 * δ := by positivity
  have hδ41 : 4 * δ < 1 := by linarith
  let w : (S → ℝ) → (S → ℝ) := fun c s ↦ (c s - d.expectation c) ^ 2
  have hwc : Continuous w :=
    continuous_pi fun s ↦ ((continuous_apply s).sub (continuous_expectation d)).pow 2
  let family : (S → ℝ) → Finset (S → ℝ) := fun c ↦ {w c}
  have hVmeas : MeasurableSet {c : S → ℝ | ∀ W ∈ family c, ∀ s, 0 ≤ W s} := by
    have : {c : S → ℝ | ∀ W ∈ family c, ∀ s, 0 ≤ W s} = Set.univ := by
      ext c
      simp [family, w, sq_nonneg]
    rw [this]
    exact MeasurableSet.univ
  have hbad : ∀ row ∈ empiricalRows n hn,
      MeasurableSet {c | bernsteinFamilyBadAt d n (4 * δ) (family c) row} := by
    intro row _
    have hset : {c | bernsteinFamilyBadAt d n (4 * δ) (family c) row} =
        {c | bernsteinRadius d n 1 (4 * δ) (w c) <
          |row.expectation (w c) - d.expectation (w c)|} := by
      ext c
      simp [bernsteinFamilyBadAt, family]
    rw [hset]
    apply measurableSet_lt
    · unfold bernsteinRadius
      exact ((((continuous_const.mul ((continuous_variance d).comp' hwc)).div_const _).sqrt).add
        (((continuous_const.mul (continuous_norm.comp' hwc)).mul continuous_const).div_const
          _)).measurable
    · exact ((((continuous_expectation row).comp' hwc).sub
        ((continuous_expectation d).comp' hwc)).abs).measurable
  have hprov := d.randomFamily_bernstein_success_gt μ n hn (4 * δ) hδ4 hδ41 draw hdraw hlaw
    V hV family hindep (Filter.Eventually.of_forall fun ω W hW s ↦ by
      simp only [family, Finset.mem_singleton] at hW
      subst hW
      exact sq_nonneg _) hVmeas hbad
  refine hprov.trans_le (measureReal_mono ?_ (measure_ne_top μ _))
  intro ω hω
  have h1 := hω (w (V ω)) (Finset.mem_singleton_self _)
  have hcard : (family (V ω)).card = 1 := Finset.card_singleton _
  rw [hcard] at h1
  unfold bernsteinRadius at h1
  have hlog : Real.log (4 * ((1 : ℕ) : ℝ) / (4 * δ)) = Real.log (1 / δ) := by
    congr 1
    rw [Nat.cast_one]
    field_simp
  rw [hlog] at h1
  have hL : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  set c := V ω
  have hc : ∀ s, c s ∈ Set.Icc 0 (1 / (1 - γ)) := fun s ↦ ⟨(hrange ω s).1, (hrange ω s).2⟩
  have h2 : d.variance (w c) ≤ (1 / (1 - γ)) ^ 2 * d.variance c :=
    d.centeredSquare_variance_le c _ hc
  have h3 : ‖w c‖ ≤ (1 / (1 - γ)) ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2 fun s ↦ ?_
    have hs := d.centeredSquare_mem_Icc c _ hc s
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have h4 : (empiricalRow n hn (draw ω)).variance c =
      (empiricalRow n hn (draw ω)).expectation (w c) -
        ((empiricalRow n hn (draw ω)).expectation c - d.expectation c) ^ 2 :=
    d.empiricalVariance_eq_centeredSquare_sub n hn c (draw ω)
  have h5 : d.expectation (w c) = d.variance c :=
    (d.variance_eq_expectation_centered_sq c).symm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqd := sq_nonneg ((empiricalRow n hn (draw ω)).expectation c - d.expectation c)
  have hle : (empiricalRow n hn (draw ω)).variance c ≤
      (empiricalRow n hn (draw ω)).expectation (w c) := by
    rw [h4]
    linarith
  have hmain := variance_scalar hn' hL (d.variance_nonneg c) hle h5 h3 h2 h1
  have heq : 5 * Real.log (1 / δ) * (1 / (1 - γ)) ^ 2 / (3 * n) =
      5 * Real.log (1 / δ) / (3 * (1 - γ) ^ 2 * n) := by
    field_simp
  show (empiricalRow n hn (draw ω)).variance c ≤ _
  rw [← heq]
  exact hmain

/-- Part (a) at confidence `4δ` (`offlineRL.tex:4345–4371`). -/
theorem deviationBound_event_gt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution S) (γ : ℝ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ < 1 / 8)
    (n : ℕ) (hn : 0 < n) (draw : Ω → Fin n → S) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure n)
    (V : Ω → S → ℝ) (hV : Measurable V)
    (hindep : IndepFun V (fun ω ↦ empiricalRow n hn (draw ω)) μ)
    (hrange : ∀ ω s, 0 ≤ V ω s ∧ V ω s ≤ 1 / (1 - γ)) :
    1 - 4 * δ < μ.real {ω | DeviationBound d γ δ n hn (V ω) (draw ω)} := by
  classical
  have hγ' : 0 < 1 - γ := sub_pos.mpr hγ1
  have hC : 0 < 1 / (1 - γ) := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL7 : 7 / 8 < Real.log (1 / δ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by positivity : (0 : ℝ) < 1 / δ)
    rw [one_div, inv_inv] at h
    rw [one_div]
    linarith
  have hL : 0 ≤ Real.log (1 / δ) := by linarith
  have hnorm : ∀ ω, ‖V ω‖ ≤ 1 / (1 - γ) := fun ω ↦
    (pi_norm_le_iff_of_nonneg hC.le).2 fun s ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hrange ω s).1]
      exact (hrange ω s).2
  have hconv : 5 * Real.log (1 / δ) * (1 / (1 - γ)) / n =
      5 * Real.log (1 / δ) / ((1 - γ) * n) := by
    field_simp
  by_cases hsmall : (n : ℝ) < 5 * Real.log (1 / δ)
  · -- deterministic small-count case
    have huniv : {ω | DeviationBound d γ δ n hn (V ω) (draw ω)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have h0 := d.empiricalRow_abs_deviation_le_norm n hn (V ω) (fun s ↦ (hrange ω s).1)
        (draw ω)
      have hr : 1 / (1 - γ) ≤ 5 * Real.log (1 / δ) * (1 / (1 - γ)) / n := by
        rw [le_div_iff₀ hn']
        nlinarith
      rw [hconv] at hr
      have hsq := Real.sqrt_nonneg
        (4 * (empiricalRow n hn (draw ω)).variance (V ω) * Real.log (1 / δ) / n)
      unfold DeviationBound
      linarith [hnorm ω]
    rw [huniv, probReal_univ]
    linarith
  · push_neg at hsmall
    have hn2 : (2 : ℝ) ≤ n := by linarith
    have hn2' : 2 ≤ n := by exact_mod_cast hn2
    have hδ4 : 0 < 4 * δ := by positivity
    have hδ41 : 4 * δ < 1 := by linarith
    let family : (S → ℝ) → Finset (S → ℝ) := fun c ↦ {c}
    have hVmeas : MeasurableSet {c : S → ℝ | ∀ W ∈ family c, ∀ s, 0 ≤ W s} := by
      have : {c : S → ℝ | ∀ W ∈ family c, ∀ s, 0 ≤ W s} = {c | ∀ s, 0 ≤ c s} := by
        ext c
        simp [family]
      rw [this, Set.setOf_forall]
      exact MeasurableSet.iInter fun s ↦ measurableSet_le measurable_const (measurable_pi_apply s)
    have hbad : ∀ row ∈ empiricalRows n hn,
        MeasurableSet {c | empiricalBernsteinFamilyBadAt d n (4 * δ) (family c) row} := by
      intro row _
      have hset : {c | empiricalBernsteinFamilyBadAt d n (4 * δ) (family c) row} =
          {c : S → ℝ | empiricalBernsteinFamilyRadius row n 1 (4 * δ) c <
            |row.expectation c - d.expectation c|} := by
        ext c
        simp [empiricalBernsteinFamilyBadAt, family]
      rw [hset]
      exact empiricalBernsteinFamily_vector_violation_measurable d row n 1 (4 * δ)
    have hprov := d.randomFamily_empiricalBernstein_success_gt μ n hn hn2' (4 * δ) hδ4 hδ41
      draw hdraw hlaw V hV family hindep (Filter.Eventually.of_forall fun ω W hW s ↦ by
        simp only [family, Finset.mem_singleton] at hW
        subst hW
        exact (hrange ω s).1) hVmeas hbad
    refine hprov.trans_le (measureReal_mono ?_ (measure_ne_top μ _))
    intro ω hω
    have h1 := hω (V ω) (Finset.mem_singleton_self _)
    have hcard : (family (V ω)).card = 1 := Finset.card_singleton _
    rw [hcard] at h1
    unfold empiricalBernsteinFamilyRadius at h1
    have hlog : Real.log (4 * ((1 : ℕ) : ℝ) / (4 * δ)) = Real.log (1 / δ) := by
      congr 1
      rw [Nat.cast_one]
      field_simp
    rw [hlog] at h1
    have hmain := deviation_scalar hn2 hL ((empiricalRow n hn (draw ω)).variance_nonneg _)
      hC.le (hnorm ω) h1
    have hconv' : 5 * Real.log (1 / δ) * (1 / (1 - γ)) / n =
        5 * Real.log (1 / δ) / ((1 - γ) * n) := hconv
    show DeviationBound d γ δ n hn (V ω) (draw ω)
    unfold DeviationBound
    rw [← hconv']
    exact hmain

/-- **Lemma 6.18** (`lem:Bernstein-infinite-proof`, `offlineRL.tex:3635–3662`), library form
with discrete independence. Both printed inequalities hold with probability greater than
`1 - 8δ`. -/
theorem bernsteinInfinite_fixedRow (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution S) (γ : ℝ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ < 1 / 8)
    (n : ℕ) (hn : 0 < n) (draw : Ω → Fin n → S) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure n)
    (V : Ω → S → ℝ) (hV : Measurable V)
    (hindep : IndepFun V (fun ω ↦ empiricalRow n hn (draw ω)) μ)
    (hrange : ∀ ω s, 0 ≤ V ω s ∧ V ω s ≤ 1 / (1 - γ)) :
    1 - 8 * δ < μ.real {ω |
      |(empiricalRow n hn (draw ω)).expectation (V ω) - d.expectation (V ω)| ≤
          Real.sqrt (4 * (empiricalRow n hn (draw ω)).variance (V ω) * Real.log (1 / δ) / n) +
            5 * Real.log (1 / δ) / ((1 - γ) * n) ∧
        (empiricalRow n hn (draw ω)).variance (V ω) ≤
          2 * d.variance (V ω) + 5 * Real.log (1 / δ) / (3 * (1 - γ) ^ 2 * n)} := by
  have hA := deviationBound_event_gt μ d γ hγ1 δ hδ hδ8 n hn draw hdraw hlaw V hV hindep hrange
  have hB := varianceBound_event_gt μ d γ hγ1 δ hδ hδ8 n hn draw hdraw hlaw V hV hindep hrange
  have hAm : MeasurableSet {ω | DeviationBound d γ δ n hn (V ω) (draw ω)} :=
    measurableSet_event hV hdraw (measurableSet_deviationBound d γ δ n hn)
  have hBm : MeasurableSet {ω | VarianceBound d γ δ n hn (V ω) (draw ω)} :=
    measurableSet_event hV hdraw (measurableSet_varianceBound d γ δ n hn)
  have h := inter_gt_of_gt μ hAm hBm hA hB
  have heq : {ω | DeviationBound d γ δ n hn (V ω) (draw ω)} ∩
      {ω | VarianceBound d γ δ n hn (V ω) (draw ω)} = {ω |
      |(empiricalRow n hn (draw ω)).expectation (V ω) - d.expectation (V ω)| ≤
          Real.sqrt (4 * (empiricalRow n hn (draw ω)).variance (V ω) * Real.log (1 / δ) / n) +
            5 * Real.log (1 / δ) / ((1 - γ) * n) ∧
        (empiricalRow n hn (draw ω)).variance (V ω) ≤
          2 * d.variance (V ω) + 5 * Real.log (1 / δ) / (3 * (1 - γ) ^ 2 * n)} :=
    by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, DeviationBound, VarianceBound]
  rw [heq] at h
  exact h

/-- Lemma 6.18 with independence stated for the coordinate σ-algebra `rowVectorSpace` on rows
(the form used by the Lemma 2.5 entry); this hypothesis is weaker than discrete independence and
is equivalent to it for these finite-range rows. -/
theorem bernsteinInfinite_fixedRow_rowVector (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution S) (γ : ℝ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ < 1 / 8)
    (n : ℕ) (hn : 0 < n) (draw : Ω → Fin n → S) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure n)
    (V : Ω → S → ℝ) (hV : Measurable V)
    (hindep : letI : MeasurableSpace (FiniteDistribution S) := rowVectorSpace
      IndepFun V (fun ω ↦ empiricalRow n hn (draw ω)) μ)
    (hrange : ∀ ω s, 0 ≤ V ω s ∧ V ω s ≤ 1 / (1 - γ)) :
    1 - 8 * δ < μ.real {ω |
      |(empiricalRow n hn (draw ω)).expectation (V ω) - d.expectation (V ω)| ≤
          Real.sqrt (4 * (empiricalRow n hn (draw ω)).variance (V ω) * Real.log (1 / δ) / n) +
            5 * Real.log (1 / δ) / ((1 - γ) * n) ∧
        (empiricalRow n hn (draw ω)).variance (V ω) ≤
          2 * d.variance (V ω) + 5 * Real.log (1 / δ) / (3 * (1 - γ) ^ 2 * n)} := by
  have hdiscrete : IndepFun V (fun ω ↦ empiricalRow n hn (draw ω)) μ := by
    letI : MeasurableSpace (FiniteDistribution S) := rowVectorSpace
    letI : MeasurableSingletonClass (FiniteDistribution S) := rowVectorSpace_singletons
    exact indepFun_finiteRange_to_discrete μ V
      (fun ω ↦ empiricalRow n hn (draw ω)) (empiricalRows n hn)
      (fun ω ↦ empiricalRow_mem_empiricalRows n hn (draw ω)) hindep
  exact bernsteinInfinite_fixedRow μ d γ hγ1 δ hδ hδ8 n hn draw hdraw hlaw V hV hdiscrete hrange

end Events

end StatisticalRL.OfflineVILCB.BernsteinInfinite
