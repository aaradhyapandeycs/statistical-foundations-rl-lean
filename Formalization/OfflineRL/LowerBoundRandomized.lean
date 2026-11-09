import Formalization.OfflineRL.LowerBoundMinimax

/-!
# Offline minimax lower bound for externally randomized estimators

`thm:infinite-lwoer-bound`, `chapters/offlineRL.tex:2367–2402`, proof `:2432–2927`.

The source infimum in `eq:infinite-lower-bound-theorem` ranges over all policy estimators. The
library export `offline_minimax_lower_bound` covers deterministic maps from datasets to policies.
This file covers estimators that also use an independent random seed `ω ~ μ` on an arbitrary
probability space `(Ω, μ)`: the joint law of `(ω, D)` is `μ ⊗ P_θ`.

Route (no new Fano argument):

* `lb_fano_core_sum`: the averaged form of Step 2, `|Θ|/4 ≤ ∑_θ P_θ(ψ ≠ θ)` for every
  deterministic decoder `ψ`. It applies the same per-test Fano inequality
  (`PrelimFano.fano_test_average_error_lower`) and the same threshold arithmetic as
  `lb_fano_core`, stopping before the final choice of `θ`.
* `lb_minimax_core_sum`: the averaged form of Steps 1, 2 and 4 for a deterministic estimator.
* `exists_prod_measureReal_ge_of_sum_sections`: if for every seed `ω` the sections satisfy
  `c |I| ≤ ∑_i P_i(E_i^ω)`, then Tonelli and a pigeonhole on the finite index give one `i` with
  `c ≤ (μ ⊗ P_i)(E_i)`.

Measurability: no measurability of `π̂` in the seed is assumed. The conclusion is about
`(μ ⊗ P_θ)` of the failure set. When that set is measurable (for instance `Ω` countable, or `π̂`
measurable in the seed and the policy value measurable in the policy) this is its probability;
otherwise it is the outer probability (Mathlib measures are outer measures on all sets). An
inner-probability version is false in general. The proof replaces each failure set by its
measurable hull (`exists_prod_measureReal_ge_of_sum_sections'`).

Since datasets range over a finite set, every estimator given as a Markov kernel from datasets to
policies is of the seeded form (`Ω = ∏_D Policy`, `μ = ⊗_D κ(D)`, `π̂(ω, D) = ω D`).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.OfflineRL.LowerBound

open StatisticalRL.OfflineRL.JointRow StatisticalRL.DiscountedMDP

section Randomization

/-- A set in `Ω × D` over a countable discrete `D` is measurable once every `ω`-section at a
fixed `d` is measurable. -/
theorem measurableSet_of_measurableSet_sections {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D] {E : Set (Ω × D)}
    (h : ∀ d, MeasurableSet {ω | (ω, d) ∈ E}) : MeasurableSet E := by
  have hE : E = ⋃ d, {ω | (ω, d) ∈ E} ×ˢ ({d} : Set D) := by
    ext ⟨ω, d⟩
    simp
  rw [hE]
  exact MeasurableSet.iUnion fun d => (h d).prod (measurableSet_singleton d)

/-- Averaging over an independent seed: if for every seed `ω` the per-instance section
probabilities sum to at least `c |I|`, then some instance has joint probability at least `c`. -/
theorem exists_prod_measureReal_ge_of_sum_sections {I Ω D : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] [MeasurableSpace D] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : I → Measure D) [∀ i, IsProbabilityMeasure (P i)] (E : I → Set (Ω × D))
    (hE : ∀ i, MeasurableSet (E i)) (c : ℝ)
    (hsum : ∀ ω, c * Fintype.card I ≤ ∑ i, (P i).real (Prod.mk ω ⁻¹' E i)) :
    ∃ i, c ≤ (μ.prod (P i)).real (E i) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ i, (μ.prod (P i)).real (E i) < c * Fintype.card I := by
    calc ∑ i, (μ.prod (P i)).real (E i) < ∑ _i : I, c :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hcon i
      _ = c * Fintype.card I := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  have hpt : ∀ ω, ENNReal.ofReal (c * Fintype.card I) ≤ ∑ i, P i (Prod.mk ω ⁻¹' E i) := by
    intro ω
    have h := ENNReal.ofReal_le_ofReal (hsum ω)
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)] at h
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using h
  have hint : ENNReal.ofReal (c * Fintype.card I) ≤ ∑ i, μ.prod (P i) (E i) := by
    calc ENNReal.ofReal (c * Fintype.card I)
        = ∫⁻ _ω, ENNReal.ofReal (c * Fintype.card I) ∂μ := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ ω, ∑ i, P i (Prod.mk ω ⁻¹' E i) ∂μ := lintegral_mono hpt
      _ = ∑ i, ∫⁻ ω, P i (Prod.mk ω ⁻¹' E i) ∂μ :=
          lintegral_finset_sum _ fun i _ => measurable_measure_prodMk_left (hE i)
      _ = ∑ i, μ.prod (P i) (E i) :=
          Finset.sum_congr rfl fun i _ => (Measure.prod_apply (hE i)).symm
  have hfin : ∑ i, μ.prod (P i) (E i) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _ => measure_ne_top _ _
  have hreal : c * Fintype.card I ≤ ∑ i, (μ.prod (P i)).real (E i) := by
    have h := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hint
    rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)] at h
    simpa only [measureReal_def] using h
  linarith

/-- Averaging over an independent seed without measurability of the events: the conclusion is
about the (outer) measure `μ ⊗ P_i`, which is the probability whenever `E i` is measurable. -/
theorem exists_prod_measureReal_ge_of_sum_sections' {I Ω D : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] [MeasurableSpace D] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : I → Measure D) [∀ i, IsProbabilityMeasure (P i)] (E : I → Set (Ω × D)) (c : ℝ)
    (hsum : ∀ ω, c * Fintype.card I ≤ ∑ i, (P i).real (Prod.mk ω ⁻¹' E i)) :
    ∃ i, c ≤ (μ.prod (P i)).real (E i) := by
  obtain ⟨i, hi⟩ := exists_prod_measureReal_ge_of_sum_sections μ P
    (fun i => toMeasurable (μ.prod (P i)) (E i)) (fun i => measurableSet_toMeasurable _ _) c
    (fun ω => (hsum ω).trans (Finset.sum_le_sum fun i _ =>
      measureReal_mono (Set.preimage_mono (subset_toMeasurable _ _)) (measure_ne_top _ _)))
  refine ⟨i, ?_⟩
  rwa [measureReal_def, measure_toMeasurable, ← measureReal_def] at hi

end Randomization

local instance lbRandStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

local instance (priority := high) lbRandTripleMeasurable (m : ℕ) :
    MeasurableSpace ((Option (Fin m) × Bool) × Option (Fin m)) := ⊤

local instance (priority := high) lbRandTripleSingleton (m : ℕ) :
    MeasurableSingletonClass ((Option (Fin m) × Bool) × Option (Fin m)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

section FanoAverage

variable (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
  (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C)

/-- Step 2 in averaged form: under the dataset KL budget of `lb_fano_core`, every decoder has
summed error `∑_{θ ∈ Θ} P_θ(ψ ≠ θ) ≥ |Θ|/4`. Same Fano inequality and arithmetic as
`lb_fano_core`, without the final choice of `θ`. -/
theorem lb_fano_core_sum (Θ : Finset (Fin m → Bool)) (hK : (4 : ℝ) ≤ Θ.card) (N : ℕ)
    (hN : (N : ℝ) * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / C) ≤ Real.log Θ.card / 4)
    (ψ : (Fin N → (Option (Fin m) × Bool) × Option (Fin m)) → Θ) :
    (Θ.card : ℝ) / 4 ≤ ∑ θ : Θ,
      ((jointRow (lbBehavior C m hC hm)
          (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).transition).sampleMeasure N).real
        {D | ψ D ≠ θ} := by
  classical
  have hC0 : 0 < C := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  set B : ℝ := (N : ℝ) * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / C) with hBdef
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg N)
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h1γ.le 3)) (sq_nonneg ε))
      hC0.le)
  have hK4 : 4 ≤ Θ.card := by exact_mod_cast hK
  set M := Θ.card - 1 with hMdef
  have hKM : Fintype.card Θ = M + 1 := by rw [Fintype.card_coe]; omega
  have hM : 2 ≤ M := by omega
  have hMR : ((M : ℝ) + 1) = Θ.card := by
    have : Θ.card = M + 1 := by omega
    rw [this]; push_cast; ring
  let e : Fin (M + 1) ≃ Θ := (Fintype.equivFinOfCardEq hKM).symm
  let P : Fin (M + 1) → Measure (Fin N → (Option (Fin m) × Bool) × Option (Fin m)) := fun j =>
    (jointRow (lbBehavior C m hC hm)
      (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC (e j).1).transition).sampleMeasure N
  haveI hP : ∀ j, IsProbabilityMeasure (P j) := fun j =>
    FiniteDistribution.sampleMeasure_isProbabilityMeasure _ N
  have hKL := fun j => lb_dataset_klDiv_le m hm γ ε C hγ hγ1 hε hεmax hC (e j).1 (e 0).1 N
  have hfin : ∀ j, InformationTheory.klDiv (P j) (P 0) ≠ ∞ := fun j => (hKL j).1
  let ψ' : PrelimFano.MeasurableTest (Ω := Fin N → (Option (Fin m) × Bool) × Option (Fin m))
      (I := Fin (M + 1)) := ⟨fun D => e.symm (ψ D), measurable_of_countable _⟩
  have hF := PrelimFano.fano_test_average_error_lower M hM P hfin ψ'
  rw [PrelimFano.averageTestError_fin_eq M P ψ'] at hF
  have hKLle : ∀ j, (InformationTheory.klDiv (P j) (P 0)).toReal ≤ B := fun j =>
    ENNReal.toReal_le_of_le_ofReal hB0 (hKL j).2
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hsumKL : (∑ j, (InformationTheory.klDiv (P j) (P 0)).toReal) / ((M : ℝ) + 1) ≤ B := by
    rw [div_le_iff₀ hpos]
    calc ∑ j, (InformationTheory.klDiv (P j) (P 0)).toReal ≤ ∑ _j : Fin (M + 1), B :=
          Finset.sum_le_sum fun j _ => hKLle j
      _ = B * ((M : ℝ) + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  set L := Real.log ((M : ℝ) + 1) with hLdef
  have hL : Real.log Θ.card = L := by rw [hLdef, hMR]
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogle : Real.log (M : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by linarith)
  have hlog4 : 2 * Real.log 2 ≤ L := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [← h4]
    exact Real.log_le_log (by norm_num) (by rw [hMR]; exact hK)
  have hN' : B ≤ L / 4 := by rw [← hL]; exact hN
  have hL0 : 0 < L := lt_of_lt_of_le hlogM hlogle
  have hquarter := GenerativeLowerBound.fano_large_cardinality_quarter ((M : ℝ) + 1) B
    (by rw [hMR]; exact hK) hN'
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnum : 0 ≤ L - Real.log 2 -
      (∑ j, (InformationTheory.klDiv (P j) (P 0)).toReal) / ((M : ℝ) + 1) := by linarith
  have hstep1 := div_le_div_of_nonneg_left hnum hlogM hlogle
  have hstep2 : (L - Real.log 2 - B) / L ≤
      (L - Real.log 2 - (∑ j, (InformationTheory.klDiv (P j) (P 0)).toReal) / ((M : ℝ) + 1)) / L :=
    div_le_div_of_nonneg_right (by linarith) hL0.le
  have hstep3 : (L - Real.log 2 - B) / L = 1 - (B + Real.log 2) / L := by
    rw [show (L - Real.log 2 - B) / L = L / L - (B + Real.log 2) / L by ring, div_self hL0.ne']
  have hlow : (1 : ℝ) / 4 ≤
      1 / ((M : ℝ) + 1) * ∑ j : Fin (M + 1), (P j).real {ω | ψ'.1 ω ≠ j} := by
    linarith
  have hset : ∀ j, {ω | ψ'.1 ω ≠ j} = {D | ψ D ≠ e j} := by
    intro j
    ext D
    exact not_congr e.symm_apply_eq
  have hreindex : ∑ j : Fin (M + 1), (P j).real {ω | ψ'.1 ω ≠ j} = ∑ θ : Θ,
      ((jointRow (lbBehavior C m hC hm)
          (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).transition).sampleMeasure N).real
        {D | ψ D ≠ θ} := by
    simp_rw [hset]
    exact e.sum_comp (fun θ : Θ =>
      ((jointRow (lbBehavior C m hC hm)
          (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).transition).sampleMeasure N).real
        {D | ψ D ≠ θ})
  rw [hreindex] at hlow
  have h2 := mul_le_mul_of_nonneg_left hlow hpos.le
  rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] at h2
  rw [← hMR]
  linarith

/-- Steps 1, 2 and 4 in averaged form for a deterministic estimator: under the hypotheses of
`lb_minimax_core`, the failure probabilities sum to at least `|Θ|/4` over the packing. -/
theorem lb_minimax_core_sum (hm12 : 12 ≤ m) (hεpos : 0 < ε) (Θ : Finset (Fin m → Bool))
    (hcard : Real.exp ((m : ℝ) / 8) ≤ Θ.card)
    (hsep : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, θ ≠ θ' → (m : ℝ) / 8 ≤ hammingDist θ θ') (N : ℕ)
    (hN : (N : ℝ) * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / C) ≤ (m : ℝ) / 32)
    (πhat : (Fin N → (Option (Fin m) × Bool) × Option (Fin m)) →
      StationaryPolicy (Option (Fin m)) Bool) :
    (Θ.card : ℝ) / 4 ≤ ∑ θ : Θ,
      ((jointRow (lbBehavior C m hC hm)
          (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).transition).sampleMeasure N).real
        {D | ε < ∑ s, (lbTest m hm).prob s *
          ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).trajectoryExpectedValue
              (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).optimalGreedyPolicy s -
            (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).trajectoryExpectedValue (πhat D) s)} := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm12R : (12 : ℝ) ≤ m := by exact_mod_cast hm12
  have hexp32 : (4 : ℝ) ≤ Real.exp (3 / 2) := by
    have he := Real.exp_one_gt_d9
    have h3 : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h16 : (4 : ℝ) ^ 2 ≤ Real.exp (3 / 2) ^ 2 := by
      rw [h3]
      have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
      nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num)).mp h16
  have hK : (4 : ℝ) ≤ Θ.card :=
    hexp32.trans ((Real.exp_le_exp.mpr (by linarith)).trans hcard)
  have hlogK : (m : ℝ) / 8 ≤ Real.log Θ.card := by
    rw [← Real.log_exp ((m : ℝ) / 8)]
    exact Real.log_le_log (Real.exp_pos _) hcard
  have hN' : (N : ℝ) * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / C) ≤ Real.log Θ.card / 4 := by
    linarith
  have hΘne : Θ.Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast (by linarith : (0 : ℝ) < Θ.card))
  have hθ := lb_fano_core_sum m hm γ ε C hγ hγ1 hε hεmax hC Θ hK N hN'
    (fun D => lbDecode Θ hΘne (πhat D))
  refine hθ.trans (Finset.sum_le_sum fun θ _ => measureReal_mono ?_ (measure_ne_top _ _))
  intro D hD
  by_contra hle
  simp only [Set.mem_setOf_eq, not_lt] at hle hD
  apply hD
  apply lbDecode_eq hm Θ hΘne hsep
  have h := (lb_gap_ge_score m hm γ ε C hγ hγ1 hε hεmax hC θ.1 (πhat D)).trans hle
  have h' : ε * (24 * lbScore (πhat D) θ.1) ≤ ε * m := by
    have e : 24 * ε / m * lbScore (πhat D) θ.1 = (ε * (24 * lbScore (πhat D) θ.1)) / m := by ring
    rw [e, div_le_iff₀ hmR] at h
    linarith
  have h'' := le_of_mul_le_mul_left h' hεpos
  linarith

end FanoAverage

universe u

/-- **Theorem 6.13** (`thm:infinite-lwoer-bound`, `chapters/offlineRL.tex:2367–2402`) for
externally randomized estimators. Same constant `c₂ = 1/(36 · 16 · 336²)`, same hard family, test
distribution and data distribution as `offline_minimax_lower_bound`. The estimator is a map
`π̂ : Ω → dataset → policy` on an arbitrary probability space `(Ω, μ)` of seeds, independent of
the data; the failure probability is `μ ⊗ P_θ` of the failure set (its outer probability if the
set is not measurable). No measurability of `π̂` in the seed is assumed. -/
theorem offline_minimax_lower_bound_randomized :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (γ : ℝ) (S : ℕ) (Cstar ε : ℝ), 2 / 3 ≤ γ → γ < 1 → 12 < S → 2 < Cstar →
        ε ≤ 1 / (672 * (1 - γ)) →
        ∃ (State : Type) (_ : Fintype State) (Θ : Type) (_ : Fintype Θ)
          (M : Θ → DiscountedMDP State Bool) (ρ : FiniteDistribution State)
          (db : FiniteDistribution (State × Bool)),
          Fintype.card State = S ∧
          (∀ θ, (M θ).discount = γ) ∧
          (∀ θ θ', (M θ).reward = (M θ').reward) ∧
          (∀ θ,
            ENNReal.ofReal Cstar ≤
                ⨆ sa : State × Bool,
                  ENNReal.ofReal
                      ((M θ).discountedJointOccupancy (M θ).optimalGreedyPolicy ρ sa.1 sa.2) /
                    ENNReal.ofReal (db.prob sa) ∧
              (⨆ sa : State × Bool,
                  ENNReal.ofReal
                      ((M θ).discountedJointOccupancy (M θ).optimalGreedyPolicy ρ sa.1 sa.2) /
                    ENNReal.ofReal (db.prob sa)) ≤ ENNReal.ofReal (2 * Cstar)) ∧
          ∀ N : ℕ, (N : ℝ) ≤ c₂ * S * Cstar / ((1 - γ) ^ 3 * ε ^ 2) →
            letI : MeasurableSpace ((State × Bool) × State) := ⊤
            ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
              (πhat : Ω → (Fin N → (State × Bool) × State) → StationaryPolicy State Bool),
              ∃ θ, (1 : ℝ) / 4 ≤
                (μ.prod (Measure.pi fun _ : Fin N =>
                    ∑ t : (State × Bool) × State,
                      ENNReal.ofReal (db.prob t.1 * ((M θ).transition t.1.1 t.1.2).prob t.2) •
                        Measure.dirac t)).real
                  {p | ε < ∑ s, ρ.prob s *
                      ((M θ).trajectoryExpectedValue (M θ).optimalGreedyPolicy s -
                        (M θ).trajectoryExpectedValue (πhat p.1 p.2) s)} := by
  refine ⟨1 / (36 * (16 * 336 ^ 2)), by norm_num, ?_⟩
  intro γ S Cstar ε hγ hγ1 hS hC hε
  have hγ0 : 0 < γ := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hC0 : 0 < Cstar := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, S = m + 1 := ⟨S - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hm12 : 12 ≤ m := by omega
  set ε₀ : ℝ := if 0 < ε then ε else 1 / (672 * (1 - γ)) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]; split_ifs with h
    · exact h
    · positivity
  have hε₀le : ε₀ ≤ 1 / (672 * (1 - γ)) := by
    rw [hε₀def]; split_ifs
    · exact hε
    · exact le_rfl
  have hε₀ : 0 ≤ ε₀ := hε₀pos.le
  have hεmax₀ : 224 * (1 - γ) * ε₀ / γ ≤ 1 / 2 := by
    have h1 : ε₀ * (672 * (1 - γ)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hε₀le
    rw [div_le_iff₀ hγ0]
    nlinarith
  have hεε₀ : ε ≤ ε₀ := by
    rw [hε₀def]; split_ifs with h
    · exact le_rfl
    · linarith
  obtain ⟨Θf, hcard, hsep⟩ := StatisticalRL.Packing.exists_gilbertVarshamov m
  have hΘne : Θf.Nonempty := Finset.card_pos.mp
    (by exact_mod_cast (lt_of_lt_of_le (Real.exp_pos _) hcard))
  refine ⟨Option (Fin m), inferInstance, Θf, inferInstance,
    fun θ => lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC θ.1, lbTest m hm,
    lbBehavior Cstar m hC hm, ?_, fun θ => rfl, fun θ θ' => rfl,
    fun θ => lb_concentrability m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC θ.1 hε₀pos, ?_⟩
  · simp
  · intro N hN Ω _ μ _ πhat
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hm12R : (12 : ℝ) ≤ m := by exact_mod_cast hm12
    rcases lt_or_ge ε 0 with hneg | hnn
    · -- `ε < 0`: the gap is nonnegative, so the event is certain.
      refine ⟨⟨_, hΘne.choose_spec⟩, ?_⟩
      dsimp only
      rw [pi_diracSum_eq_sampleMeasure]
      have hset : {p : Ω × (Fin N → (Option (Fin m) × Bool) × Option (Fin m)) |
          ε < ∑ s, (lbTest m hm).prob s *
          ((lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hΘne.choose).trajectoryExpectedValue
              (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hΘne.choose).optimalGreedyPolicy s -
            (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hΘne.choose).trajectoryExpectedValue
              (πhat p.1 p.2) s)} = Set.univ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        refine lt_of_lt_of_le hneg (Finset.sum_nonneg fun s _ => mul_nonneg
          ((lbTest m hm).prob_nonneg s) (sub_nonneg.mpr ?_))
        exact (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hΘne.choose).trajectoryValue_le_optimalGreedy
          (πhat p.1 p.2) s
      rw [hset, probReal_univ]
      norm_num
    · -- `ε ≥ 0`: the dataset KL budget at `ε₀` is at most `m/32`.
      have hBN : (N : ℝ) * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε₀ ^ 2 / Cstar) ≤ (m : ℝ) / 32 := by
        rcases hnn.lt_or_eq with hpos | hzero
        · have he : ε₀ = ε := by rw [hε₀def, if_pos hpos]
          rw [he]
          have hX : 0 < (1 - γ) ^ 3 * ε ^ 2 := mul_pos (pow_pos h1γ 3) (pow_pos hpos 2)
          have hNX : (N : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) ≤
              1 / (36 * (16 * 336 ^ 2)) * ((m + 1 : ℕ) : ℝ) * Cstar :=
            (le_div_iff₀ hX).mp hN
          push_cast at hNX
          calc (N : ℝ) * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / Cstar)
              = 16 * 336 ^ 2 * ((N : ℝ) * ((1 - γ) ^ 3 * ε ^ 2)) * Cstar⁻¹ := by ring
            _ ≤ 16 * 336 ^ 2 * (1 / (36 * (16 * 336 ^ 2)) * ((m : ℝ) + 1) * Cstar) * Cstar⁻¹ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNX (by norm_num))
                  (inv_nonneg.mpr hC0.le)
            _ = ((m : ℝ) + 1) / 36 * (Cstar * Cstar⁻¹) := by ring
            _ = ((m : ℝ) + 1) / 36 := by rw [mul_inv_cancel₀ hC0.ne', mul_one]
            _ ≤ (m : ℝ) / 32 := by linarith
        · have hN0 : (N : ℝ) = 0 :=
            le_antisymm (by simpa [← hzero] using hN) (Nat.cast_nonneg N)
          rw [hN0, zero_mul]
          positivity
      haveI : Nonempty Θf := ⟨⟨_, hΘne.choose_spec⟩⟩
      obtain ⟨θ, hθ⟩ := exists_prod_measureReal_ge_of_sum_sections' (I := Θf) μ
        (fun θ => (jointRow (lbBehavior Cstar m hC hm)
          (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC θ.1).transition).sampleMeasure N)
        (fun θ => {p : Ω × (Fin N → (Option (Fin m) × Bool) × Option (Fin m)) |
          ε < ∑ s, (lbTest m hm).prob s *
          ((lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC θ.1).trajectoryExpectedValue
              (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC θ.1).optimalGreedyPolicy s -
            (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC θ.1).trajectoryExpectedValue
              (πhat p.1 p.2) s)})
        (1 / 4)
        (fun ω => by
          have hω := lb_minimax_core_sum m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hm12 hε₀pos Θf
            hcard hsep N hBN (πhat ω)
          rw [Fintype.card_coe]
          refine le_trans (le_of_eq (by ring)) (hω.trans (Finset.sum_le_sum fun θ _ =>
            measureReal_mono ?_ (measure_ne_top _ _)))
          intro D hD
          exact lt_of_le_of_lt hεε₀ hD)
      refine ⟨θ, ?_⟩
      dsimp only
      rw [pi_diracSum_eq_sampleMeasure]
      exact hθ

/-- Dirac-seed check: the deterministic export is the special case `Ω = Unit`, `μ = δ_()`. For a
deterministic `π̂`, the seeded estimator `fun _ => π̂` has the same failure probability, and the
failure set in `Unit × D` is measurable, so the outer measure is the probability. -/
theorem offline_minimax_lower_bound_of_randomized :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (γ : ℝ) (S : ℕ) (Cstar ε : ℝ), 2 / 3 ≤ γ → γ < 1 → 12 < S → 2 < Cstar →
        ε ≤ 1 / (672 * (1 - γ)) →
        ∃ (State : Type) (_ : Fintype State) (Θ : Type) (_ : Fintype Θ)
          (M : Θ → DiscountedMDP State Bool) (ρ : FiniteDistribution State)
          (db : FiniteDistribution (State × Bool)),
          Fintype.card State = S ∧
          (∀ θ, (M θ).discount = γ) ∧
          (∀ θ θ', (M θ).reward = (M θ').reward) ∧
          (∀ θ,
            ENNReal.ofReal Cstar ≤
                ⨆ sa : State × Bool,
                  ENNReal.ofReal
                      ((M θ).discountedJointOccupancy (M θ).optimalGreedyPolicy ρ sa.1 sa.2) /
                    ENNReal.ofReal (db.prob sa) ∧
              (⨆ sa : State × Bool,
                  ENNReal.ofReal
                      ((M θ).discountedJointOccupancy (M θ).optimalGreedyPolicy ρ sa.1 sa.2) /
                    ENNReal.ofReal (db.prob sa)) ≤ ENNReal.ofReal (2 * Cstar)) ∧
          ∀ N : ℕ, (N : ℝ) ≤ c₂ * S * Cstar / ((1 - γ) ^ 3 * ε ^ 2) →
            letI : MeasurableSpace ((State × Bool) × State) := ⊤
            ∀ πhat : (Fin N → (State × Bool) × State) → StationaryPolicy State Bool,
              ∃ θ, (1 : ℝ) / 4 ≤
                (Measure.pi fun _ : Fin N =>
                    ∑ t : (State × Bool) × State,
                      ENNReal.ofReal (db.prob t.1 * ((M θ).transition t.1.1 t.1.2).prob t.2) •
                        Measure.dirac t).real
                  {D | ε < ∑ s, ρ.prob s *
                      ((M θ).trajectoryExpectedValue (M θ).optimalGreedyPolicy s -
                        (M θ).trajectoryExpectedValue (πhat D) s)} := by
  obtain ⟨c₂, hc₂, h⟩ := offline_minimax_lower_bound_randomized.{0}
  refine ⟨c₂, hc₂, ?_⟩
  intro γ S Cstar ε hγ hγ1 hS hC hε
  obtain ⟨State, _, Θ, _, M, ρ, db, h1, h2, h3, h4, h5⟩ := h γ S Cstar ε hγ hγ1 hS hC hε
  refine ⟨State, inferInstance, Θ, inferInstance, M, ρ, db, h1, h2, h3, h4, ?_⟩
  intro N hN
  letI : MeasurableSpace ((State × Bool) × State) := ⊤
  haveI : MeasurableSingletonClass ((State × Bool) × State) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  intro πhat
  obtain ⟨θ, hθ⟩ := h5 N hN Unit (Measure.dirac ()) (fun _ => πhat)
  refine ⟨θ, ?_⟩
  set P := (Measure.pi fun _ : Fin N =>
    ∑ t : (State × Bool) × State,
      ENNReal.ofReal (db.prob t.1 * ((M θ).transition t.1.1 t.1.2).prob t.2) •
        Measure.dirac t) with hP
  set E : Set (Fin N → (State × Bool) × State) := {D | ε < ∑ s, ρ.prob s *
      ((M θ).trajectoryExpectedValue (M θ).optimalGreedyPolicy s -
        (M θ).trajectoryExpectedValue (πhat D) s)} with hE
  have hEm : MeasurableSet E := MeasurableSet.of_discrete
  change (1 : ℝ) / 4 ≤ ((Measure.dirac ()).prod P).real (Prod.snd ⁻¹' E) at hθ
  rw [Measure.dirac_prod, map_measureReal_apply measurable_prodMk_left
    (measurable_snd hEm)] at hθ
  exact hθ

end StatisticalRL.OfflineRL.LowerBound
