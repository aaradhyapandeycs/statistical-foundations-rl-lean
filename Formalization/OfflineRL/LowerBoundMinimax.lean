import Formalization.OfflineRL.LowerBoundValueGap
import Formalization.OfflineRL.LowerBoundDataKL
import Formalization.Probability.Fano.HammingPacking
import Formalization.Probability.Fano.FanoLemma
import Formalization.Generative.GenerativeLowerBoundFanoThreshold

/-!
# Offline minimax lower bound (`thm:infinite-lwoer-bound`)

`chapters/offlineRL.tex:2367–2402`, proof `:2432–2927`, Appendix C `:5498–5933`.

* Step 1 (`:2655–2730`): the score `∑_s (1 - π(θ_s|s))` of a policy, its minimizer over the packing
  `Θ` (`lbDecode`), and the fact that `V⋆_θ(ρ) - V^π_θ(ρ) ≤ ε` forces the minimizer to be `θ`
  (`lb_gap_ge_score`, `lbDecode_eq`).
* Step 2 (`:2734–2792`): Fano's inequality in its per-test form (`fano_test_average_error_lower`),
  reindexed to the packing, with the dataset KL bound of Step 3 (`lb_fano_core`).
* Step 4 (`:2897–2927`): the threshold arithmetic with `c₂ = 1/(36 · 16 · 336²)`
  (`lb_minimax_core`, `offline_minimax_lower_bound`).

`offline_minimax_lower_bound` states the printed hypotheses only. The source does not assume
`ε > 0` (see `docs/SOURCE-ISSUES.md`, C9). For `ε < 0` the event has probability one. For `ε = 0`,
Lean's `x / 0 = 0` makes the printed threshold `N ≤ 0`, and the construction is built at the
admissible accuracy `1/(672(1-γ))`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.OfflineRL.JointRow

/-- The source's one-triple law, written as a finite sum of point masses, is the joint row law;
its `N`-fold product is the sample law. -/
theorem pi_diracSum_eq_sampleMeasure {State Action : Type*} [Fintype State] [Fintype Action]
    (db : FiniteDistribution (State × Action)) (P : State → Action → FiniteDistribution State)
    (N : ℕ) :
    letI : MeasurableSpace ((State × Action) × State) := ⊤
    (Measure.pi fun _ : Fin N =>
        ∑ t : (State × Action) × State,
          ENNReal.ofReal (db.prob t.1 * (P t.1.1 t.1.2).prob t.2) • Measure.dirac t) =
      (jointRow db P).sampleMeasure N := by
  letI : MeasurableSpace ((State × Action) × State) := ⊤
  classical
  have hrow : (∑ t : (State × Action) × State,
      ENNReal.ofReal (db.prob t.1 * (P t.1.1 t.1.2).prob t.2) • Measure.dirac t) =
      (jointRow db P).rowMeasure := by
    refine Measure.ext_iff_singleton.2 fun x => ?_
    rw [Measure.finset_sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator_apply,
      Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ x)]
    unfold FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ x MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply]
    rfl
  unfold FiniteDistribution.sampleMeasure
  rw [hrow]

end StatisticalRL.OfflineRL.JointRow

namespace StatisticalRL.OfflineRL.LowerBound

open StatisticalRL.OfflineRL.JointRow StatisticalRL.DiscountedMDP

/-- The Step 1 score `∑_s (1 - π(θ_s | s))` of a policy against `θ`. -/
noncomputable def lbScore {m : ℕ} (π : StationaryPolicy (Option (Fin m)) Bool)
    (θ : Fin m → Bool) : ℝ :=
  ∑ i, (1 - (π (some i)).prob (θ i))

/-- `d_H(θ', θ) - score(θ) ≤ score(θ')`. -/
theorem lbScore_sep {m : ℕ} (π : StationaryPolicy (Option (Fin m)) Bool) (θ θ' : Fin m → Bool) :
    (hammingDist θ' θ : ℝ) - lbScore π θ ≤ lbScore π θ' := by
  classical
  have hterm : ∀ i, (if θ' i ≠ θ i then (1 : ℝ) else 0) - (1 - (π (some i)).prob (θ i)) ≤
      1 - (π (some i)).prob (θ' i) := by
    intro i
    have hsum : (π (some i)).prob (θ i) + (π (some i)).prob (!θ i) = 1 := by
      have := (π (some i)).sum_prob
      rwa [sum_bool_split _ (θ i)] at this
    have h0 := (π (some i)).prob_nonneg (θ i)
    have h0' := (π (some i)).prob_nonneg (!θ i)
    by_cases h : θ' i = θ i
    · rw [if_neg (not_not.mpr h), h]; linarith
    · have key : ∀ x y : Bool, x ≠ y → x = !y := by decide
      rw [if_pos h, key _ _ h]; linarith
  have hd : (hammingDist θ' θ : ℝ) = ∑ i, (if θ' i ≠ θ i then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
    rfl
  unfold lbScore
  rw [hd, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => hterm i

theorem exists_lbScore_min {m : ℕ} (Θ : Finset (Fin m → Bool)) (hΘ : Θ.Nonempty)
    (π : StationaryPolicy (Option (Fin m)) Bool) :
    ∃ θ ∈ Θ, ∀ θ' ∈ Θ, lbScore π θ ≤ lbScore π θ' :=
  Finset.exists_min_image Θ (lbScore π) hΘ

/-- The Step 1 decoder `θ̂ = argmin_{θ ∈ Θ} ∑_s (1 - π(θ_s | s))` (`eq:defn-theta-hat-inf-LB`). -/
noncomputable def lbDecode {m : ℕ} (Θ : Finset (Fin m → Bool)) (hΘ : Θ.Nonempty)
    (π : StationaryPolicy (Option (Fin m)) Bool) : Θ :=
  ⟨Classical.choose (exists_lbScore_min Θ hΘ π), (Classical.choose_spec (exists_lbScore_min Θ hΘ π)).1⟩

/-- On a packing with pairwise distance `m/8`, a score at most `m/24` decodes correctly. -/
theorem lbDecode_eq {m : ℕ} (hm : 1 ≤ m) (Θ : Finset (Fin m → Bool)) (hΘ : Θ.Nonempty)
    (hsep : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, θ ≠ θ' → (m : ℝ) / 8 ≤ hammingDist θ θ')
    (π : StationaryPolicy (Option (Fin m)) Bool) (θ : Θ) (hs : lbScore π θ.1 ≤ (m : ℝ) / 24) :
    lbDecode Θ hΘ π = θ := by
  by_contra hne
  have hmin : lbScore π (lbDecode Θ hΘ π).1 ≤ lbScore π θ.1 :=
    (Classical.choose_spec (exists_lbScore_min Θ hΘ π)).2 θ.1 θ.2
  have hne' : (lbDecode Θ hΘ π).1 ≠ θ.1 := fun h => hne (Subtype.ext h)
  have hdist := hsep _ (lbDecode Θ hΘ π).2 θ.1 θ.2 hne'
  have hsc := lbScore_sep π θ.1 (lbDecode Θ hΘ π).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  linarith

/-- Averaging `eq:infinite-delta-key-auxiliary` over `ρ`:
`V⋆_θ(ρ) - V^π_θ(ρ) ≥ (24 ε / (S-1)) ∑_s (1 - π(θ_s | s))`. -/
theorem lb_gap_ge_score (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool)
    (π : StationaryPolicy (Option (Fin m)) Bool) :
    24 * ε / m * lbScore π θ ≤
      ∑ s, (lbTest m hm).prob s *
        ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).trajectoryExpectedValue
            (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy s -
          (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).trajectoryExpectedValue π s) := by
  rw [Fintype.sum_option]
  have h0 : (lbTest m hm).prob none = 0 := rfl
  rw [h0, zero_mul, zero_add]
  unfold lbScore
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : (lbTest m hm).prob (some i) = 1 / m := rfl
  rw [h1]
  have hgap := lb_value_gap_state m hm γ ε C hγ hγ1 hε hεmax hC θ π i
  have hm0 : (0 : ℝ) ≤ 1 / m := by positivity
  calc 24 * ε / m * (1 - (π (some i)).prob (θ i)) =
        1 / m * (24 * ε * (1 - (π (some i)).prob (θ i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap hm0

local instance lbMinStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

local instance (priority := high) lbMinTripleMeasurable (m : ℕ) :
    MeasurableSpace ((Option (Fin m) × Bool) × Option (Fin m)) := ⊤

local instance (priority := high) lbMinTripleSingleton (m : ℕ) :
    MeasurableSingletonClass ((Option (Fin m) × Bool) × Option (Fin m)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

section Fano

variable (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
  (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C)

/-- Step 2: Fano's inequality over a family of at least four hard instances. If the dataset
KL budget `N c₃ (1-γ)³ ε² / C` is at most `log|Θ|/4`, every decoder errs with probability at least
`1/4` under some `θ ∈ Θ`. -/
theorem lb_fano_core (Θ : Finset (Fin m → Bool)) (hK : (4 : ℝ) ≤ Θ.card) (N : ℕ)
    (hN : (N : ℝ) * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / C) ≤ Real.log Θ.card / 4)
    (ψ : (Fin N → (Option (Fin m) × Bool) × Option (Fin m)) → Θ) :
    ∃ θ : Θ, (1 : ℝ) / 4 ≤
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
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ j : Fin (M + 1), (P j).real {ω | ψ'.1 ω ≠ j} < ∑ _j : Fin (M + 1), (1 / 4 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => ?_
    have hset : {ω | ψ'.1 ω ≠ j} = {D | ψ D ≠ e j} := by
      ext D
      exact not_congr e.symm_apply_eq
    rw [hset]
    exact hcon (e j)
  have hsc : ∑ _j : Fin (M + 1), (1 / 4 : ℝ) = ((M : ℝ) + 1) / 4 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  rw [hsc] at hlt
  have h2 := mul_lt_mul_of_pos_left hlt (by positivity : (0 : ℝ) < 1 / ((M : ℝ) + 1))
  have e2 : 1 / ((M : ℝ) + 1) * (((M : ℝ) + 1) / 4) = 1 / 4 := by
    rw [← mul_div_assoc, one_div_mul_cancel hpos.ne']
  linarith

/-- Steps 1, 2 and 4 for a fixed admissible accuracy `ε > 0`: on the Gilbert–Varshamov packing
of `{0,1}^m` (`m ≥ 12`), if `N c₃ (1-γ)³ ε² / C ≤ m/32`, every policy estimator has
`P_θ(V⋆_θ(ρ) - V^π̂_θ(ρ) > ε) ≥ 1/4` for some `θ ∈ Θ`. -/
theorem lb_minimax_core (hm12 : 12 ≤ m) (hεpos : 0 < ε) (Θ : Finset (Fin m → Bool))
    (hcard : Real.exp ((m : ℝ) / 8) ≤ Θ.card)
    (hsep : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, θ ≠ θ' → (m : ℝ) / 8 ≤ hammingDist θ θ') (N : ℕ)
    (hN : (N : ℝ) * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / C) ≤ (m : ℝ) / 32)
    (πhat : (Fin N → (Option (Fin m) × Bool) × Option (Fin m)) →
      StationaryPolicy (Option (Fin m)) Bool) :
    ∃ θ : Θ, (1 : ℝ) / 4 ≤
      ((jointRow (lbBehavior C m hC hm)
          (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).transition).sampleMeasure N).real
        {D | ε < ∑ s, (lbTest m hm).prob s *
          ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).trajectoryExpectedValue
              (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).optimalGreedyPolicy s -
            (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ.1).trajectoryExpectedValue (πhat D) s)} := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm12R : (12 : ℝ) ≤ m := by exact_mod_cast hm12
  -- `|Θ| ≥ e^{3/2} ≥ 4`
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
  have hΘne : Θ.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0 : ℝ) < Θ.card))
  obtain ⟨θ, hθ⟩ := lb_fano_core m hm γ ε C hγ hγ1 hε hεmax hC Θ hK N hN'
    (fun D => lbDecode Θ hΘne (πhat D))
  refine ⟨θ, hθ.trans (measureReal_mono ?_ (measure_ne_top _ _))⟩
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

end Fano

/-- **Theorem 6.13** (`thm:infinite-lwoer-bound`, `chapters/offlineRL.tex:2367–2402`): the
library form of `StatisticalRL.Statements.Ch6.Thm6_13`, with `c₂ = 1/(36 · 16 · 336²)`. -/
theorem offline_minimax_lower_bound :
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
  refine ⟨1 / (36 * (16 * 336 ^ 2)), by norm_num, ?_⟩
  intro γ S Cstar ε hγ hγ1 hS hC hε
  have hγ0 : 0 < γ := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hC0 : 0 < Cstar := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, S = m + 1 := ⟨S - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hm12 : 12 ≤ m := by omega
  -- the accuracy at which the hard family is built
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
  refine ⟨Option (Fin m), inferInstance, Θf, inferInstance,
    fun θ => lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC θ.1, lbTest m hm,
    lbBehavior Cstar m hC hm, ?_, fun θ => rfl, fun θ θ' => rfl,
    fun θ => lb_concentrability m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC θ.1 hε₀pos, ?_⟩
  · simp
  · intro N hN πhat
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hm12R : (12 : ℝ) ≤ m := by exact_mod_cast hm12
    rcases lt_or_ge ε 0 with hneg | hnn
    · -- `ε < 0`: the gap is nonnegative, so the event is certain.
      have hΘne : Θf.Nonempty := Finset.card_pos.mp
        (by exact_mod_cast (lt_of_lt_of_le (Real.exp_pos _) hcard))
      refine ⟨⟨_, hΘne.choose_spec⟩, ?_⟩
      dsimp only
      rw [pi_diracSum_eq_sampleMeasure]
      have hset : {D | ε < ∑ s, (lbTest m hm).prob s *
          ((lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hΘne.choose).trajectoryExpectedValue
              (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hΘne.choose).optimalGreedyPolicy s -
            (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hΘne.choose).trajectoryExpectedValue
              (πhat D) s)} = Set.univ := by
        ext D
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        refine lt_of_lt_of_le hneg (Finset.sum_nonneg fun s _ => mul_nonneg
          ((lbTest m hm).prob_nonneg s) (sub_nonneg.mpr ?_))
        exact (lbMDP m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hΘne.choose).trajectoryValue_le_optimalGreedy
          (πhat D) s
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
      obtain ⟨θ, hθ⟩ := lb_minimax_core m hm γ ε₀ Cstar hγ hγ1 hε₀ hεmax₀ hC hm12 hε₀pos Θf
        hcard hsep N hBN πhat
      refine ⟨θ, ?_⟩
      dsimp only
      rw [pi_diracSum_eq_sampleMeasure]
      refine hθ.trans (measureReal_mono ?_ (measure_ne_top _ _))
      intro D hD
      exact lt_of_le_of_lt hεε₀ hD

end StatisticalRL.OfflineRL.LowerBound
