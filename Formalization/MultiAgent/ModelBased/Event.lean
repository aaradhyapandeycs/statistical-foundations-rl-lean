import Formalization.MultiAgent.ModelBased.Evaluation
import Formalization.Generative.FiniteHorizonAllLevelBernstein

/-!
# Theorem 7.6: causality, decoupling and the simultaneous Bernstein event

* `DataCausal Pol`: the step-`t` output of the data-to-policy map `Pol` depends only on the sample
  stages `j` with `j + 1 ≥ t` (game steps `≥ t`). A causal oracle applied to the empirical game
  gives such a map (`CausalOracle.dataCausal`).
* `rhoSel G π i hAi b`: `π` (`b = false`) or the greedy true best response
  `brPolicy G π i × π_{-i}` (`b = true`); both are causal functions of `π`.
* `value_factors_future`: the empirical continuation value from game step `j + 2` of `rhoSel` of a
  data-causal map only depends on the strictly-future samples (stages `> j`); no leave-one-out
  argument is needed (`generative_model_model_based.tex:2549`).
* `simultaneous_event`: one event, of probability at least `1 − δ`, on which the Bernstein bound
  holds for two data-causal maps, every player with at least two actions, both policy kinds, and
  every stage/state/joint-action row.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.FiniteHorizonGenerative

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- The step-`t` output depends only on the sample stages `j` with `t ≤ j + 1`. -/
def DataCausal {N : ℕ} (Pol : GameSamples m S H A N → JointPolicy m S A) : Prop :=
  ∀ (data data' : GameSamples m S H A N) (t : ℕ),
    (∀ j : Fin H, t ≤ (j : ℕ) + 1 → ∀ s a n, data ((j, s, a), n) = data' ((j, s, a), n)) →
      Pol data t = Pol data' t

theorem empiricalGame_agree (G : MarkovGame m S H A) (N : ℕ) (hN : 0 < N)
    (data data' : GameSamples m S H A N) (t : ℕ)
    (hd : ∀ j : Fin H, t ≤ (j : ℕ) + 1 → ∀ s a n, data ((j, s, a), n) = data' ((j, s, a), n)) :
    ∀ t', t ≤ t' → (empiricalGame G N hN data).transition t' =
        (empiricalGame G N hN data').transition t' ∧
      ∀ i, (empiricalGame G N hN data).reward i t' = (empiricalGame G N hN data').reward i t' := by
  intro t' ht'
  refine ⟨?_, fun i => rfl⟩
  funext s a
  simp only [empiricalGame]
  split_ifs with h1
  · congr 1
    funext n
    exact hd ⟨t' - 1, by omega⟩ (by simp only; omega) s a n
  · rfl

theorem CausalOracle.dataCausal {O : MarkovGame m S H A → JointPolicy m S A}
    (hO : CausalOracle O) (G : MarkovGame m S H A) (N : ℕ) (hN : 0 < N) :
    DataCausal (fun data : GameSamples m S H A N => O (empiricalGame G N hN data)) := by
  intro data data' t hd
  exact hO _ _ t (empiricalGame_agree G N hN data data' t hd)

/-! ### Causality of the best response -/

theorem brQ_congr (G : MarkovGame m S H A) (π π' : JointPolicy m S A) (i : Fin m)
    (W : Fin S → ℝ) (t : ℕ) (h : π t = π' t) : brQ G π i W t = brQ G π' i W t := by
  funext s b
  simp only [brQ, h]

theorem brW_congr (G : MarkovGame m S H A) (π π' : JointPolicy m S A) (i : Fin m) :
    ∀ k h, (∀ t, h ≤ t → π t = π' t) → brW G π i h k = brW G π' i h k := by
  intro k
  induction k with
  | zero => intro h _; funext s; rfl
  | succ k ih =>
    intro h hπ
    have hn := ih (h + 1) fun t ht => hπ t (by omega)
    funext s
    simp only [brW]
    rw [hn, brQ_congr G π π' i _ h (hπ h le_rfl)]

theorem choose_congr {α : Sort*} {p q : α → Prop} (hpq : p = q) (hp : ∃ x, p x)
    (hq : ∃ x, q x) : Classical.choose hp = Classical.choose hq := by
  subst hpq; rfl

theorem finiteDistribution_ext {Ω : Type*} [Fintype Ω] {d d' : FiniteDistribution Ω}
    (h : ∀ x, d.prob x = d'.prob x) : d = d' := by
  cases d; cases d'
  simp only [FiniteDistribution.mk.injEq]
  exact funext h

theorem brPolicy_congr (G : MarkovGame m S H A) (π π' : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) (h : ℕ) (hπ : ∀ t, h ≤ t → π t = π' t) :
    ∀ t, h ≤ t → brPolicy G π i hAi t = brPolicy G π' i hAi t := by
  intro t ht
  have hW := brW_congr G π π' i (H - t) (t + 1) fun t' ht' => hπ t' (by omega)
  have hQ := brQ_congr G π π' i (brW G π' i (t + 1) (H - t)) t (hπ t ht)
  funext s
  simp only [brPolicy]
  congr 1
  apply choose_congr
  rw [hW, hQ]

theorem deviate_congr_step (π π' : JointPolicy m S A) (i : Fin m) (σ σ' : PlayerPolicy S (A i))
    (t : ℕ) (hπ : π t = π' t) (hσ : σ t = σ' t) : deviate π i σ t = deviate π' i σ' t := by
  funext s
  apply finiteDistribution_ext
  intro a
  simp only [deviate, hπ, hσ]

/-- `π` itself (`false`) or the greedy true best response of player `i` against `π_{-i}`
(`true`). -/
noncomputable def rhoSel (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) : Bool → JointPolicy m S A
  | false => π
  | true => deviate π i (brPolicy G π i hAi)

theorem rhoSel_congr (G : MarkovGame m S H A) (π π' : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) (b : Bool) (h : ℕ) (hπ : ∀ t, h ≤ t → π t = π' t) :
    ∀ t, h ≤ t → rhoSel G π i hAi b t = rhoSel G π' i hAi b t := by
  intro t ht
  cases b with
  | false => exact hπ t ht
  | true =>
    exact deviate_congr_step _ _ i _ _ t (hπ t ht) (brPolicy_congr G π π' i hAi h hπ t ht)

/-- The empirical continuation value from game step `j + 2` factors through the strictly-future
samples. -/
theorem value_factors_future (G : MarkovGame m S H A) (N : ℕ) (hN : 0 < N)
    (Pol : GameSamples m S H A N → JointPolicy m S A) (hPol : DataCausal Pol)
    (i : Fin m) (hAi : 0 < A i) (b : Bool) (j : Fin H) (k : ℕ)
    (data data' : GameSamples m S H A N)
    (hd : ∀ j' : Fin H, j < j' → ∀ s a n, data ((j', s, a), n) = data' ((j', s, a), n)) :
    valueJ (empiricalGame G N hN data) (rhoSel G (Pol data) i hAi b) i ((j : ℕ) + 2) k =
      valueJ (empiricalGame G N hN data') (rhoSel G (Pol data') i hAi b) i ((j : ℕ) + 2) k := by
  have hd' : ∀ t, (j : ℕ) + 2 ≤ t → ∀ j' : Fin H, t ≤ (j' : ℕ) + 1 →
      ∀ s a n, data ((j', s, a), n) = data' ((j', s, a), n) := by
    intro t ht j' hj'
    exact hd j' (by rw [Fin.lt_def]; omega)
  have hπ : ∀ t, (j : ℕ) + 2 ≤ t → Pol data t = Pol data' t := fun t ht => hPol data data' t (hd' t ht)
  have hG := empiricalGame_agree G N hN data data' ((j : ℕ) + 2) (hd' _ le_rfl)
  exact valueJ_congr_from _ _ _ _ i k _ (rhoSel_congr G _ _ i hAi b _ hπ)
    (fun t ht => (hG t ht).1) (fun t ht => (hG t ht).2 i)

/-! ### The simultaneous event -/

/-- The empirical stage is the empirical game's kernel at game step `j + 1`. -/
theorem empiricalStage_eq_empiricalGame (G : MarkovGame m S H A) (hS : 0 < S)
    (hA : ∀ i, 0 < A i) (N : ℕ) (hN : 0 < N) (data : GameSamples m S H A N) (j : Fin H)
    (s : Fin S) (a : JointAction m A) :
    (empiricalStage (gameStages G hS hA) N hN data j).transition s a =
      (empiricalGame G N hN data).transition ((j : ℕ) + 1) s a := by
  have h1 : 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ H := ⟨by omega, j.isLt⟩
  simp only [empiricalGame, dif_pos h1]
  have hj : (⟨(j : ℕ) + 1 - 1, by omega⟩ : Fin H) = j := Fin.ext (by simp)
  rw [hj]
  rfl

/-- Index set of the simultaneous event: oracle, player with at least two actions, policy kind,
stage, state, joint action. -/
abbrev EventIndex (m S H : ℕ) (A : Fin m → ℕ) :=
  Fin 2 × {i : Fin m // 2 ≤ A i} × Bool × Fin H × Fin S × JointAction m A

theorem card_eventIndex :
    (Fintype.card (EventIndex m S H A) : ℝ) =
      4 * (Finset.univ.filter (fun i : Fin m => 2 ≤ A i)).card * H * S * ∏ i, (A i : ℝ) := by
  simp only [EventIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_subtype, Fintype.card_pi, Nat.cast_mul, Nat.cast_prod, Nat.cast_ofNat]
  ring

/-- The empirical continuation value appearing in the event. -/
noncomputable def contValue (G : MarkovGame m S H A) (N : ℕ) (hN : 0 < N)
    (Pol : Fin 2 → GameSamples m S H A N → JointPolicy m S A)
    (x : EventIndex m S H A) (data : GameSamples m S H A N) : Fin S → ℝ :=
  valueJ (empiricalGame G N hN data) (rhoSel G (Pol x.1 data) x.2.1.1 (by have := x.2.1.2; omega)
    x.2.2.1) x.2.1.1 ((x.2.2.2.1 : ℕ) + 2) (H + 1 - ((x.2.2.2.1 : ℕ) + 2))

theorem simultaneous_event (G : MarkovGame m S H A)
    (hR : ∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1)
    (hS : 0 < S) (hA : ∀ i, 0 < A i) (N : ℕ) (hN : 0 < N)
    (Pol : Fin 2 → GameSamples m S H A N → JointPolicy m S A) (hPol : ∀ o, DataCausal (Pol o))
    (hJ : Nonempty (EventIndex m S H A))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (gameSamplingLaw G hS hA N).real {data |
      ∀ x : EventIndex m S H A,
        |((empiricalGame G N hN data).transition ((x.2.2.2.1 : ℕ) + 1) x.2.2.2.2.1
              x.2.2.2.2.2).expectation (contValue G N hN Pol x data) -
            (G.transition ((x.2.2.2.1 : ℕ) + 1) x.2.2.2.2.1 x.2.2.2.2.2).expectation
              (contValue G N hN Pol x data)| ≤
          Real.sqrt (2 * Real.log (4 * Fintype.card (EventIndex m S H A) / δ) / N) *
              Real.sqrt ((G.transition ((x.2.2.2.1 : ℕ) + 1) x.2.2.2.2.1 x.2.2.2.2.2).variance
                (contValue G N hN Pol x data)) +
            2 * H * Real.log (4 * Fintype.card (EventIndex m S H A) / δ) / (3 * N)} := by
  classical
  let J := EventIndex m S H A
  let k : ℝ := Fintype.card J
  let η := δ / k
  let μ := gameSamplingLaw G hS hA N
  let E := gameStages G hS hA
  haveI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (samplingLaw E N); infer_instance
  have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast Fintype.card_pos_iff.mpr hJ
  have hk : 0 < k := by linarith
  have hη : 0 < η := div_pos hδ hk
  have hη1 : η < 1 := by dsimp [η]; exact (div_lt_iff₀ hk).2 (by linarith)
  let good (x : J) : Set (GameSamples m S H A N) := {data |
    |((empiricalStage E N hN data x.2.2.2.1).transition x.2.2.2.2.1 x.2.2.2.2.2).expectation
        (contValue G N hN Pol x data) -
      ((E x.2.2.2.1).transition x.2.2.2.2.1 x.2.2.2.2.2).expectation (contValue G N hN Pol x data)| ≤
      FiniteDistribution.bernsteinRadius ((E x.2.2.2.1).transition x.2.2.2.2.1 x.2.2.2.2.2) N 1 η
        (contValue G N hN Pol x data)}
  have hs (x : J) : 1 - η < μ.real (good x) := by
    obtain ⟨o, ⟨i, hi⟩, b, j, s, a⟩ := x
    have hAi : 0 < A i := by omega
    refine futureValue_row_bernstein E N hN j s a
      (fun data => contValue G N hN Pol (o, ⟨i, hi⟩, b, j, s, a) data) ?_ ?_ η hη hη1
    · intro data t
      refine (valueJ_mem_Icc _ _ i _ _ ?_ t).1
      intro t' ht1 ht2 s' a'
      exact hR i t' s' a' (by omega) (by omega)
    · intro x data
      exact value_factors_future G N hN (Pol o) (hPol o) i hAi b j _ data _ fun j' hj' s a n => by
        simp [completeFutureData, futureData, hj']
  have hb (x : J) : μ.real (good x)ᶜ ≤ η := by
    have hp := measureReal_compl (μ := μ) ((Set.to_countable (good x)).measurableSet)
    rw [probReal_univ] at hp
    have hh := hs x
    linarith
  have hu : μ.real (⋃ x : J, (good x)ᶜ) ≤ δ := by
    calc
      _ ≤ ∑ x : J, μ.real (good x)ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _x : J, η := Finset.sum_le_sum fun x _ => hb x
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change k * (δ / k) = δ
        field_simp [hk.ne']
  have hcomp := measureReal_compl (μ := μ) ((Set.to_countable (⋃ x : J, (good x)ᶜ)).measurableSet)
  rw [probReal_univ] at hcomp
  have hp : 1 - δ ≤ μ.real (⋃ x : J, (good x)ᶜ)ᶜ := by linarith
  apply hp.trans
  apply measureReal_mono _ (measure_ne_top μ _)
  intro data hd x
  have hh : data ∈ good x := by
    by_contra hn
    exact hd (Set.mem_iUnion.mpr ⟨x, hn⟩)
  simp only [good, Set.mem_setOf_eq] at hh
  rw [empiricalStage_eq_empiricalGame G hS hA N hN data] at hh
  have hEt : ∀ j : Fin H, (E j).transition = G.transition ((j : ℕ) + 1) := fun j => rfl
  rw [hEt, FiniteDistribution.bernsteinRadius_eq_source] at hh
  have hlog : 4 * ((1 : ℕ) : ℝ) / η = 4 * k / δ := by
    dsimp [η]; push_cast; field_simp
  rw [hlog] at hh
  refine hh.trans (add_le_add le_rfl ?_)
  -- the sup norm of the continuation value is at most `H`
  have hL : 0 ≤ Real.log (4 * k / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ]; linarith)
  have hnorm : ‖contValue G N hN Pol x data‖ ≤ H := by
    refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg H)).mpr fun t => ?_
    obtain ⟨o, ⟨i, hi⟩, b, j, s, a⟩ := x
    have hv := valueJ_mem_Icc (empiricalGame G N hN data) (rhoSel G (Pol o data) i (by omega) b) i
      (H + 1 - ((j : ℕ) + 2)) ((j : ℕ) + 2)
      (fun t' ht1 ht2 s' a' => hR i t' s' a' (by omega) (by omega)) t
    have hc : contValue G N hN Pol (o, ⟨i, hi⟩, b, j, s, a) data t =
        valueJ (empiricalGame G N hN data) (rhoSel G (Pol o data) i (by omega) b) i ((j : ℕ) + 2)
          (H + 1 - ((j : ℕ) + 2)) t := rfl
    rw [Real.norm_eq_abs, hc, abs_of_nonneg hv.1]
    refine hv.2.trans ?_
    exact_mod_cast (show H + 1 - ((j : ℕ) + 2) ≤ H by omega)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : 2 * ‖contValue G N hN Pol x data‖ * Real.log (4 * k / δ) ≤ 2 * H * Real.log (4 * k / δ) := by
    have := mul_le_mul_of_nonneg_right hnorm hL
    linarith
  exact div_le_div_of_nonneg_right this (by positivity)

end StatisticalRL.Ch7Rest.Marl76
