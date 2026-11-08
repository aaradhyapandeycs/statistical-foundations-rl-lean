import Formalization.Generative.FiniteHorizonMainSample

/-! The finite-horizon statistical pipeline of `Thm:sample-compl-finite`, parametrized by
an arbitrary data-selected deterministic policy `sel data`. Two properties of `sel` are
used, both as explicit hypotheses of the consuming theorems:

* `SelectorFactorsFuture`: decisions after stage `h` depend only on the strictly-future
  samples (the source's causality, MB:2547–2549), which gives the Bernstein step;
* empirical optimality at every suffix, which replaces the backward-greedy identity.

This is a copy of `FiniteHorizonAllLevelBernstein` … `FiniteHorizonMainSample` with the
planner `backwardGreedyActions fallback (empiricalStages …)` replaced by `sel`; no
existing declaration is changed. The fixed comparison policy stays the true-model
backward-greedy planner, and the constant stays 8640. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance selectorPipelineStateMeasurable : MeasurableSpace State := ⊤

/-- Causality of a data-selected policy: decisions at stages after `h` are unchanged when
all samples at stages `≤ h` are overwritten. -/
def SelectorFactorsFuture {H N : ℕ} (sel : Samples State Action H N → ℕ → State → Action) :
    Prop :=
  ∀ (h : Fin H) (x : State) (data : Samples State Action H N) (k : ℕ) (s : State),
    sel data (h.val + 1 + k) s = sel (completeFutureData h N x (futureData h N data)) (h.val + 1 + k) s

/-- Empirical optimality of a data-selected policy at every suffix and state. -/
def SelectorEmpiricallyOptimal {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ)
    (hN : 0 < N) (sel : Samples State Action H N → ℕ → State → Action) : Prop :=
  ∀ data h s, policyTrajectorySuffix (empiricalStages E N hN data) (sel data) h s =
    EnvironmentStage.optimalValue ((empiricalStages E N hN data).drop h) s

/-- Simultaneous all-stage true V and forced-action Q loss of a policy `f`. -/
def PolicyPerformanceBound {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (f : ℕ → State → Action) (R : ℝ) : Prop :=
  ∀ h : ℕ,
    (∀ s, 0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
        policyTrajectorySuffix (List.ofFn E) f h s ∧
      EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
        policyTrajectorySuffix (List.ofFn E) f h s ≤ R) ∧
    (∀ s a, 0 ≤ EnvironmentStage.optimalQ ((List.ofFn E).drop h) s a -
        policyTrajectoryQSuffix (List.ofFn E) f h s a ∧
      EnvironmentStage.optimalQ ((List.ofFn E).drop h) s a -
        policyTrajectoryQSuffix (List.ofFn E) f h s a ≤ R)

theorem policyPerformanceBound_mono {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (f : ℕ → State → Action) (R S : ℝ) (hRS : R ≤ S) (he : PolicyPerformanceBound E f R) :
    PolicyPerformanceBound E f S := by
  intro h
  exact ⟨fun s ↦ ⟨((he h).1 s).1, ((he h).1 s).2.trans hRS⟩,
    fun s a ↦ ⟨((he h).2 s a).1, ((he h).2 s a).2.trans hRS⟩⟩

/-- The true-model auxiliary value of the selected suffix policy after stage `h`. -/
noncomputable def selectorTrueAuxiliaryContinuation {H N : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (sel : Samples State Action H N → ℕ → State → Action) (h : Fin H) (l : ℕ)
    (data : Samples State Action H N) : State → ℝ :=
  trueAuxiliaryValueAt (List.ofFn E) (sel data) l (h.val + 1)

theorem selectorTrueAuxiliaryContinuation_factors_future {H N : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (sel : Samples State Action H N → ℕ → State → Action) (hsel : SelectorFactorsFuture sel)
    (h : Fin H) (l : ℕ) (x : State) (data : Samples State Action H N) :
    selectorTrueAuxiliaryContinuation E sel h l data =
      selectorTrueAuxiliaryContinuation E sel h l
        (completeFutureData h N x (futureData h N data)) := by
  apply trueAuxiliaryValueAt_suffix_congr
  · rfl
  · intro k s
    exact hsel h x data k s

noncomputable def selectorSourceAuxiliaryContinuation {H N : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (sel : Samples State Action H N → ℕ → State → Action) (fixed : ℕ → State → Action)
    (b : Bool) (l : ℕ) (h : Fin H) (data : Samples State Action H N) : State → ℝ :=
  if b then trueAuxiliaryValueAt (List.ofFn E) fixed l (h.val + 1)
    else selectorTrueAuxiliaryContinuation E sel h l data

theorem selectorSourceAuxiliaryContinuation_nonneg {H N : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (sel : Samples State Action H N → ℕ → State → Action) (fixed : ℕ → State → Action)
    (b : Bool) (l : ℕ) (h : Fin H) (data : Samples State Action H N) (t : State) :
    0 ≤ selectorSourceAuxiliaryContinuation E sel fixed b l h data t := by
  cases b
  · exact trueAuxiliaryValue_nonneg _ _ _ _
  · exact trueAuxiliaryValue_nonneg _ _ _ _

theorem selectorSourceAuxiliaryContinuation_factors_future {H N : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (sel : Samples State Action H N → ℕ → State → Action) (hsel : SelectorFactorsFuture sel)
    (fixed : ℕ → State → Action) (b : Bool) (l : ℕ) (h : Fin H)
    (x : State) (data : Samples State Action H N) :
    selectorSourceAuxiliaryContinuation E sel fixed b l h data =
      selectorSourceAuxiliaryContinuation E sel fixed b l h
        (completeFutureData h N x (futureData h N data)) := by
  cases b
  · exact selectorTrueAuxiliaryContinuation_factors_future E sel hsel h l x data
  · rfl

theorem selectorSourceAuxiliaryContinuation_row_bernstein {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (sel : Samples State Action H N → ℕ → State → Action) (hsel : SelectorFactorsFuture sel)
    (fixed : ℕ → State → Action) (b : Bool) (l : ℕ)
    (h : Fin H) (s : State) (a : Action) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw E N).real {data |
      |((empiricalStage E N hN data h).transition s a).expectation
          (selectorSourceAuxiliaryContinuation E sel fixed b l h data) -
        ((E h).transition s a).expectation
          (selectorSourceAuxiliaryContinuation E sel fixed b l h data)| ≤
      FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1 δ
        (selectorSourceAuxiliaryContinuation E sel fixed b l h data)} :=
  futureValue_row_bernstein E N hN h s a _
    (selectorSourceAuxiliaryContinuation_nonneg E sel fixed b l h)
    (selectorSourceAuxiliaryContinuation_factors_future E sel hsel fixed b l h) δ hδ hδ1

/-- The exact rowwise common event for the selected and the fixed policy families. -/
def SelectorAllLevelBernsteinEvent {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (sel : Samples State Action H N → ℕ → State → Action) (fixed : ℕ → State → Action)
    (δ : ℝ) (data : Samples State Action H N) : Prop :=
  ∀ (b : Bool) (l : Fin (Nat.log 2 H + 1)) (h : Fin H) (s : State) (a : Action),
    |policyRowResidual (E h) (empiricalStage E N hN data h)
      (selectorSourceAuxiliaryContinuation E sel fixed b l.val h data) s a| ≤
    FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1
      (allLevelConfidence (H := H) State Action δ)
      (selectorSourceAuxiliaryContinuation E sel fixed b l.val h data)

/-- One event covers both policy families, every level and every row; the confidence
cost is exactly `2·K·H·S·A`. Copy of `simultaneous_sourceAuxiliaryContinuation_bernstein`. -/
theorem selectorAllLevelBernsteinEvent_probability {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (hH : 0 < H)
    (sel : Samples State Action H N → ℕ → State → Action) (hsel : SelectorFactorsFuture sel)
    (fixed : ℕ → State → Action) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw E N).real
      {data | SelectorAllLevelBernsteinEvent E N hN sel fixed δ data} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  let K := Nat.log 2 H + 1
  letI : Nonempty (Fin K) := ⟨⟨0, Nat.zero_lt_succ _⟩⟩
  let I := Fin H × State × Action
  let J := Bool × Fin K × I
  let m : ℝ := Fintype.card J
  let η := δ / m
  let μ := samplingLaw E N
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm1 : 1 ≤ m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hη : 0 < η := div_pos hδ hm
  have hη1 : η < 1 := by dsimp [η]; exact (div_lt_iff₀ hm).2 (by linarith)
  let value (i : J) (data : Samples State Action H N) : State → ℝ :=
    selectorSourceAuxiliaryContinuation E sel fixed i.1 i.2.1.val i.2.2.1 data
  let good (i : J) : Set (Samples State Action H N) := {data |
    |((empiricalStage E N hN data i.2.2.1).transition i.2.2.2.1 i.2.2.2.2).expectation (value i data) -
      ((E i.2.2.1).transition i.2.2.2.1 i.2.2.2.2).expectation (value i data)| ≤
      FiniteDistribution.bernsteinRadius ((E i.2.2.1).transition i.2.2.2.1 i.2.2.2.2) N 1 η
        (value i data)}
  let bad (i : J) := (good i)ᶜ
  have hs (i : J) : 1 - η < μ.real (good i) := by
    rcases i with ⟨b,l,h,s,a⟩
    exact selectorSourceAuxiliaryContinuation_row_bernstein E N hN sel hsel fixed b l.val h s a
      η hη hη1
  have hb (i : J) : μ.real (bad i) < η := by
    have hp := measureReal_compl (μ := μ) ((Set.to_countable (good i)).measurableSet)
    rw [probReal_univ] at hp
    have hh := hs i
    change μ.real (good i)ᶜ < η
    linarith
  have hu : μ.real (⋃ i : J, bad i) < δ := by
    calc
      _ ≤ ∑ i : J, μ.real (bad i) := measureReal_iUnion_fintype_le _
      _ < ∑ _i : J, η := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ ↦ hb i)
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change m * (δ / m) = δ
        field_simp [hm.ne']
  have hηeq : η = δ / (2 * (Nat.log 2 H + 1) * Fintype.card I) := by
    dsimp [η, m, J, K]
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one]
    ring
  have hcomp := measureReal_compl (μ := μ) ((Set.to_countable (⋃ i : J, bad i)).measurableSet)
  rw [probReal_univ] at hcomp
  have hp : 1 - δ < μ.real (⋃ i : J, bad i)ᶜ := by linarith
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top μ _)
  intro data hd b l h s a
  have hh : data ∈ good (b,l,(h,s,a)) := by
    by_contra hn
    exact hd (Set.mem_iUnion.mpr ⟨(b,l,(h,s,a)), hn⟩)
  dsimp only [good, value] at hh
  rw [hηeq] at hh
  exact hh

/-- The two policies used on the common event. -/
noncomputable def selectorSourceAuxiliaryPolicy {H N : ℕ}
    (sel : Samples State Action H N → ℕ → State → Action) (fixed : ℕ → State → Action)
    (b : Bool) (data : Samples State Action H N) : ℕ → State → Action :=
  if b then fixed else sel data

theorem selectorSourceAuxiliaryContinuation_eq_valueAt {H N : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (sel : Samples State Action H N → ℕ → State → Action) (fixed : ℕ → State → Action)
    (b : Bool) (l : ℕ) (h : Fin H) (data : Samples State Action H N) :
    selectorSourceAuxiliaryContinuation E sel fixed b l h data =
      trueAuxiliaryValueAt (List.ofFn E) (selectorSourceAuxiliaryPolicy sel fixed b data) l
        (h.val + 1) := by
  cases b <;> rfl

/-- Copy of `allLevelBernsteinEvent_implies_residual` for a selected policy. -/
theorem selectorAllLevelBernsteinEvent_implies_residual {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (hH : 0 < H)
    (sel : Samples State Action H N → ℕ → State → Action) (fixed : ℕ → State → Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (data : Samples State Action H N)
    (hevent : SelectorAllLevelBernsteinEvent E N hN sel fixed δ data)
    (b : Bool) (l : ℕ) (hl : l ≤ Nat.log 2 H) :
    auxiliaryResidualCondition (pairedEmpiricalStages E N hN data)
      (selectorSourceAuxiliaryPolicy sel fixed b data) l
      (Real.sqrt (allLevelBeta (H := H) State Action δ / N))
      (allLevelBeta (H := H) State Action δ / N) := by
  apply auxiliaryResidualCondition_of_indexed
  intro i s
  have hi : i.val < H := by simpa only [pairedEmpiricalStages, List.length_ofFn] using i.isLt
  let h : Fin H := ⟨i.val,hi⟩
  let f := selectorSourceAuxiliaryPolicy sel fixed b data
  have hh := hevent b ⟨l, by omega⟩ h s (f i.val s)
  have hη := allLevelConfidence_bounds E hH δ hδ hδ1
  have hw := bernsteinRadius_le_residual_coefficients ((E h).transition s (f i.val s)) N
    (allLevelConfidence (H := H) State Action δ) hη.1 hη.2
    (selectorSourceAuxiliaryContinuation E sel fixed b l h data)
  have hbound := hh.trans hw
  rw [selectorSourceAuxiliaryContinuation_eq_valueAt] at hbound
  dsimp [h, f] at hbound
  simpa only [pairedEmpiricalStages_map_fst, pairedEmpiricalStages, List.getElem_ofFn,
    List.map_ofFn, Function.comp_def, allLevelBeta] using hbound

/-- Copy of `allLevelBernsteinEvent_policyEvaluation` for a selected policy. -/
theorem selectorAllLevelBernsteinEvent_policyEvaluation {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (hH : 0 < H)
    (sel : Samples State Action H N → ℕ → State → Action) (fixed : ℕ → State → Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 12 * (H : ℝ) * allLevelBeta (H := H) State Action δ < N)
    (data : Samples State Action H N)
    (hevent : SelectorAllLevelBernsteinEvent E N hN sel fixed δ data) (b : Bool) (h : ℕ) :
    ‖policyTrajectorySuffix (empiricalStages E N hN data)
        (selectorSourceAuxiliaryPolicy sel fixed b data) h -
      policyTrajectorySuffix (List.ofFn E) (selectorSourceAuxiliaryPolicy sel fixed b data) h‖ ≤
      6 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ)) := by
  have hh := auxiliaryErrorNormAt_le_lemmaNine (pairedEmpiricalStages E N hN data)
    (selectorSourceAuxiliaryPolicy sel fixed b data) H N
    (allLevelBeta (H := H) State Action δ) hH
    (allLevelBeta_nonneg E hH δ hδ hδ1)
    (by simp only [pairedEmpiricalStages, List.length_ofFn]; exact le_rfl) hsize
    (fun l hl ↦ selectorAllLevelBernsteinEvent_implies_residual E N hN hH sel fixed δ hδ hδ1
      data hevent b l hl) h
  rw [pairedEmpiricalStages_map_fst] at hh
  change ‖empiricalAuxiliaryValueAt E N hN data
      (selectorSourceAuxiliaryPolicy sel fixed b data) 0 h -
    trueAuxiliaryValueAt (List.ofFn E) (selectorSourceAuxiliaryPolicy sel fixed b data) 0 h‖ ≤ _
    at hh
  rwa [empiricalAuxiliaryValueAt_zero_eq_policyTrajectorySuffix,
    trueAuxiliaryValueAt_zero_eq_policyTrajectorySuffix] at hh

/-- Copy of `allLevelBernsteinEvent_policyPerformance`; the backward-greedy identity on
the empirical stages is replaced by the empirical optimality of `sel`. -/
theorem selectorAllLevelBernsteinEvent_policyPerformance {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (hH : 0 < H)
    (default : Action) (sel : Samples State Action H N → ℕ → State → Action)
    (hopt : SelectorEmpiricallyOptimal E N hN sel)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 12 * (H : ℝ) * allLevelBeta (H := H) State Action δ < N)
    (data : Samples State Action H N)
    (hevent : SelectorAllLevelBernsteinEvent E N hN sel
      (backwardGreedyActions default (List.ofFn E)) δ data) :
    PolicyPerformanceBound E (sel data)
      (12 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ))) := by
  let f := sel data
  let fixed := backwardGreedyActions default (List.ofFn E)
  let r : ℝ := 6 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hv (h : ℕ) (s : State) :
      0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ∧
      EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ≤ 2 * r := by
    have htrue := selectorAllLevelBernsteinEvent_policyEvaluation E N hN hH sel fixed δ hδ hδ1
      hsize data hevent true h
    have hfit := selectorAllLevelBernsteinEvent_policyEvaluation E N hN hH sel fixed δ hδ hδ1
      hsize data hevent false h
    change ‖policyTrajectorySuffix (empiricalStages E N hN data) fixed h -
      policyTrajectorySuffix (List.ofFn E) fixed h‖ ≤ r at htrue
    change ‖policyTrajectorySuffix (empiricalStages E N hN data) f h -
      policyTrajectorySuffix (List.ofFn E) f h‖ ≤ r at hfit
    have ht := (norm_le_pi_norm (policyTrajectorySuffix (empiricalStages E N hN data) fixed h -
      policyTrajectorySuffix (List.ofFn E) fixed h) s).trans htrue
    have hf := (norm_le_pi_norm (policyTrajectorySuffix (empiricalStages E N hN data) f h -
      policyTrajectorySuffix (List.ofFn E) f h) s).trans hfit
    simp only [Pi.sub_apply, Real.norm_eq_abs] at ht hf
    have hop := policyTrajectorySuffix_le_optimal (empiricalStages E N hN data) fixed h s
    have htrueeq := congrFun (backwardGreedyActions_policyTrajectorySuffix default (List.ofFn E) h) s
    have hfiteq := hopt data h s
    refine ⟨sub_nonneg.mpr (policyTrajectorySuffix_le_optimal _ f h s), ?_⟩
    have htl := (abs_le.mp ht).1
    have hfl := (abs_le.mp hf).2
    change policyTrajectorySuffix (List.ofFn E) fixed h s = _ at htrueeq
    change policyTrajectorySuffix (empiricalStages E N hN data) f h s = _ at hfiteq
    linarith
  intro h
  constructor
  · intro s
    have hh := hv h s
    refine ⟨hh.1, ?_⟩
    calc
      _ ≤ 2 * r := hh.2
      _ = _ := by dsimp [r]; ring
  · intro s a
    have hh := policyTrajectoryQSuffix_loss_le_of_values (List.ofFn E) f (2 * r)
      (mul_nonneg (by norm_num) hr) (fun h s ↦ (hv h s).2) h s a
    refine ⟨hh.1, ?_⟩
    calc
      _ ≤ 2 * r := hh.2
      _ = _ := by dsimp [r]; ring

/-- Copy of `oneStage_causalPolicyPerformance`: with one stage, any empirically optimal
selected policy is exactly optimal in the true model, pathwise. -/
theorem oneStage_selectorPolicyPerformance
    (E : Fin 1 → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (default : Action)
    (sel : Samples State Action 1 N → ℕ → State → Action)
    (hopt : SelectorEmpiricallyOptimal E N hN sel) (data : Samples State Action 1 N) :
    PolicyPerformanceBound E (sel data) 0 := by
  let f := sel data
  let fixed := backwardGreedyActions default (List.ofFn E)
  have hv (h : ℕ) (s : State) :
      0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ∧
      EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ≤ 0 := by
    have hop := policyTrajectorySuffix_le_optimal (empiricalStages E N hN data) fixed h s
    have hetrue := congrFun (oneStage_policyTrajectorySuffix_eq E N hN data fixed h) s
    have hefit := congrFun (oneStage_policyTrajectorySuffix_eq E N hN data f h) s
    have htrue := congrFun (backwardGreedyActions_policyTrajectorySuffix default (List.ofFn E) h) s
    have hfit := hopt data h s
    change policyTrajectorySuffix (List.ofFn E) fixed h s = _ at htrue
    change policyTrajectorySuffix (empiricalStages E N hN data) f h s = _ at hfit
    refine ⟨sub_nonneg.mpr (policyTrajectorySuffix_le_optimal _ f h s), ?_⟩
    linarith
  intro h
  exact ⟨hv h, fun s a ↦ policyTrajectoryQSuffix_loss_le_of_values (List.ofFn E) f 0 le_rfl
    (fun k t ↦ (hv k t).2) h s a⟩

/-- Copy of `mainSample_causalFinitePolicy` for any causal, empirically optimal selected
policy, with the same threshold constant 8640. -/
theorem mainSample_selectorPolicy {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (hH : 0 < H)
    (sel : Samples State Action H N → ℕ → State → Action) (hsel : SelectorFactorsFuture sel)
    (hopt : SelectorEmpiricallyOptimal E N hN sel) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεH : ε ≤ H)
    (hsize : 8640 * (H : ℝ) ^ 3 *
      Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action / δ) / ε ^ 2 ≤ N) :
    1 - δ ≤ (samplingLaw E N).real {data | PolicyPerformanceBound E (sel data) ε} := by
  let default : Action := Classical.choice (E ⟨0, hH⟩).action_nonempty
  by_cases hδ1 : δ < 1
  · by_cases hH1 : H = 1
    · subst H
      have he : {data : Samples State Action 1 N | PolicyPerformanceBound E (sel data) ε} =
          Set.univ := by
        ext data
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact policyPerformanceBound_mono E _ 0 ε hε.le
          (oneStage_selectorPolicyPerformance E N hN default sel hopt data)
      rw [he, probReal_univ]
      linarith
    · have hH2 : 2 ≤ H := by omega
      have hrow : (Fintype.card (Fin H × State × Action) : ℝ) =
          (H : ℝ) * Fintype.card State * Fintype.card Action := by
        simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
        ring
      have hcal := auxiliary_sample_threshold_arithmetic (H : ℝ) (N : ℝ) ε
        (allLevelBeta (H := H) State Action δ)
        (Real.log ((Fintype.card (Fin H × State × Action) : ℝ) / δ))
        (Nat.cast_pos.mpr hH) (Nat.cast_pos.mpr hN) hε hεH
        (allLevelBeta_pos E hH δ hδ hδ1)
        (allLevelBeta_le_source_log E hH2 δ hδ hδ1) (by simpa only [hrow] using hsize)
      have hp := selectorAllLevelBernsteinEvent_probability E N hN hH sel hsel
        (backwardGreedyActions default (List.ofFn E)) δ hδ hδ1
      apply hp.le.trans
      apply measureReal_mono _ (measure_ne_top (samplingLaw E N) _)
      intro data hd
      exact policyPerformanceBound_mono E _ _ ε hcal.2
        (selectorAllLevelBernsteinEvent_policyPerformance E N hN hH default sel hopt δ hδ hδ1
          hcal.1 data hd)
  · have hp : 0 ≤ (samplingLaw E N).real {data | PolicyPerformanceBound E (sel data) ε} :=
      measureReal_nonneg
    linarith

end StatisticalRL.FiniteHorizonGenerative
