import Formalization.Generative.FiniteHorizonAllLevelBernstein
import Formalization.Generative.FiniteHorizonLemmaNine

/-! Indexed common-event to actual recursive residual bridge, with exact
same-data trajectory semantics. No final confidence/log absorption is asserted. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance residualBridgeStateMeasurable : MeasurableSpace State := ⊤

theorem trueAuxiliaryValueAt_cons_succ (E : EnvironmentStage State Action)
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action) (l n : ℕ) :
    trueAuxiliaryValueAt (E :: es) f l (n + 1) =
      trueAuxiliaryValueAt es (fun k ↦ f (k + 1)) l n := by
  unfold trueAuxiliaryValueAt
  rw [List.drop_succ_cons]
  congr 1
  funext k
  congr 1
  omega

/-- Indexed one-step bounds imply the exact recursive condition used by Lemma 9.
Both sides use the same actual true suffix and the same shifted policy. -/
theorem auxiliaryResidualCondition_of_indexed
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (a b : ℝ)
    (hres : ∀ (h : Fin pairs.length) (s : State),
      let V := trueAuxiliaryValueAt (pairs.map Prod.fst) f l (h.val + 1)
      |policyRowResidual (pairs[h.val]).1 (pairs[h.val]).2 V s (f h.val s)| ≤
        a * Real.sqrt (((pairs[h.val]).1.transition s (f h.val s)).variance V) + b * ‖V‖) :
    auxiliaryResidualCondition pairs f l a b := by
  induction pairs generalizing f with
  | nil => trivial
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    constructor
    · intro s
      have hh := hres ⟨0, by simp⟩ s
      simpa only [List.getElem_cons_zero, List.map_cons, trueAuxiliaryValueAt,
        List.drop_succ_cons, List.drop_zero, Nat.zero_add, auxiliaryPolicyReward,
        Nat.add_comm] using hh
    · apply ih (fun k ↦ f (k + 1))
      intro h s
      have hh := hres ⟨h.val + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ h.isLt⟩ s
      simpa only [List.getElem_cons_succ, List.map_cons, trueAuxiliaryValueAt_cons_succ] using hh

/-- A direct coefficient weakening of the reviewed Bernstein radius. -/
theorem bernsteinRadius_le_residual_coefficients (d : FiniteDistribution State)
    (N : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) (V : State → ℝ) :
    FiniteDistribution.bernsteinRadius d N 1 η V ≤
      Real.sqrt ((2 * Real.log (4 / η)) / N) * Real.sqrt (d.variance V) +
        ((2 * Real.log (4 / η)) / N) * ‖V‖ := by
  rw [FiniteDistribution.bernsteinRadius_eq_source]
  norm_num only [Nat.cast_one, mul_one]
  have hlog : 0 ≤ Real.log (4 / η) := Real.log_nonneg ((le_div_iff₀ hη).2 (by linarith))
  apply add_le_add le_rfl
  have he : 2 * ‖V‖ * Real.log (4 / η) / (3 * N) =
      (((2 * Real.log (4 / η)) / N) * ‖V‖) / 3 := by ring
  rw [he]
  exact div_le_self (by positivity) (by norm_num)

noncomputable def allLevelConfidence {H : ℕ} (State Action : Type*) [Fintype State] [Fintype Action]
    (δ : ℝ) : ℝ := δ / (2 * (Nat.log 2 H + 1) * Fintype.card (Fin H × State × Action))

noncomputable def allLevelBeta {H : ℕ} (State Action : Type*) [Fintype State] [Fintype Action]
    (δ : ℝ) : ℝ := 2 * Real.log (4 / allLevelConfidence (H := H) State Action δ)

/-- The exact rowwise common event, before selected current actions are substituted. -/
def AllLevelBernsteinEvent {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (fixed : ℕ → State → Action) (δ : ℝ) (data : Samples State Action H N) : Prop :=
  ∀ (b : Bool) (l : Fin (Nat.log 2 H + 1)) (h : Fin H) (s : State) (a : Action),
    |policyRowResidual (E h) (empiricalStage E N hN data h)
      (sourceAuxiliaryContinuation E N hN fallback fixed b l.val h data) s a| ≤
    FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1
      (allLevelConfidence (H := H) State Action δ)
      (sourceAuxiliaryContinuation E N hN fallback fixed b l.val h data)

theorem allLevelBernsteinEvent_probability {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (hH : 0 < H) (fallback : Action) (fixed : ℕ → State → Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw E N).real {data | AllLevelBernsteinEvent E N hN fallback fixed δ data} := by
  exact simultaneous_sourceAuxiliaryContinuation_bernstein E N hN hH fallback fixed δ hδ hδ1

/-- The two policies used on the common event remain separate after selection. -/
noncomputable def sourceAuxiliaryPolicy {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (fixed : ℕ → State → Action) (b : Bool)
    (data : Samples State Action H N) : ℕ → State → Action :=
  if b then fixed else backwardGreedyActions fallback (empiricalStages E N hN data)

theorem sourceAuxiliaryContinuation_eq_valueAt {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (fixed : ℕ → State → Action) (b : Bool) (l : ℕ) (h : Fin H)
    (data : Samples State Action H N) :
    sourceAuxiliaryContinuation E N hN fallback fixed b l h data =
      trueAuxiliaryValueAt (List.ofFn E) (sourceAuxiliaryPolicy E N hN fallback fixed b data) l (h.val + 1) := by
  cases b <;> rfl

theorem allLevelConfidence_bounds {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < allLevelConfidence (H := H) State Action δ ∧
      allLevelConfidence (H := H) State Action δ < 1 := by
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  have hc : 1 ≤ (Fintype.card (Fin H × State × Action) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hK : (1 : ℝ) ≤ (Nat.log 2 H : ℝ) + 1 := by have hh := Nat.cast_nonneg (α := ℝ) (Nat.log 2 H); linarith
  have hprod : (1 : ℝ) ≤ ((Nat.log 2 H : ℝ) + 1) * Fintype.card (Fin H × State × Action) := by
    simpa only [one_mul] using mul_le_mul hK hc (by norm_num) (by positivity)
  have hden : 0 < 2 * ((Nat.log 2 H : ℝ) + 1) * (Fintype.card (Fin H × State × Action) : ℝ) := by
    nlinarith
  unfold allLevelConfidence
  constructor
  · exact div_pos hδ hden
  · exact (div_lt_iff₀ hden).2 (by nlinarith)

theorem allLevelBeta_nonneg {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ allLevelBeta (H := H) State Action δ := by
  have he := allLevelConfidence_bounds E hH δ hδ hδ1
  exact mul_nonneg (by norm_num) (Real.log_nonneg ((le_div_iff₀ he.1).2 (by linarith)))

theorem pairedEmpiricalStages_map_fst {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action H N) :
    (pairedEmpiricalStages E N hN data).map Prod.fst = List.ofFn E := by
  simp only [pairedEmpiricalStages, List.map_ofFn, Function.comp_def]

theorem pairedEmpiricalStages_map_snd {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action H N) :
    (pairedEmpiricalStages E N hN data).map Prod.snd = empiricalStages E N hN data := by
  simp only [pairedEmpiricalStages, List.map_ofFn, Function.comp_def, empiricalStages]

/-- A single common indexed event supplies the actual recursive condition for
both policies, after substituting their possibly data-selected current actions. -/
theorem allLevelBernsteinEvent_implies_residual {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (hH : 0 < H) (fallback : Action) (fixed : ℕ → State → Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (data : Samples State Action H N)
    (hevent : AllLevelBernsteinEvent E N hN fallback fixed δ data)
    (b : Bool) (l : ℕ) (hl : l ≤ Nat.log 2 H) :
    auxiliaryResidualCondition (pairedEmpiricalStages E N hN data)
      (sourceAuxiliaryPolicy E N hN fallback fixed b data) l
      (Real.sqrt (allLevelBeta (H := H) State Action δ / N))
      (allLevelBeta (H := H) State Action δ / N) := by
  apply auxiliaryResidualCondition_of_indexed
  intro i s
  have hi : i.val < H := by simpa only [pairedEmpiricalStages, List.length_ofFn] using i.isLt
  let h : Fin H := ⟨i.val,hi⟩
  let f := sourceAuxiliaryPolicy E N hN fallback fixed b data
  have hh := hevent b ⟨l, by omega⟩ h s (f i.val s)
  have hη := allLevelConfidence_bounds E hH δ hδ hδ1
  have hw := bernsteinRadius_le_residual_coefficients ((E h).transition s (f i.val s)) N
    (allLevelConfidence (H := H) State Action δ) hη.1 hη.2
    (sourceAuxiliaryContinuation E N hN fallback fixed b l h data)
  have hbound := hh.trans hw
  rw [sourceAuxiliaryContinuation_eq_valueAt] at hbound
  dsimp [h, f] at hbound
  simpa only [pairedEmpiricalStages_map_fst, pairedEmpiricalStages, List.getElem_ofFn,
    List.map_ofFn, Function.comp_def, allLevelBeta] using hbound

end StatisticalRL.FiniteHorizonGenerative
