import Formalization.RobustRL.Ch7.LowerBound75Bounds
import Formalization.RobustRL.Ch7.Ch7PrintedStatements
import Formalization.RobustRL.Ch7.LowerBound73Testing

/-!
# Corrected Theorem 7.5: gap event and assembly

Hard pair `M_j = hardMDP h a_j γ (ℓ(u')) (ℓ(u))`, `μ = δ_{s₀}`, with the parameters of
`Params`. Any policy with `π(a_j|s₀) ≤ 1/2` has χ² robust gap `> ε` in `M_j`
(`chi_gap_event`); the two-point testing bound (`LowerBound73.hard_test_sum`) gives `1/8`.
Constants: `c₃ = 1/512`, `c₄ = 1/5308416`, and every smaller positive pair.
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.LowerBound75

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.EnvironmentStage
  StatisticalRL.RobustRL.Ch7.LowerBound73

section Gap

variable {State Action : Type*} [Fintype State] [Fintype Action] [DecidableEq State]
  [DecidableEq Action]

/-- **Gap event.** In the hard model with good action `g`, every stationary policy putting
mass at most `1/2` on `g` at `s₀` has χ² robust gap `> ε` at `μ = δ_{s₀}`. -/
theorem chi_gap_event {s₀ s₁ : State} (h : s₀ ≠ s₁) (g : Action) {γ σ ε lg lb Tg Tb : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hσ0 : 0 ≤ σ) (hpg : ChiPair σ lg Tg) (hpb : ChiPair σ lb Tb)
    (hTbg : Tb ≤ Tg)
    (hgap : ∀ b, 0 ≤ b → b ≤ Tg - (Tg - Tb) / 2 → ε < ychi γ Tg - ychi γ b)
    (π : StationaryPolicy State Action) (hπ : (π s₀).prob g ≤ 1 / 2) :
    ε < robustOptimalValueAt chiBall (hardMDP h g γ lg lb hγ0 hγ1) σ (pointMass s₀) -
      robustPolicyValueAt chiBall (hardMDP h g γ lg lb hγ0 hγ1) σ π (pointMass s₀) := by
  unfold robustOptimalValueAt robustPolicyValueAt
  rw [expectation_pointMass, expectation_pointMass]
  have hopt := HorizonTrap.robustPolicyValue_le_optimal chiBall
    (hardMDP h g γ lg lb hγ0 hγ1) σ (fun p ↦ QLearning.qChiBall_self p σ hσ0)
    (detPolicy fun _ ↦ g) s₀
  rw [chi_hard_robustPolicyValue h g hγ0 hγ1 hσ0 hpg hpb] at hopt
  rw [chi_hard_robustPolicyValue h g hγ0 hγ1 hσ0 hpg hpb]
  have hdet : (detPolicy (fun _ : State ↦ g) s₀).expectation (ell g Tg Tb) = Tg := by
    simp [detPolicy, ell]
  rw [hdet] at hopt
  rw [expectation_ell]
  have hπ0 := (π s₀).prob_nonneg g
  have hD : 0 ≤ Tg - Tb := by linarith
  have hb0 : 0 ≤ Tb + (π s₀).prob g * (Tg - Tb) := by
    have := mul_nonneg hπ0 hD; linarith [hpb.nonneg]
  have hb : Tb + (π s₀).prob g * (Tg - Tb) ≤ Tg - (Tg - Tb) / 2 := by
    have : (π s₀).prob g * (Tg - Tb) ≤ 1 / 2 * (Tg - Tb) := mul_le_mul_of_nonneg_right hπ hD
    linarith
  have := hgap _ hb0 hb
  linarith

end Gap

local instance lowerBound75LowerBoundStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- Body of the conclusion of Theorem 7.5 (χ² balls), with the shared-reward clause. -/
def KRConclusion (State Action : Type) [Fintype State] [Fintype Action] (γ σ ε : ℝ) (N : ℕ) :
    Prop :=
  ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
    M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
    ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
      1 / 8 ≤ max
        ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
          {data | ε < robustOptimalValueAt chiBall M₀ σ μ -
            robustPolicyValueAt chiBall M₀ σ (est data) μ})
        ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
          {data | ε < robustOptimalValueAt chiBall M₁ σ μ -
            robustPolicyValueAt chiBall M₁ σ (est data) μ})

/-- **Core case** (`S ≥ 2`, `A ≥ 2`, `ε > 0`) at the explicit constants `c₃ = 1/512`,
`c₄ = 1/5308416`; the two hard models share their reward. -/
theorem core_explicit (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ) (hS : 2 ≤ Fintype.card State)
    (hA : 2 ≤ Fintype.card Action) (hε : 0 < ε) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hσ : 0 < σ)
    (hεle : ε ≤ 1 / 512 / (1 - γ))
    (hN : (N : ℝ) ≤ 1 / 5308416 / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ))) :
    KRConclusion State Action γ σ ε N := by
  classical
  obtain ⟨s₀, s₁, hs⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card State)
  obtain ⟨a₀, a₁, ha⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Action)
  have hγ0 : 0 ≤ γ := by linarith
  have hh0 : 0 < 1 - γ := by linarith
  have hh1 : 1 - γ ≤ 1 / 4 := by linarith
  have hhε : (1 - γ) * ε ≤ 1 / 512 := by
    rw [le_div_iff₀ hh0] at hεle; linarith
  obtain ⟨hs0, hs2, hu, hsu, hd⟩ := uf_spec (h := 1 - γ) hσ.le hh0
  set s := Real.sqrt σ with hsdef
  set u := uf σ (1 - γ) with hudef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN' : (N : ℝ) * ((1 - γ) ^ 4 * ε ^ 2) ≤ 1 / 5308416 * ((1 - γ) + s ^ 2) := by
    have := mul_le_mul_of_nonneg_right hN (by positivity : (0 : ℝ) ≤ (1 - γ) ^ 4 * ε ^ 2)
    have e : 1 / 5308416 / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) *
        ((1 - γ) ^ 4 * ε ^ 2) = 1 / 5308416 * ((1 - γ) + σ) := by
      field_simp
    rw [e] at this
    rw [hs2]; exact this
  have hδ := df_pos hs0 hu hsu hh0 hε
  have hδu := df_le hs0 hu hsu hd hh0 hh1 hε hhε
  have hdiff := tdiff_lower hs0 hu hsu hd hh0 hh1 hε hhε
  have htg := tg_le hs0 hu hsu hd hh0 hh1 hε hhε
  have hNb := test_budget hs0 hu hsu hd hh0 hh1 hε hhε hN0 hN'
  set δ := df s u (1 - γ) ε with hδdef
  have hpg : ChiPair σ (ellf (u + δ)) (tf s (u + δ)) := chiPair_of hs0 hs2 (by linarith)
    (by linarith)
  have hpb : ChiPair σ (ellf u) (tf s u) := chiPair_of hs0 hs2 hu hsu
  have hlbg : ellf u ≤ ellf (u + δ) := by
    have := ellf_diff (u := u) δ
    have : 0 ≤ δ * (2 * u + δ) / ((1 + u ^ 2) * (1 + (u + δ) ^ 2)) := by positivity
    linarith
  have hTbg : tf s u ≤ tf s (u + δ) := by
    have : 0 ≤ 32 * (1 - γ) ^ 2 * ε := by positivity
    linarith
  have hgap : ∀ b, 0 ≤ b → b ≤ tf s (u + δ) - (tf s (u + δ) - tf s u) / 2 →
      ε < ychi γ (tf s (u + δ)) - ychi γ b := by
    intro b hb0 hb
    exact chi_gap_gt hγ hγ1 hε hb0 hb hdiff htg
  set lg := ellf (u + δ) with hlg
  set lb := ellf u with hlb
  refine ⟨hardMDP hs a₀ γ lg lb hγ0 hγ1, hardMDP hs a₁ γ lg lb hγ0 hγ1, pointMass s₀,
    rfl, rfl, rfl, ?_⟩
  intro est
  let test : ModelBasedPolicyLearning.Samples State Action N → Bool :=
    fun data ↦ decide (1 / 2 < (est data s₀).prob a₀)
  set E₀ := {data | ε < robustOptimalValueAt chiBall (hardMDP hs a₀ γ lg lb hγ0 hγ1) σ
        (pointMass s₀) - robustPolicyValueAt chiBall
          (hardMDP hs a₀ γ lg lb hγ0 hγ1) σ (est data) (pointMass s₀)} with hE₀
  set E₁ := {data | ε < robustOptimalValueAt chiBall (hardMDP hs a₁ γ lg lb hγ0 hγ1) σ
        (pointMass s₀) - robustPolicyValueAt chiBall
          (hardMDP hs a₁ γ lg lb hγ0 hγ1) σ (est data) (pointMass s₀)} with hE₁
  have hsum := hard_test_sum hs hγ0 hγ1 (a₀ := a₀) (a₁ := a₁) ha hpb.pos hlbg hpg.lt_one N hNb
    E₀ E₁ test ?_ ?_
  · have h₀ := le_max_left
      ((ModelBasedPolicyLearning.samplingLaw (hardMDP hs a₀ γ lg lb hγ0 hγ1) N).real E₀)
      ((ModelBasedPolicyLearning.samplingLaw (hardMDP hs a₁ γ lg lb hγ0 hγ1) N).real E₁)
    have h₁ := le_max_right
      ((ModelBasedPolicyLearning.samplingLaw (hardMDP hs a₀ γ lg lb hγ0 hγ1) N).real E₀)
      ((ModelBasedPolicyLearning.samplingLaw (hardMDP hs a₁ γ lg lb hγ0 hγ1) N).real E₁)
    linarith
  · intro data hdata
    simp only [Set.mem_setOf_eq, test, decide_eq_false_iff_not, not_lt] at hdata
    exact chi_gap_event hs a₀ hγ0 hγ1 hσ.le hpg hpb hTbg hgap (est data) hdata
  · intro data hdata
    simp only [Set.mem_setOf_eq, test, decide_eq_true_eq] at hdata
    have hsum1 : (est data s₀).prob a₀ + (est data s₀).prob a₁ ≤ 1 := by
      have h := (est data s₀).sum_prob
      have := Finset.add_le_sum (f := (est data s₀).prob)
        (fun i _ ↦ (est data s₀).prob_nonneg i) (Finset.mem_univ a₀) (Finset.mem_univ a₁) ha
      linarith
    exact chi_gap_event hs a₁ hγ0 hγ1 hσ.le hpg hpb hTbg hgap (est data) (by linarith)

end StatisticalRL.RobustRL.Ch7.LowerBound75
