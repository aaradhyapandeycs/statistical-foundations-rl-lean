import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Source two-state lower-bound parameter arithmetic. -/
namespace StatisticalRL.GenerativeLowerBound

/-- The source hard-instance self-loop parameter. -/
noncomputable def baseProbability (γ : ℝ) : ℝ := (4 * γ - 1) / (3 * γ)

/-- The source two-point probability increment. -/
noncomputable def probabilityIncrement (γ ε : ℝ) : ℝ :=
  32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2)

/-- Exact source parameter admissibility for the two hard instances. -/
theorem source_parameters_admissible (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) :
    1 / 2 ≤ baseProbability γ ∧
    baseProbability γ < baseProbability γ + probabilityIncrement γ ε ∧
    baseProbability γ + probabilityIncrement γ ε < 1 ∧
    2 * probabilityIncrement γ ε ≤ 1 - baseProbability γ := by
  have hg : 0 < γ := by linarith
  have hh : 0 < 1 - γ := by linarith
  have he : 32 * (1 - γ) * ε < 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 32 * (1 - γ))).1 hεmax
    nlinarith
  dsimp [baseProbability, probabilityIncrement]
  have ha : 0 < 32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2) := by positivity
  have hb : 1 / 2 ≤ (4 * γ - 1) / (3 * γ) := by
    apply (le_div_iff₀ (by positivity : 0 < 3 * γ)).2
    linarith
  have hc : 2 * (32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2)) <
      1 - (4 * γ - 1) / (3 * γ) := by
    field_simp
    nlinarith
  constructor
  · exact hb
  constructor
  · linarith
  constructor
  · linarith
  · exact hc.le

/-- Exact separation of the two scalar Bellman values in the source
construction. This does not itself identify an MDP trajectory value. -/
theorem source_parameters_scalar_separation (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) :
    2 * ε < 1 / (1 - γ * (baseProbability γ + probabilityIncrement γ ε)) -
      1 / (1 - γ * baseProbability γ) := by
  have hg : 0 < γ := by linarith
  have hh : 0 < 1 - γ := by linarith
  have hp := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  have hα : 0 < probabilityIncrement γ ε := by linarith [hp.2.1]
  have hbase : 0 < 1 - γ * baseProbability γ := by
    have hc : baseProbability γ < 1 := by linarith [hp.2.2.1, hp.2.1]
    nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hc.le)]
  have hnext : 0 < 1 - γ * (baseProbability γ + probabilityIncrement γ ε) := by
    nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hp.2.2.1.le)]
  have hscale : 1 - γ * baseProbability γ = 4 * (1 - γ) / 3 := by
    dsimp [baseProbability]
    field_simp
    ring
  have hαeq : probabilityIncrement γ ε =
      2 * (1 - γ * baseProbability γ) ^ 2 * ε / γ ^ 2 := by
    rw [hscale]
    dsimp [probabilityIncrement]
    ring
  have hcomp : γ * (1 - γ * (baseProbability γ + probabilityIncrement γ ε)) <
      1 - γ * baseProbability γ := by
    have hm := mul_nonneg (sub_nonneg.mpr hγ1.le) hnext.le
    have ha := mul_pos hg hα
    nlinarith
  have hmul := mul_pos (sub_pos.mpr hcomp)
    (show 0 < 2 * ε * (1 - γ * baseProbability γ) by positivity)
  have hmain : 2 * ε * ((1 - γ * (baseProbability γ + probabilityIncrement γ ε)) *
      (1 - γ * baseProbability γ)) <
      2 * (1 - γ * baseProbability γ) ^ 2 * ε / γ := by
    apply (lt_div_iff₀ hg).2
    nlinarith
  have hid : 1 / (1 - γ * (baseProbability γ + probabilityIncrement γ ε)) -
      1 / (1 - γ * baseProbability γ) =
      (γ * probabilityIncrement γ ε) /
        ((1 - γ * (baseProbability γ + probabilityIncrement γ ε)) *
         (1 - γ * baseProbability γ)) := by
    field_simp
    ring
  rw [hid]
  apply (lt_div_iff₀ (mul_pos hnext hbase)).2
  nth_rw 2 [hαeq]
  have halg : γ * (2 * (1 - γ * baseProbability γ) ^ 2 * ε / γ ^ 2) =
      2 * (1 - γ * baseProbability γ) ^ 2 * ε / γ := by
    field_simp
  rw [halg]
  exact hmain

/-- The exact ratio and the source universal coefficient used later in the
Bernoulli KL estimate. -/
theorem source_parameters_squared_ratio (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε) :
    probabilityIncrement γ ε ^ 2 / (1 - baseProbability γ) =
      32 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / (27 * γ ^ 3) ∧
    probabilityIncrement γ ε ^ 2 / (1 - baseProbability γ) ≤
      128 * (1 - γ) ^ 3 * ε ^ 2 := by
  have hg : 0 < γ := by linarith
  have hh : 0 < 1 - γ := by linarith
  have heq : 1 - baseProbability γ = (1 - γ) / (3 * γ) := by
    dsimp [baseProbability]
    field_simp
    ring
  have hid : probabilityIncrement γ ε ^ 2 / (1 - baseProbability γ) =
      32 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / (27 * γ ^ 3) := by
    rw [heq]
    dsimp [probabilityIncrement]
    field_simp
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  apply (div_le_iff₀ (by positivity : 0 < 27 * γ ^ 3)).2
  have hg3 : 8 / 27 ≤ γ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) hγ 3
    norm_num at h
    exact h
  have hm := mul_nonneg (sub_nonneg.mpr hg3) (show 0 ≤ (1 - γ) ^ 3 * ε ^ 2 by positivity)
  nlinarith

end StatisticalRL.GenerativeLowerBound
