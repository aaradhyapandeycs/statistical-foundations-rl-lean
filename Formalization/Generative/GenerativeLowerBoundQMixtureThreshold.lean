import Formalization.Generative.GenerativeLowerBoundQMixtureChiIntegral

/-! Source-parameter and cardinality arithmetic for sparse-mixture testing. -/
namespace StatisticalRL.GenerativeLowerBound

/-- The one-coordinate Bernoulli χ² factor has the source H⁻³ scale. -/
theorem qMixture_source_chi_factor_bound (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεmax : ε < 1 / (32 * (1 - γ))) :
    (probabilityIncrement γ ε) ^ 2 /
      (baseProbability γ * (1 - baseProbability γ)) ≤
        256 * (1 - γ) ^ 3 * ε ^ 2 := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  have hg : 0 < γ := by linarith
  have hh : 0 < 1 - γ := by linarith
  have hp : 0 < baseProbability γ := by linarith [ha.1]
  have hp1 : 0 < 1 - baseProbability γ := by linarith [ha.2.1, ha.2.2.1]
  have hbase : 1 - baseProbability γ = (1 - γ) / (3 * γ) := by
    unfold baseProbability
    field_simp
    ring
  have hγcube : (8 : ℝ) / 27 ≤ γ ^ 3 := by nlinarith [sq_nonneg (γ - 2 / 3)]
  rw [hbase]
  unfold probabilityIncrement
  apply (div_le_iff₀ (mul_pos hp (div_pos hh (by positivity)))).2
  field_simp
  nlinarith [sq_nonneg ε, sq_nonneg (1 - γ), sq_nonneg ((1 - γ) * ε)]

/-- Exact alternative count K=m*A supports log(SA) up to a factor two. -/
theorem qMixture_log_card_lower (m A : ℕ) (hm : 1 ≤ m) (hA : 2 ≤ A) :
    Real.log (((m + 1) * A : ℕ) : ℝ) ≤ 2 * Real.log ((m * A + 1 : ℕ) : ℝ) := by
  have hS : (((m + 1) * A : ℕ) : ℝ) ≤ ((m * A + 1 : ℕ) : ℝ) ^ 2 := by
    have hmA : A ≤ m * A := by nlinarith [Nat.mul_le_mul_right A hm]
    have hnat : (m + 1) * A ≤ (m * A + 1) ^ 2 := by
      nlinarith [Nat.zero_le ((m * A) ^ 2)]
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < (((m + 1) * A : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log hpos hS
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

end StatisticalRL.GenerativeLowerBound
