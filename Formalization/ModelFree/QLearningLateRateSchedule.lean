import Formalization.ModelFree.QLearningWeightTelescope

/-! source Q-learning finite schedule and late cap. -/
namespace StatisticalRL.QLearning

/-- Source equation `eq:thm:infinite-horizaon-eta`, with deterministic rates
and exactly the time range 0≤k≤T. -/
def qSourceRateSchedule (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ) : Prop :=
  ∀ k, k ≤ T →
    1 / (1 + c₁ * (1 - γ) * (T : ℝ) / Real.log (T : ℝ)^3) ≤ η k ∧
      η k ≤ 1 / (1 + c₂ * (1 - γ) * (k : ℝ) / Real.log (T : ℝ)^3)

/-- The exact source late-rate cap. No large-T growth condition beyond T≥2 is
needed for this step. -/
theorem qSourceRate_late_le (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ1 : γ < 1) (hc₂ : 0 < c₂)
    (hs : qSourceRateSchedule γ c₁ c₂ T η) (i : ℕ) (hi : T/2 < i) (hiT : i ≤ T) :
    η i ≤ min 1 (2 * Real.log (T : ℝ)^3 / (c₂ * (1 - γ) * (T : ℝ))) := by
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
  have hgap : 0 < 1-γ := by linarith
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hir : 0 < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hx : 0 < c₂ * (1-γ) * (i : ℝ) / Real.log (T : ℝ)^3 := by positivity
  have hrate := (hs i hiT).2
  have h1 : η i ≤ 1 := by
    apply hrate.trans
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith)).trans_eq (by norm_num)
  have hrecip : 1 / (1 + c₂ * (1-γ) * (i : ℝ) / Real.log (T : ℝ)^3) ≤
      1 / (c₂ * (1-γ) * (i : ℝ) / Real.log (T : ℝ)^3) :=
    one_div_le_one_div_of_le hx (by linarith)
  have hrate' : η i ≤ Real.log (T : ℝ)^3 / (c₂ * (1-γ) * (i : ℝ)) := by
    simpa only [one_div_div] using hrate.trans hrecip
  have htime : (T : ℝ) < 2 * (i : ℝ) := by
    exact_mod_cast (show T < 2*i by omega)
  have hden : 0 < c₂ * (1-γ) * (i : ℝ) := by positivity
  have hdenT : 0 < c₂ * (1-γ) * (T : ℝ) := by positivity
  have h2 : η i ≤ 2 * Real.log (T : ℝ)^3 / (c₂ * (1-γ) * (T : ℝ)) := by
    apply hrate'.trans
    apply (div_le_div_iff₀ hden hdenT).2
    have hm := mul_le_mul_of_nonneg_left htime.le (mul_nonneg hc₂.le hgap.le)
    have hn := mul_le_mul_of_nonneg_left hm (pow_nonneg hlog.le 3)
    nlinarith [hn]
  exact le_min h1 h2

/-- The source schedule also supplies nonnegativity and ≤1 through T. -/
theorem qSourceRate_unit_interval (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ1 : γ < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : qSourceRateSchedule γ c₁ c₂ T η) (i : ℕ) (hiT : i ≤ T) :
    0 ≤ η i ∧ η i ≤ 1 := by
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
  have hgap : 0 < 1-γ := by linarith
  have hlower : 0 ≤ 1 / (1 + c₁ * (1-γ) * (T : ℝ) / Real.log (T : ℝ)^3) := by positivity
  have hx : 0 ≤ c₂ * (1-γ) * (i : ℝ) / Real.log (T : ℝ)^3 := by positivity
  have hupper : 1 ≤ 1 + c₂ * (1-γ) * (i : ℝ) / Real.log (T : ℝ)^3 := by linarith
  exact ⟨hlower.trans (hs i hiT).1,
    (hs i hiT).2.trans ((one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hupper).trans_eq (by norm_num))⟩

/- Combine qSourceRate_late_le and qSourceRate_unit_interval with the compiled
qLate_weight_squares_le for u≤T. This derives the exact source late-weight cap
without assuming the squared budget. The source's theorem assumes γ∈[1/2,1),
T≥2 and c₁≥c₂>0, but this isolated upper bound uses only γ<1, c₁,c₂>0 and T≥2.
Large-T sample-size conditions are needed elsewhere, not in this late-rate step.
No compiler, axiom probe or theorem-level probability claim yet. -/
end StatisticalRL.QLearning
