import Formalization.ModelFree.QLearningLowerBoundAuxMoments
import Formalization.ModelFree.QLearningLowerBoundXi
import Formalization.ModelFree.QLearningLowerBoundRescaledTheorem

/-! Small facts read from Theorems 4.6 and 4.7 and from Remark 4.5
(`chapters/generative_model_model_free.tex:945–953`, `:992–1000`, `:3455–3457`). -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-! ### Constant learning rate in Theorem 4.6 -/

/-- The constant rate `η = 1/(1 + c₁(1−γ)T/log³T)` lies in the schedule window at every
`k ≤ T`, and under the iteration condition it is at most `(1−γ)³ε²/(c₁c₃ log T log(SAT/δ))`. -/
theorem constantRate_schedule_and_bound (c₁ c₂ c₃ γ ε δ : ℝ) (S A T : ℕ) (hc₂ : 0 < c₂)
    (hc₂₁ : c₂ ≤ c₁) (hc₃ : 0 < c₃) (hγ1 : γ < 1) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T) :
    (∀ k : ℕ, k ≤ T →
      1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 3) ≤
        1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 3) ∧
      1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 3) ≤
        1 / (1 + c₂ * (1 - γ) * k / Real.log (T : ℝ) ^ 3)) ∧
    (c₃ * Real.log (T : ℝ) ^ 4 * Real.log ((S : ℝ) * A * T / δ) / ((1 - γ) ^ 4 * ε ^ 2) ≤ T →
      1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 3) ≤
        (1 - γ) ^ 3 * ε ^ 2 / (c₁ * c₃ * Real.log (T : ℝ) * Real.log ((S : ℝ) * A * T / δ))) := by
  have hh : 0 < 1 - γ := sub_pos.mpr hγ1
  have hc₁ : 0 < c₁ := hc₂.trans_le hc₂₁
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hL : 0 < Real.log (T : ℝ) := Real.log_pos (by linarith)
  have hL3 : 0 < Real.log (T : ℝ) ^ 3 := by positivity
  refine ⟨fun k hk ↦ ⟨le_rfl, ?_⟩, fun hthr ↦ ?_⟩
  · have hkT : (k : ℝ) ≤ T := by exact_mod_cast hk
    have hnum : c₂ * (1 - γ) * k ≤ c₁ * (1 - γ) * T := by
      have h1 : c₂ * k ≤ c₁ * T :=
        mul_le_mul hc₂₁ hkT (Nat.cast_nonneg k) hc₁.le
      nlinarith
    apply one_div_le_one_div_of_le (by positivity)
    have := div_le_div_of_nonneg_right hnum hL3.le
    linarith
  · have hSAT : (1 : ℝ) < (S : ℝ) * A * T / δ := by
      have hS' : (1 : ℝ) ≤ S := by exact_mod_cast hS
      have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
      rw [lt_div_iff₀ hδ]
      have : (1 : ℝ) ≤ (S : ℝ) * A := one_le_mul_of_one_le_of_one_le hS' hA'
      nlinarith
    have hℓ : 0 < Real.log ((S : ℝ) * A * T / δ) := Real.log_pos hSAT
    set L := Real.log (T : ℝ)
    set ℓ := Real.log ((S : ℝ) * A * T / δ)
    have hTpos : (0 : ℝ) < T := by linarith
    -- η ≤ L³/(c₁(1−γ)T)
    have hη : 1 / (1 + c₁ * (1 - γ) * T / L ^ 3) ≤ L ^ 3 / (c₁ * (1 - γ) * T) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ L ^ 3 := hL3.le
      rw [one_mul, mul_add, mul_one, mul_div_cancel₀ _ hL3.ne']
      linarith
    refine hη.trans ?_
    rw [div_le_iff₀ (by positivity)] at hthr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- L³ · (c₁c₃ L ℓ) ≤ (1−γ)³ε² · c₁(1−γ)T  ⇐  c₃ L⁴ ℓ ≤ T (1−γ)⁴ ε²
    have key : c₃ * L ^ 4 * ℓ ≤ T * ((1 - γ) ^ 4 * ε ^ 2) := hthr
    have := mul_le_mul_of_nonneg_left key hc₁.le
    nlinarith [this]

/-! ### Iteration lower bound read from Theorem 4.7 -/

/-- Contrapositive form of Theorem 4.7: mean-square accuracy `ε²` at every state forces
`T log² T ≥ c_lb/((1−γ)⁴ε²)`. The regime constant is raised to `max c₃ 1` so that
`T ≥ 16` and `log T > 0`. -/
theorem qLb_thm47_iterationLowerBound : ∃ c₃ c_lb : ℝ, 0 < c₃ ∧ 0 < c_lb ∧
    ∀ γ : ℝ, 3 / 4 ≤ γ → γ < 1 → ∀ T : ℕ, c₃ / (1 - γ) ^ 2 ≤ T →
    ∀ η : ℕ → ℝ,
      ((∃ cη : ℝ, 0 < cη ∧ ∀ t : ℕ, η t = 1 / (1 + cη * (1 - γ) * t)) ∨
        (∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧ ∀ t : ℕ, η t = η₀)) →
      ∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ ∧
        ∀ ε : ℝ, 0 < ε →
          (∀ s, ∫ d, (qLearningValue M (qSampledIterate M η T (fun _ _ ↦ 0) d) s -
              M.trajectoryExpectedValue M.optimalGreedyPolicy s) ^ 2 ∂qSamplingLaw M T ≤
            ε ^ 2) →
          c_lb / ((1 - γ) ^ 4 * ε ^ 2) ≤ T * Real.log T ^ 2 := by
  obtain ⟨c₃, c_lb, hc₃, hclb, hmain⟩ := qLb_thm47
  refine ⟨max c₃ 1, c_lb, lt_max_of_lt_right one_pos, hclb, ?_⟩
  intro γ hγ hγ1 T hT η hη
  have hh : 0 < 1 - γ := by linarith
  have hg2 : 0 < (1 - γ) ^ 2 := by positivity
  have hT3 : c₃ / (1 - γ) ^ 2 ≤ T :=
    le_trans (div_le_div_of_nonneg_right (le_max_left _ _) hg2.le) hT
  have hT1 : 1 / (1 - γ) ^ 2 ≤ T :=
    le_trans (div_le_div_of_nonneg_right (le_max_right _ _) hg2.le) hT
  have hT16 : (16 : ℝ) ≤ T := by
    have hsm : (1 - γ) ^ 2 ≤ 1 / 16 := by nlinarith
    have : (16 : ℝ) ≤ 1 / (1 - γ) ^ 2 := by
      rw [le_div_iff₀ hg2]; linarith
    linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  obtain ⟨M, hMγ, s, hs⟩ := hmain γ hγ hγ1 T hT3 η hη
  refine ⟨M, hMγ, fun ε hε hacc ↦ ?_⟩
  have hle := hs.trans (hacc s)
  have hden : 0 < (1 - γ) ^ 4 * T * Real.log T ^ 2 := by positivity
  rw [div_le_iff₀ hden] at hle
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hle]

/-! ### Remark 4.5: mean-zero noise for adapted value processes -/

/-- `E[∑_{k=1}^t η(1−η)^{t−k} γ (P_k(1∣1,a) − p) W_{k−1}] = 0` for every value process `W`
whose value at time `n` depends only on the state-1 draws at times `1, …, n`. -/
theorem qLb_integral_xi_adapted (M : DiscountedMDP (Fin 4) Bool) (N : ℕ) (γ η : ℝ)
    (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) (a : Bool)
    (W : ℕ → (ℕ → Fin 4 → Bool → Fin 4) → ℝ)
    (hW : ∀ n s s', qLbAgree1 s s' n → W n s = W n s') :
    ∫ d, ∑ k ∈ Finset.Icc 1 t, η * (1 - η) ^ (t - k) * γ *
        (qLbStay (qSamplesExtend M N d) 1 k a - qHardP γ) * W (k - 1) (qSamplesExtend M N d)
      ∂qSamplingLaw M N = 0 := by
  rw [integral_finset_sum _ (fun k _ ↦ qSampling_integrable M N _)]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hk1, hkt⟩ := Finset.mem_Icc.mp hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hpt : ∀ d : QSamples (Fin 4) Bool N,
      η * (1 - η) ^ (t - (n + 1)) * γ * (qLbStay (qSamplesExtend M N d) 1 (n + 1) a - qHardP γ) *
        W (n + 1 - 1) (qSamplesExtend M N d) =
      (η * (1 - η) ^ (t - (n + 1)) * γ) * (W n (qSamplesExtend M N d) *
        (qLbStay (qSamplesExtend M N d) 1 (n + 1) a - qHardP γ)) := by
    intro d; simp only [Nat.add_sub_cancel]; ring
  simp_rw [hpt]
  rw [integral_const_mul, qLb_integral_mul_centered M N γ hrow n (by omega)
    (fun d ↦ W n (qSamplesExtend M N d)) (fun d d' h ↦ hW n _ _ h) a, mul_zero]

/-- The single-action auxiliary recursion `Q̂_0 = 1/(1−γp)`,
`Q̂_{k+1} = (1−η)Q̂_k + η(1 + γ P_{k+1}(1∣1,a) Q̂_k)`. -/
noncomputable def qLbSingleAuxIterate (γ η : ℝ) (a : Bool)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ) : ℝ :=
  Nat.rec (1 / (1 - γ * qHardP γ))
    (fun k q ↦ (1 - η) * q + η * (1 + γ * qLbStay samples 1 (k + 1) a * q)) n

/-- The single-action recursion is adapted to the state-1 draws. -/
theorem qLbSingleAuxIterate_congr (γ η : ℝ) (a : Bool) (n : ℕ)
    (s s' : ℕ → Fin 4 → Bool → Fin 4) (h : qLbAgree1 s s' n) :
    qLbSingleAuxIterate γ η a s n = qLbSingleAuxIterate γ η a s' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h' : qLbAgree1 s s' n := fun k hk1 hk b ↦ h k hk1 (by omega) b
    have hstay : qLbStay s 1 (n + 1) a = qLbStay s' 1 (n + 1) a := by
      unfold qLbStay; rw [h (n + 1) (by omega) le_rfl a]
    change (1 - η) * qLbSingleAuxIterate γ η a s n +
        η * (1 + γ * qLbStay s 1 (n + 1) a * qLbSingleAuxIterate γ η a s n) =
      (1 - η) * qLbSingleAuxIterate γ η a s' n +
        η * (1 + γ * qLbStay s' 1 (n + 1) a * qLbSingleAuxIterate γ η a s' n)
    rw [ih h', hstay]

end StatisticalRL.QLearning
