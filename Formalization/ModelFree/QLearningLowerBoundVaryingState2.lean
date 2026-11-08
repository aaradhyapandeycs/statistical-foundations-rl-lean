import Formalization.ModelFree.QLearningLowerBoundVaryingPathwise

/-!
# Mean of the state-2 chain with a learning-rate schedule

Time-varying form of `eq:EV2` (`chapters/generative_model_model_free.tex:3010–3021`):
`V⋆(2) - E v_t = Π_{1-γp}(0,t) V⋆(2)` with `Π_x(0,t) = ∏_{j ≤ t} (1 - x η_j)`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

theorem qLbvChain2_congr (γ : ℝ) (η : ℕ → ℝ) (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ)
    (h : qLbAgree2 s s' n) (t : ℕ) (ht : t ≤ n) :
    qLbvChain2 γ η s t = qLbvChain2 γ η s' t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [qLbvChain2, qLbStay, ih (by omega), h (t + 1) (by omega) ht]

/-- `V⋆(2) - E v_t = Π_{1-γp}(0,t) V⋆(2)` for `t ≤ N`. -/
theorem qLbv_state2_mean (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (N : ℕ) (η : ℕ → ℝ)
    (t : ℕ) (ht : t ≤ N) :
    1 / (1 - γ * qHardP γ) -
        ∫ d, qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t
          ∂qSamplingLaw (qLbMDP γ hγ hγ1) N =
      qLbvProd η (1 - γ * qHardP γ) 0 t * (1 / (1 - γ * qHardP γ)) := by
  have hden : 1 - γ * qHardP γ ≠ 0 := by
    rw [qLb_one_sub_gamma_p γ hγ]
    intro h; linarith
  induction t with
  | zero => simp [qLbvChain2, qLbvProd_self]
  | succ t ih =>
    have ih' := ih (by omega)
    have hpt : ∀ d : QSamples (Fin 4) Bool N,
        qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) (t + 1) =
          (1 - η (t + 1)) * qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t + η (t + 1) +
            (η (t + 1) * γ) * (qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t *
              qLbInd2 (qSamplesExtend (qLbMDP γ hγ hγ1) N d (t + 1) 2 false)) := by
      intro d; simp only [qLbvChain2, qLbStay, qLbInd2]; ring
    simp_rw [hpt]
    rw [integral_add (qSampling_integrable _ N _) (qSampling_integrable _ N _),
      integral_add (qSampling_integrable _ N _) (integrable_const _), integral_const_mul,
      integral_const_mul,
      qLb_integral_mul_state2 γ hγ hγ1 N t _
        (fun d d' h ↦ qLbvChain2_congr γ η _ _ t h t le_rfl) qLbInd2,
      qLb_integral_state2 γ hγ hγ1 N (t + 1) (by omega) ht qLbInd2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, qLbInd2]
    simp only [show ¬((0 : Fin 4) = 2) by decide, ↓reduceIte]
    rw [qLbvProd_succ η _ 0 t (Nat.zero_le t)]
    set m := ∫ d, qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t
      ∂qSamplingLaw (qLbMDP γ hγ hγ1) N
    have e : 1 / (1 - γ * qHardP γ) - m = qLbvProd η (1 - γ * qHardP γ) 0 t *
        (1 / (1 - γ * qHardP γ)) := ih'
    field_simp at e ⊢
    linear_combination (1 - (1 - γ * qHardP γ) * η (t + 1)) * e

end StatisticalRL.QLearning
