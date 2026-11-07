import Formalization.Ch7Rest.FedGeneric710
import Formalization.Probability.EmpiricalRow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Theorem 7.10 under the reading "universal `c₀` first" (SOURCE-ISSUES C42)

Source: `chapters/federated_RL.tex`, Theorem 7.10 (`thm:lower_bound`) :227–239, generic
Algorithm `alg:general_fed_alg_with_inter_comm` :166–220 (box :200–220).

The communication hypothesis is very restrictive. The schedule contains `T`
(`t_{C_round} = T`, :196), so `C_round ≥ 1`, and `C_round ≤ c₀ / ((1-γ) log² N)` forces
`log² N ≤ c₀ / (1-γ)`. Hence `T ≤ N ≤ N_max := ⌊exp √(c₀/(1-γ))⌋`. On the instance with reward
`r ≡ 1` (any transitions; here uniform) every agent's iterate is deterministic and constant in
`(s,a)`, with error `e_t = (1 - η_t (1-γ)) e_{t-1}`, `e_0 = 1/(1-γ)`. Since `η_t ≤ 1`,
`e_T ≥ γ^T / (1-γ) ≥ γ^{N_max} / (1-γ)`. Because `√N log³ N ≥ 1` for `N ≥ 16`, the printed
bound holds with `C_γ = γ^{N_max} / (1-γ)` (`lbConst c₀ γ`), which is doubly exponentially
small in `√(c₀/(1-γ))`. This does not establish the discussion at :242–248 (a communication
requirement polynomial in `1/(1-γ)`); see `docs/SOURCE-ISSUES.md#C42`.

The export `lowerBound_of_fewRounds` assumes less than the printed theorem: any `c₀` (no
positivity), `γ ∈ (0,1)`, `S, A ≥ 1`, any learning rates in `[0,1]`, `K ≥ 1`, and no condition
`T ≥ 1/(1-γ)` or `𝒞 ⊆ {1,…,T}`; the instance is chosen before `K`.
-/

open MeasureTheory

namespace StatisticalRL.Ch7Rest.FedGeneric

open StatisticalRL.Ch7Rest.Fed (greedyValue)

variable {State Action : Type} [Fintype State] [Fintype Action]

local instance fedLowerBoundStateMeasurable : MeasurableSpace State := ⊤

instance fedSamplingLaw_isProbabilityMeasure (M : DiscountedMDP State Action) (T K B : ℕ) :
    IsProbabilityMeasure (fedSamplingLaw M T K B) := by
  unfold fedSamplingLaw
  infer_instance

/-- The instance with reward `r ≡ 1`, uniform transitions, and discount `γ`. -/
noncomputable def onesMDP [Nonempty State] [Nonempty Action] (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) : DiscountedMDP State Action where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition := fun _ _ ↦
    ⟨fun _ ↦ 1 / (Fintype.card State : ℝ), fun _ ↦ by positivity, by
      have : (Fintype.card State : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos (α := State)).ne'
      simp [Finset.card_univ, this]⟩
  reward := fun _ _ ↦ 1
  reward_nonneg := fun _ _ ↦ zero_le_one
  reward_le_one := fun _ _ ↦ le_rfl
  discount := γ
  discount_nonneg := hγ0
  discount_lt_one := hγ1

section Ones

variable [Nonempty State] [Nonempty Action] (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

@[simp] theorem onesMDP_discount :
    (onesMDP (State := State) (Action := Action) γ hγ0 hγ1).discount = γ :=
  rfl

@[simp] theorem onesMDP_reward (s : State) (a : Action) :
    (onesMDP (State := State) (Action := Action) γ hγ0 hγ1).reward s a = 1 := rfl

omit [Fintype State] [Fintype Action] [Nonempty State] in
theorem greedyValue_const (c : ℝ) (s : State) :
    greedyValue (fun (_ : State) (_ : Action) ↦ c) s = c := ciSup_const

/-- The common iterate of all agents on `onesMDP`. -/
noncomputable def onesIter (η : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - η (t + 1)) * onesIter η t + η (t + 1) * (1 + γ * onesIter η t)

theorem batchUpdate_ones (η : ℝ) (B : ℕ) (hB : 1 ≤ B) (c : ℝ)
    (next : State → Action → Fin B → State) (s : State) (a : Action) :
    batchUpdate (onesMDP γ hγ0 hγ1) η B (fun _ _ ↦ c) next s a =
      (1 - η) * c + η * (1 + γ * c) := by
  have hB' : (B : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  simp only [batchUpdate, greedyValue_const, onesMDP_reward, onesMDP_discount,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Every agent's iterate on `onesMDP` is `onesIter`, for every sample path. -/
theorem genericRun_ones (η : ℕ → ℝ) (K B : ℕ) (hK : 1 ≤ K) (hB : 1 ≤ B) (𝒞 : Finset ℕ)
    (samples : ℕ → Fin K → State → Action → Fin B → State) (t : ℕ) :
    genericRun (onesMDP γ hγ0 hγ1) η K B 𝒞 samples t = fun _ _ _ ↦ onesIter γ η t := by
  have hK' : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  induction t with
  | zero => rfl
  | succ t ih =>
    funext k s a
    simp only [genericRun, genericStep, ih]
    split_ifs
    · simp only [batchUpdate_ones γ hγ0 hγ1 _ B hB, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, onesIter]
      field_simp
    · simp only [batchUpdate_ones γ hγ0 hγ1 _ B hB, onesIter]

theorem genericOutput_ones (η : ℕ → ℝ) (K B : ℕ) (hK : 1 ≤ K) (hB : 1 ≤ B) (𝒞 : Finset ℕ)
    (samples : ℕ → Fin K → State → Action → Fin B → State) (T : ℕ) (s : State) (a : Action) :
    genericOutput (onesMDP γ hγ0 hγ1) η K B 𝒞 samples T s a = onesIter γ η T := by
  have hK' : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  simp only [genericOutput, genericRun_ones γ hγ0 hγ1 η K B hK hB, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

include hγ0 hγ1 in
/-- The error of the common iterate is at least `γ^t / (1-γ)` when all rates lie in `[0,1]`. -/
theorem onesIter_error_ge (η : ℕ → ℝ) (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (t : ℕ) :
    γ ^ t / (1 - γ) ≤ 1 / (1 - γ) - onesIter γ η t := by
  have h1γ : 0 < 1 - γ := by linarith
  induction t with
  | zero => simp [onesIter]
  | succ t ih =>
    obtain ⟨h0, h1⟩ := hη (t + 1)
    have hrec : 1 / (1 - γ) - onesIter γ η (t + 1) =
        (1 - η (t + 1) * (1 - γ)) * (1 / (1 - γ) - onesIter γ η t) := by
      simp only [onesIter]
      field_simp
      ring
    have he : 0 ≤ 1 / (1 - γ) - onesIter γ η t := le_trans (div_nonneg (pow_nonneg hγ0 t) h1γ.le) ih
    have hfac : γ ≤ 1 - η (t + 1) * (1 - γ) := by nlinarith
    rw [hrec, pow_succ, mul_comm (γ ^ t) γ, mul_div_assoc]
    calc γ * (γ ^ t / (1 - γ)) ≤ γ * (1 / (1 - γ) - onesIter γ η t) :=
          mul_le_mul_of_nonneg_left ih hγ0
      _ ≤ _ := mul_le_mul_of_nonneg_right hfac he

/-- The optimal Q-function of `onesMDP` is `1/(1-γ)` everywhere. -/
theorem onesMDP_optimalityFixedPoint :
    (onesMDP (State := State) (Action := Action) γ hγ0 hγ1).optimalityFixedPoint =
      fun _ _ ↦ 1 / (1 - γ) := by
  set M := onesMDP (State := State) (Action := Action) γ hγ0 hγ1
  have h1γ : 0 < 1 - γ := by linarith
  have hfix : M.qOptimality (fun _ _ ↦ 1 / (1 - γ)) = fun _ _ ↦ 1 / (1 - γ) := by
    funext s a
    have hS : (Fintype.card State : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := State)).ne'
    simp only [DiscountedMDP.qOptimality, actionMaximum, Finset.sup'_const,
      FiniteDistribution.expectation, M, onesMDP, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
    ring
  have h := M.optimality_fixedPoint_exists_unique
  exact ((Classical.choose_spec h).2 _ hfix).symm

omit [Fintype State] [Fintype Action] in
theorem supError_const (x y : ℝ) :
    supError (fun (_ : State) (_ : Action) ↦ x) (fun _ _ ↦ y) = |x - y| := by
  simp only [supError, ciSup_const]

end Ones

/-- The constant `C_γ` of the export: `γ^{N_max} / (1-γ)` with
`N_max = ⌊exp √(c₀/(1-γ))⌋`. -/
noncomputable def lbConst (c₀ γ : ℝ) : ℝ :=
  γ ^ ⌊Real.exp (Real.sqrt (c₀ / (1 - γ)))⌋₊ / (1 - γ)

theorem lbConst_pos (c₀ γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) : 0 < lbConst c₀ γ := by
  have : 0 < 1 - γ := by linarith
  unfold lbConst
  positivity

/-- **Theorem 7.10, universal `c₀` first.** For every `c₀`, if the schedule contains `T` and
`|𝒞| ≤ c₀ / ((1-γ) log² N)` with `N = BT ≥ 16`, then on the instance `r ≡ 1` (chosen before `K`)
the expected error of Algorithm 𝒜 is at least `lbConst c₀ γ / (√N log³ N)`, for every number of
agents `K ≥ 1` and all learning rates in `[0,1]`. -/
theorem lowerBound_of_fewRounds (c₀ γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (State Action : Type) [Fintype State] [Fintype Action]
    (hS : 1 ≤ Fintype.card State) (hA : 1 ≤ Fintype.card Action)
    (T B : ℕ) (𝒞 : Finset ℕ) (η : ℕ → ℝ) (hT : 16 ≤ T) (hB : 1 ≤ B) (hT𝒞 : T ∈ 𝒞)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1)
    (hround : (𝒞.card : ℝ) ≤ c₀ / ((1 - γ) * Real.log ((B : ℝ) * T) ^ 2)) :
    ∃ M : DiscountedMDP State Action, M.discount = γ ∧
      ∀ K : ℕ, 1 ≤ K →
        lbConst c₀ γ / (Real.sqrt ((B : ℝ) * T) * Real.log ((B : ℝ) * T) ^ 3) ≤
          ∫ data, supError (genericOutput M η K B 𝒞 (fedSamplesExtend M T K B data) T)
            M.optimalityFixedPoint ∂fedSamplingLaw M T K B := by
  haveI : Nonempty State := Fintype.card_pos_iff.mp (by omega)
  haveI : Nonempty Action := Fintype.card_pos_iff.mp (by omega)
  have h1γ : 0 < 1 - γ := by linarith
  refine ⟨onesMDP γ hγ0.le hγ1, rfl, fun K hK ↦ ?_⟩
  set M := onesMDP (State := State) (Action := Action) γ hγ0.le hγ1
  -- The integrand is the constant `e_T`.
  have hint : (fun data ↦ supError (genericOutput M η K B 𝒞 (fedSamplesExtend M T K B data) T)
      M.optimalityFixedPoint) = fun _ ↦ 1 / (1 - γ) - onesIter γ η T := by
    funext data
    have hout : genericOutput M η K B 𝒞 (fedSamplesExtend M T K B data) T =
        fun _ _ ↦ onesIter γ η T := by
      funext s a
      exact genericOutput_ones γ hγ0.le hγ1 η K B hK hB 𝒞 _ T s a
    have he := onesIter_error_ge γ hγ0.le hγ1 η hη T
    have he0 : 0 ≤ 1 / (1 - γ) - onesIter γ η T :=
      le_trans (div_nonneg (pow_nonneg hγ0.le T) h1γ.le) he
    rw [hout, onesMDP_optimalityFixedPoint, supError_const, abs_sub_comm, abs_of_nonneg he0]
  rw [hint, integral_const, probReal_univ, one_smul]
  -- Bound `T` through the communication hypothesis.
  set N : ℝ := (B : ℝ) * T with hN
  have hTr : (16 : ℝ) ≤ T := by exact_mod_cast hT
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hTN : (T : ℝ) ≤ N := by nlinarith
  have hN16 : (16 : ℝ) ≤ N := le_trans hTr hTN
  have hNpos : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have hcard : (1 : ℝ) ≤ 𝒞.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨T, hT𝒞⟩
  have hL2 : Real.log N ^ 2 ≤ c₀ / (1 - γ) := by
    have h1 : 1 ≤ c₀ / ((1 - γ) * Real.log N ^ 2) := le_trans hcard hround
    have hden : 0 < (1 - γ) * Real.log N ^ 2 := by positivity
    rw [le_div_iff₀ hden, one_mul] at h1
    rw [le_div_iff₀ h1γ]
    linarith
  have hL : Real.log N ≤ Real.sqrt (c₀ / (1 - γ)) := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ Real.log N)]
    exact Real.sqrt_le_sqrt hL2
  have hNle : N ≤ Real.exp (Real.sqrt (c₀ / (1 - γ))) := by
    rw [← Real.exp_log hNpos]
    exact Real.exp_le_exp.mpr hL
  have hTfloor : T ≤ ⌊Real.exp (Real.sqrt (c₀ / (1 - γ)))⌋₊ :=
    Nat.le_floor (le_trans hTN hNle)
  have hpow : γ ^ ⌊Real.exp (Real.sqrt (c₀ / (1 - γ)))⌋₊ ≤ γ ^ T :=
    pow_le_pow_of_le_one hγ0.le hγ1.le hTfloor
  have hden1 : 1 ≤ Real.sqrt N * Real.log N ^ 3 := by
    have hs : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by linarith)
    have hl : 1 ≤ Real.log N ^ 3 := one_le_pow₀ hlog1
    nlinarith
  calc lbConst c₀ γ / (Real.sqrt N * Real.log N ^ 3) ≤ lbConst c₀ γ :=
        div_le_self (lbConst_pos c₀ γ hγ0 hγ1).le hden1
    _ ≤ γ ^ T / (1 - γ) := by
        unfold lbConst
        exact div_le_div_of_nonneg_right hpow h1γ.le
    _ ≤ 1 / (1 - γ) - onesIter γ η T := onesIter_error_ge γ hγ0.le hγ1 η hη T

/-- Both printed learning-rate schedules take values in `(0,1] ⊆ [0,1]` on `1 ≤ t ≤ T`. -/
theorem printedRates_mem_Icc (γ : ℝ) (hγ1 : γ < 1) (T : ℕ) (η : ℕ → ℝ)
    (hη : (∃ c_η : ℝ, 0 < c_η ∧ ∀ t : ℕ, 1 ≤ t → t ≤ T → η t = 1 / (1 + c_η * (1 - γ) * t)) ∨
      (∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧ ∀ t : ℕ, 1 ≤ t → t ≤ T → η t = η₀)) :
    ∀ t, 1 ≤ t → t ≤ T → 0 ≤ η t ∧ η t ≤ 1 := by
  intro t ht1 htT
  rcases hη with ⟨c, hc, h⟩ | ⟨η₀, h0, h1, h⟩
  · rw [h t ht1 htT]
    have h1γ : 0 < 1 - γ := by linarith
    have hd : 1 ≤ 1 + c * (1 - γ) * t := by
      have : 0 ≤ c * (1 - γ) * t := by positivity
      linarith
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact hd⟩
  · rw [h t ht1 htT]
    exact ⟨h0.le, h1.le⟩

/-- The iterates up to `T` depend on the learning rates only through `η 1, …, η T`. -/
theorem genericRun_congr_rates (M : DiscountedMDP State Action) (η η' : ℕ → ℝ) (K B : ℕ)
    (𝒞 : Finset ℕ) (samples : ℕ → Fin K → State → Action → Fin B → State) (T : ℕ)
    (h : ∀ t, 1 ≤ t → t ≤ T → η t = η' t) :
    ∀ t, t ≤ T → genericRun M η K B 𝒞 samples t = genericRun M η' K B 𝒞 samples t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    simp only [genericRun]
    rw [ih (by omega), h (n + 1) (by omega) hn]

/-- `lowerBound_of_fewRounds` with the rates constrained only on `1 ≤ t ≤ T`. -/
theorem lowerBound_of_fewRounds_onRange (c₀ γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (State Action : Type) [Fintype State] [Fintype Action]
    (hS : 1 ≤ Fintype.card State) (hA : 1 ≤ Fintype.card Action)
    (T B : ℕ) (𝒞 : Finset ℕ) (η : ℕ → ℝ) (hT : 16 ≤ T) (hB : 1 ≤ B) (hT𝒞 : T ∈ 𝒞)
    (hη : ∀ t, 1 ≤ t → t ≤ T → 0 ≤ η t ∧ η t ≤ 1)
    (hround : (𝒞.card : ℝ) ≤ c₀ / ((1 - γ) * Real.log ((B : ℝ) * T) ^ 2)) :
    ∃ M : DiscountedMDP State Action, M.discount = γ ∧
      ∀ K : ℕ, 1 ≤ K →
        lbConst c₀ γ / (Real.sqrt ((B : ℝ) * T) * Real.log ((B : ℝ) * T) ^ 3) ≤
          ∫ data, supError (genericOutput M η K B 𝒞 (fedSamplesExtend M T K B data) T)
            M.optimalityFixedPoint ∂fedSamplingLaw M T K B := by
  classical
  let η' : ℕ → ℝ := fun t ↦ if 1 ≤ t ∧ t ≤ T then η t else 1
  have hη' : ∀ t, 0 ≤ η' t ∧ η' t ≤ 1 := by
    intro t
    simp only [η']
    split_ifs with ht
    · exact hη t ht.1 ht.2
    · exact ⟨zero_le_one, le_rfl⟩
  have hagree : ∀ t, 1 ≤ t → t ≤ T → η t = η' t := by
    intro t h1 h2
    simp only [η', if_pos (And.intro h1 h2)]
  obtain ⟨M, hM, hK⟩ := lowerBound_of_fewRounds c₀ γ hγ0 hγ1 State Action hS hA T B 𝒞 η'
    hT hB hT𝒞 hη' hround
  refine ⟨M, hM, fun K hK1 ↦ ?_⟩
  have hout : ∀ data, genericOutput M η K B 𝒞 (fedSamplesExtend M T K B data) T =
      genericOutput M η' K B 𝒞 (fedSamplesExtend M T K B data) T := by
    intro data
    funext s a
    simp only [genericOutput,
      genericRun_congr_rates M η η' K B 𝒞 _ T hagree T le_rfl]
  simp only [hout]
  exact hK K hK1

end StatisticalRL.Ch7Rest.FedGeneric
