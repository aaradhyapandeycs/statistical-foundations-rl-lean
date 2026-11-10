import Formalization.ModelFree.AsyncQ.Core
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.MDP.FixedPoint

/-! # Printed Theorem 4.12 and Remark 4.3 are false at `T = 1` (SOURCE-ISSUES C34 (1))

Source: `thm:infinite-horizon-asyn`, `chapters/generative_model_model_free.tex:2062–2086`, rate
`eq:thm:infinite-horizaon-eta-asyn` (:2054–2058), `assump:ergodicity-asyncQ` (:2012–2016),
`defn:mu-min` (:2024–2028), `defn-tmix` (:2034–2039); Remark 4.3 (:2088–2090).

`Thm4_12_printed` is the statement-index entry `Thm4_12_corrected`
(`Formalization/Statements/Ch4.lean`) with its two C34 premises `0 < μ_min` and
`2 ≤ T ∨ 2 ≤ S A` removed. It keeps the domain premise `1 ≤ T` (implicit in the source), which
only makes the transcription weaker and the refutation stronger. `Remark4_3_printed` is the
reading `Remark4_3_corrected` (the remark has no displayed formula; reading as in Remarks
4.1/4.2) with the same two premises removed.

Instance: `S = A = Unit`, `γ = 1/2`, reward `0`, `μ_min = 1`, `t_mix = 0`, `T = 1`,
`δ = ε = 1/2` (Theorem 4.12) and `ε = 1/4` (Remark 4.3). At `T = 1`, `log³ T = 0`, so the rate
`c₁ log³T/((1−γ) T μ_min)` is `0` and the
budget reads `0 ≤ 1` for every `c₂`; with rate `0` the iterate never moves, `Q_1 = Q_0`. Whatever
the value `q = Q⋆((),())` is, one of `Q₀ ≡ 0` or `Q₀ ≡ 2 = 1/(1−γ)` (both admissible) is at
distance `≥ 1 > ε` from it, so the accuracy event is empty (Theorem 4.12), and the mean error is
`≥ 1 > 1/2 = 2ε > 23/64 = ε(1−δ) + δ/(1−γ)` with `δ = ε(1−γ)/2 = 1/16` (Remark 4.3), so
both the intermediate bound and the bare `2ε` form fail. The argument never
evaluates `Q⋆`; it works for every `c₁` and `c₂` (`not_Thm4_12_printedAt`,
`not_Remark4_3_printedAt`), hence for every quantifier order of the printed "universal constants".

Classification: boundary case `T = 1` (with `S A = 1`), not a Lean junk value: `log 1 = 0`
is the genuine value and the printed premises admit `T = 1`. Read with `η_t ∈ (0,1)` (:1937)
the instance is ill-posed rather than a counterexample (C34 (1)). The `μ_min = 0` failure
(C34 (2)) is not formalized here.
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.AsyncQ

open StatisticalRL.FiniteMarkov

attribute [local instance] pairMeasurableSpace

universe u v

open Classical in
/-- Printed Theorem 4.12 (`thm:infinite-horizon-asyn`,
`chapters/generative_model_model_free.tex:2062–2086`): `Thm4_12_corrected` without the C34
premises `0 < μ_min` and `2 ≤ T ∨ 2 ≤ S A` (the domain premise `1 ≤ T` is kept), for fixed constants `c₁, c₂`. -/
def Thm4_12_printedAt (c₁ c₂ : ℝ) : Prop :=
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A]
    (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (μ : FiniteDistribution (S × A))
    (μmin : ℝ) (tmix : ℕ) (s₀ : S) (δ ε : ℝ) (T : ℕ),
    1 / 2 ≤ M.discount →
    (∀ y, ∑ x, μ.prob x * AsyncQ.pairKernel M πb x y = μ.prob y) →
    (∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (t : ℕ) (x : S × A),
        FiniteMarkov.tvDist (AsyncQ.pairPow M πb t x) μ.prob ≤ C * r ^ t) →
    IsLeast {t : ℕ | ∀ x : S × A,
      FiniteMarkov.tvDist (AsyncQ.pairPow M πb t x) μ.prob ≤ 1 / 4} tmix →
    (∀ x, μmin ≤ μ.prob x) → (∃ x, μ.prob x = μmin) →
    1 ≤ T →
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 →
    c₂ * Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ) ^ 2 / μmin *
        max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2)) (tmix / (1 - M.discount)) ≤ T →
    ∀ Q₀ : S → A → ℝ, (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    1 - δ ≤ (AsyncQ.pathLaw M πb s₀ T).real {x | ∀ s a,
      |AsyncQ.iterate M (c₁ * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε}

/-- Printed Theorem 4.12 (`thm:infinite-horizon-asyn`,
`chapters/generative_model_model_free.tex:2062–2086`): `Thm4_12_corrected` without the C34
premises `0 < μ_min` and `2 ≤ T ∨ 2 ≤ S A` (the domain premise `1 ≤ T` is kept). -/
def Thm4_12_printed : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ Thm4_12_printedAt.{u, v} c₁ c₂

open Classical in
/-- Printed Remark 4.3 (`chapters/generative_model_model_free.tex:2088–2090`), in the reading
of `Remark4_3_corrected` (`δ = ε(1−γ)/2` in Theorem 4.12's budget, mean error
`≤ ε(1−δ) + δ/(1−γ) ≤ 2ε`) without the C34 premises `0 < μ_min` and `2 ≤ T ∨ 2 ≤ S A`, for
fixed constants `c₁, c₂`. -/
def Remark4_3_printedAt (c₁ c₂ : ℝ) : Prop :=
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A]
    (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (μ : FiniteDistribution (S × A))
    (μmin : ℝ) (tmix : ℕ) (s₀ : S) (ε : ℝ) (T : ℕ),
    1 / 2 ≤ M.discount →
    (∀ y, ∑ x, μ.prob x * AsyncQ.pairKernel M πb x y = μ.prob y) →
    (∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (t : ℕ) (x : S × A),
        FiniteMarkov.tvDist (AsyncQ.pairPow M πb t x) μ.prob ≤ C * r ^ t) →
    IsLeast {t : ℕ | ∀ x : S × A,
      FiniteMarkov.tvDist (AsyncQ.pairPow M πb t x) μ.prob ≤ 1 / 4} tmix →
    (∀ x, μmin ≤ μ.prob x) → (∃ x, μ.prob x = μmin) →
    1 ≤ T →
    0 < ε → ε ≤ 1 →
    c₂ * Real.log (2 * (Fintype.card S : ℝ) * Fintype.card A * T /
          (ε * (1 - M.discount))) ^ 2 / μmin *
        max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2)) (tmix / (1 - M.discount)) ≤ T →
    ∀ Q₀ : S → A → ℝ, (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    let δ := ε * (1 - M.discount) / 2
    let err := fun x ↦ ⨆ p : S × A,
      |AsyncQ.iterate M (c₁ * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T p.1 p.2 -
        M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2|
    0 < δ ∧ δ < 1 ∧
    Integrable err (AsyncQ.pathLaw M πb s₀ T) ∧
    ∫ x, err x ∂(AsyncQ.pathLaw M πb s₀ T) ≤ ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
    ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε

/-- Printed Remark 4.3 (`chapters/generative_model_model_free.tex:2088–2090`), in the reading
of `Remark4_3_corrected` without the C34 premises `0 < μ_min` and `2 ≤ T ∨ 2 ≤ S A`. -/
def Remark4_3_printed : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ Remark4_3_printedAt.{u, v} c₁ c₂

/-! The library's `DecidableEq` arguments below are bound with `{}` so that every helper applies to
whatever (classical) instance the transcribed statements carry. -/

local instance thm412PairMeasurableSingletonClass {S A : Type*} :
    @MeasurableSingletonClass (S × A) pairMeasurableSpace :=
  ⟨fun _ ↦ trivial⟩

section General

variable {S A : Type*} [Fintype S] [Fintype A]

/-- With rate `0` asynchronous Q-learning never moves. -/
theorem iterate_rate_zero {decS : DecidableEq S} {decA : DecidableEq A} (M : DiscountedMDP S A) (Q₀ : S → A → ℝ) {n : ℕ}
    (x : Fin (n + 1) → S × A) : ∀ t, iterate M 0 Q₀ x t = Q₀
  | 0 => rfl
  | t + 1 => by
    funext s a
    simp only [iterate, iterate_rate_zero M Q₀ x t]
    split_ifs <;> ring

/-- The path law integrates constants to themselves (it is a probability measure). -/
theorem integral_pathLaw_const {decS : DecidableEq S} (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (s₀ : S)
    (T : ℕ) (c : ℝ) : ∫ _x, c ∂(pathLaw M πb s₀ T) = c := by
  classical
  haveI : IsProbabilityMeasure (pathLaw M πb s₀ T) :=
    pathMeasure_isProb (pairKernel_isStochastic M πb) (initLaw_isProb πb s₀) T
  simp

end General

/-- The probability vector on the one-point type. -/
noncomputable def thm412UnitDist : FiniteDistribution Unit where
  prob := fun _ ↦ 1
  prob_nonneg := fun _ ↦ zero_le_one
  sum_prob := by simp

/-- The probability vector on the one-point pair type. -/
noncomputable def thm412PairDist : FiniteDistribution (Unit × Unit) where
  prob := fun _ ↦ 1
  prob_nonneg := fun _ ↦ zero_le_one
  sum_prob := by simp

/-- One state, one action, reward `0`, discount `1/2`. -/
noncomputable def thm412MDP : DiscountedMDP Unit Unit where
  state_nonempty := ⟨()⟩
  action_nonempty := ⟨()⟩
  transition := fun _ _ ↦ thm412UnitDist
  reward := fun _ _ ↦ 0
  reward_nonneg := fun _ _ ↦ le_rfl
  reward_le_one := fun _ _ ↦ zero_le_one
  discount := 1 / 2
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-- The behaviour policy (the only one). -/
noncomputable def thm412Policy : StationaryPolicy Unit Unit := fun _ ↦ thm412UnitDist

section Instance

variable {decU : DecidableEq Unit} {decU' : DecidableEq Unit}

theorem thm412_pairPow (t : ℕ) (x y : Unit × Unit) :
    @pairPow Unit Unit _ _ decU decU' thm412MDP thm412Policy t x y = 1 := by
  induction t generalizing x y with
  | zero => simp [pairPow, kpow, Subsingleton.elim x y]
  | succ t ih =>
    simp only [pairPow, kpow] at ih ⊢
    simp only [ih, mul_one]
    simp [pairKernel, thm412MDP, thm412Policy, thm412UnitDist]

theorem thm412_tv (t : ℕ) (x : Unit × Unit) :
    tvDist (@pairPow Unit Unit _ _ decU decU' thm412MDP thm412Policy t x)
      thm412PairDist.prob = 0 := by
  simp [tvDist, thm412_pairPow, thm412PairDist]

theorem thm412_stationary (y : Unit × Unit) :
    ∑ x, thm412PairDist.prob x * pairKernel thm412MDP thm412Policy x y =
      thm412PairDist.prob y := by
  simp [thm412PairDist, pairKernel, thm412MDP, thm412Policy, thm412UnitDist]

theorem thm412_ergodic : ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (t : ℕ) (x : Unit × Unit),
    tvDist (@pairPow Unit Unit _ _ decU decU' thm412MDP thm412Policy t x)
      thm412PairDist.prob ≤ C * r ^ t :=
  ⟨0, 0, le_rfl, zero_lt_one, fun t x ↦ by simp [thm412_tv]⟩

theorem thm412_tmix : IsLeast {t : ℕ | ∀ x : Unit × Unit,
    tvDist (@pairPow Unit Unit _ _ decU decU' thm412MDP thm412Policy t x)
      thm412PairDist.prob ≤ 1 / 4} 0 :=
  ⟨fun x ↦ by rw [thm412_tv]; norm_num, fun _ _ ↦ Nat.zero_le _⟩

end Instance

/-- An admissible constant initialization at distance `≥ 1` from a given value `q`. -/
noncomputable def thm412Init (q : ℝ) : Unit → Unit → ℝ := fun _ _ ↦ if q ≤ 1 then 2 else 0

theorem thm412Init_far (q : ℝ) : 1 ≤ |thm412Init q () () - q| := by
  unfold thm412Init
  split_ifs with h
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

theorem thm412Init_far_optimal (s a : Unit) :
    1 ≤ |thm412Init (thm412MDP.trajectoryExpectedQ thm412MDP.optimalGreedyPolicy () ()) s a -
      thm412MDP.trajectoryExpectedQ thm412MDP.optimalGreedyPolicy s a| := by
  cases s; cases a; exact thm412Init_far _

theorem thm412Init_adm (q : ℝ) (s : Unit) (a : Unit) :
    0 ≤ thm412Init q s a ∧ thm412Init q s a ≤ thm412MDP.effectiveHorizon := by
  simp only [thm412Init, DiscountedMDP.effectiveHorizon, thm412MDP]
  split_ifs <;> norm_num

/-- **C34 (1), every constant.** For every `c₁` and `c₂` the printed Theorem 4.12 claim fails
on the `T = 1`, `S = A = 1` instance, which does not depend on the constants; so every quantifier
order of the printed universal constants fails. -/
theorem not_Thm4_12_printedAt (c₁ c₂ : ℝ) : ¬ Thm4_12_printedAt.{0, 0} c₁ c₂ := by
  intro h
  set q := thm412MDP.trajectoryExpectedQ thm412MDP.optimalGreedyPolicy () ()
  have key := h Unit Unit thm412MDP thm412Policy thm412PairDist 1 0 () (1 / 2) (1 / 2) 1
    (by simp [thm412MDP]) thm412_stationary thm412_ergodic thm412_tmix
    (fun _ ↦ by simp [thm412PairDist]) ⟨((), ()), rfl⟩ le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp) (thm412Init q) (thm412Init_adm q)
  simp only [Nat.cast_one, Real.log_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_div, iterate_rate_zero] at key
  have hF : ∀ s a : Unit, ¬ |thm412Init q s a -
      thm412MDP.trajectoryExpectedQ thm412MDP.optimalGreedyPolicy s a| ≤ 1 / 2 :=
    fun s a h ↦ by linarith [thm412Init_far_optimal s a]
  simp only [hF, forall_const, Set.setOf_false, measureReal_empty] at key
  norm_num at key

/-- **C34 (1).** Printed Theorem 4.12 is false (boundary case `T = 1`, `S = A = 1`). -/
theorem not_Thm4_12_printed : ¬ Thm4_12_printed.{0, 0} := by
  rintro ⟨c₁, -, -, c₂, -, h⟩
  exact not_Thm4_12_printedAt c₁ c₂ h

/-- **C34 (1), Remark 4.3, every constant.** The reading of printed Remark 4.3 fails on the same
instance with `ε = 1/4` (so `δ = 1/16`): the mean error is `≥ 1`, which exceeds both the
intermediate bound `ε(1−δ) + δ/(1−γ) = 23/64` and the bare `2ε = 1/2`, for every `c₁` and `c₂`. -/
theorem not_Remark4_3_printedAt (c₁ c₂ : ℝ) : ¬ Remark4_3_printedAt.{0, 0} c₁ c₂ := by
  intro h
  have key := h Unit Unit thm412MDP thm412Policy thm412PairDist 1 0 () (1 / 4) 1
    (by simp [thm412MDP]) thm412_stationary thm412_ergodic thm412_tmix
    (fun _ ↦ by simp [thm412PairDist]) ⟨((), ()), rfl⟩ le_rfl
    (by norm_num) (by norm_num)
    (by simp) (thm412Init (thm412MDP.trajectoryExpectedQ thm412MDP.optimalGreedyPolicy () ()))
    (thm412Init_adm _)
  obtain ⟨-, -, -, hint, h2⟩ := key
  simp only [Nat.cast_one, Real.log_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_div, iterate_rate_zero] at hint
  haveI : Unique (Unit × Unit) := ⟨⟨((), ())⟩, fun _ ↦ rfl⟩
  rw [integral_pathLaw_const, ciSup_unique] at hint
  have hd : thm412MDP.discount = 1 / 2 := rfl
  rw [hd] at hint h2
  have := thm412Init_far_optimal (default : Unit × Unit).1 (default : Unit × Unit).2
  -- the bare reading: mean error `≤ 2ε = 1/2`, against error `≥ 1`
  have hbare := hint.trans h2
  linarith

/-- **C34 (1), Remark 4.3.** The reading of printed Remark 4.3 is false on the same instance. -/
theorem not_Remark4_3_printed : ¬ Remark4_3_printed.{0, 0} := by
  rintro ⟨c₁, -, -, c₂, -, h⟩
  exact not_Remark4_3_printedAt c₁ c₂ h

end StatisticalRL.AsyncQ
