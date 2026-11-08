import Formalization.MDP.CoreDefinitions
import Formalization.Probability.ExpQuadraticBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Hedge (exponential weights) with a second-order regret bound

`hedgeDist hn η G` is the exponential-weights distribution `π(b) ∝ exp(η G(b))` on `Fin n`
(`n ≥ 1`), i.e. follow-the-regularized-leader with the entropic regularizer.

`hedge_second_order_regret`: for gains `q t ∈ [0, R]^n`, `η > 0`, `η R ≤ 1`, with cumulative gains
`G_t = ∑_{t' < t} q_{t'}` and `π_t = hedgeDist (G_t)`, for every `b`,

  `∑_{t<T} q_t(b) ≤ log n / η + ∑_{t<T} ⟨π_t, q_t⟩ + η ∑_{t<T} Var_{π_t}(q_t)`,

with `Var_π(q) = ∑_b π(b) (q(b) − ⟨π, q⟩)²`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Online.Hedge

open StatisticalRL

/-- Exponential weights `π(b) = exp(η G b) / ∑_c exp(η G c)` on `Fin n`, `n ≥ 1`. -/
noncomputable def hedgeDist {n : ℕ} (hn : 0 < n) (η : ℝ) (G : Fin n → ℝ) :
    FiniteDistribution (Fin n) where
  prob b := Real.exp (η * G b) / ∑ c, Real.exp (η * G c)
  prob_nonneg b := div_nonneg (Real.exp_pos _).le (sum_nonneg fun c _ => (Real.exp_pos _).le)
  sum_prob := by
    have hpos : 0 < ∑ c, Real.exp (η * G c) :=
      sum_pos (fun c _ => Real.exp_pos _) ⟨⟨0, hn⟩, mem_univ _⟩
    rw [← sum_div, div_self hpos.ne']

theorem hedgeDist_prob {n : ℕ} (hn : 0 < n) (η : ℝ) (G : Fin n → ℝ) (b : Fin n) :
    (hedgeDist hn η G).prob b = Real.exp (η * G b) / ∑ c, Real.exp (η * G c) := rfl

/-- Mean of `q` under weights `p`. -/
noncomputable def wmean {n : ℕ} (p : FiniteDistribution (Fin n)) (q : Fin n → ℝ) : ℝ :=
  ∑ b, p.prob b * q b

/-- Variance `∑_b p(b) (q(b) − ⟨p, q⟩)²`. -/
noncomputable def wvar {n : ℕ} (p : FiniteDistribution (Fin n)) (q : Fin n → ℝ) : ℝ :=
  ∑ b, p.prob b * (q b - wmean p q) ^ 2

theorem wvar_nonneg {n : ℕ} (p : FiniteDistribution (Fin n)) (q : Fin n → ℝ) : 0 ≤ wvar p q :=
  sum_nonneg fun b _ => mul_nonneg (p.prob_nonneg b) (sq_nonneg _)

/-- Cumulative gains `G_t(b) = ∑_{t' < t} q_{t'}(b)`. -/
noncomputable def cumGain {n : ℕ} (q : ℕ → Fin n → ℝ) (t : ℕ) (b : Fin n) : ℝ :=
  ∑ t' ∈ range t, q t' b

/-- The Hedge iterate at round `t`. -/
noncomputable def hedgeIter {n : ℕ} (hn : 0 < n) (η : ℝ) (q : ℕ → Fin n → ℝ) (t : ℕ) :
    FiniteDistribution (Fin n) :=
  hedgeDist hn η (cumGain q t)

/-- The (un-normalised) log-potential `Φ_t = log ∑_b exp(η G_t(b))`. -/
noncomputable def potential {n : ℕ} (η : ℝ) (q : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  Real.log (∑ b, Real.exp (η * cumGain q t b))

theorem potential_step {n : ℕ} (hn : 0 < n) {η R : ℝ} (hη : 0 < η) (hηR : η * R ≤ 1)
    (q : ℕ → Fin n → ℝ) (t : ℕ) (hq0 : ∀ b, 0 ≤ q t b) (hq1 : ∀ b, q t b ≤ R) :
    potential η q (t + 1) ≤ potential η q t + η * wmean (hedgeIter hn η q t) (q t) +
      η ^ 2 * wvar (hedgeIter hn η q t) (q t) := by
  set p := hedgeIter hn η q t
  set Z := ∑ c, Real.exp (η * cumGain q t c) with hZ
  have hZpos : 0 < Z := sum_pos (fun c _ => Real.exp_pos _) ⟨⟨0, hn⟩, mem_univ _⟩
  set μ := wmean p (q t)
  set V := wvar p (q t)
  -- the new partition function is `Z · ∑_b p(b) exp(η q_t(b))`
  have hsplit : ∑ b, Real.exp (η * cumGain q (t + 1) b) =
      Z * ∑ b, p.prob b * Real.exp (η * q t b) := by
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    simp only [p, hedgeIter, hedgeDist_prob]
    rw [← hZ, show cumGain q (t + 1) b = cumGain q t b + q t b from sum_range_succ _ _, mul_add,
      Real.exp_add]
    field_simp
  have hμ0 : 0 ≤ μ := sum_nonneg fun b _ => mul_nonneg (p.prob_nonneg b) (hq0 b)
  have hμ1 : μ ≤ R := by
    calc μ ≤ ∑ b, p.prob b * R := sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hq1 b)
          (p.prob_nonneg b)
      _ = R := by rw [← sum_mul, p.sum_prob, one_mul]
  have hX : ∀ b, |η * (q t b - μ)| ≤ 1 := by
    intro b
    rw [abs_mul, abs_of_pos hη]
    have : |q t b - μ| ≤ R := abs_le.2 ⟨by linarith [hq0 b], by linarith [hq1 b]⟩
    calc η * |q t b - μ| ≤ η * R := mul_le_mul_of_nonneg_left this hη.le
      _ ≤ 1 := hηR
  have hmean0 : ∑ b, p.prob b * (η * (q t b - μ)) = 0 := by
    have : ∑ b, p.prob b * (η * (q t b - μ)) = η * (∑ b, p.prob b * q t b - μ * ∑ b, p.prob b) := by
      rw [mul_sub, mul_sum, mul_sum, mul_sum]
      rw [← sum_sub_distrib]; refine sum_congr rfl fun b _ => by ring
    rw [this, p.sum_prob, mul_one]; simp [μ, wmean]
  have hexp : ∑ b, p.prob b * Real.exp (η * (q t b - μ)) ≤ 1 + η ^ 2 * V := by
    calc ∑ b, p.prob b * Real.exp (η * (q t b - μ))
        ≤ ∑ b, p.prob b * (1 + η * (q t b - μ) + (η * (q t b - μ)) ^ 2) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (StatisticalRL.exp_le_one_add_add_sq (hX b)) (p.prob_nonneg b)
      _ = ∑ b, p.prob b + ∑ b, p.prob b * (η * (q t b - μ)) + η ^ 2 * V := by
          rw [← sum_add_distrib]
          simp only [V, wvar, mul_sum]
          rw [← sum_add_distrib]; refine sum_congr rfl fun b _ => by ring
      _ = 1 + η ^ 2 * V := by rw [p.sum_prob, hmean0, add_zero]
  have hfac : ∑ b, p.prob b * Real.exp (η * q t b) =
      Real.exp (η * μ) * ∑ b, p.prob b * Real.exp (η * (q t b - μ)) := by
    rw [mul_sum]; refine sum_congr rfl fun b _ => ?_
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hV0 : 0 ≤ V := wvar_nonneg _ _
  have hinner_pos : 0 < ∑ b, p.prob b * Real.exp (η * (q t b - μ)) := by
    obtain ⟨b, hb⟩ : ∃ b, 0 < p.prob b := by
      by_contra hcon
      push_neg at hcon
      have : ∑ b, p.prob b ≤ 0 := sum_nonpos fun b _ => hcon b
      rw [p.sum_prob] at this; norm_num at this
    exact lt_of_lt_of_le (mul_pos hb (Real.exp_pos _))
      (single_le_sum (f := fun b => p.prob b * Real.exp (η * (q t b - μ)))
        (fun c _ => mul_nonneg (p.prob_nonneg c) (Real.exp_pos _).le) (mem_univ b))
  unfold potential
  rw [hsplit, hfac, Real.log_mul hZpos.ne' (mul_pos (Real.exp_pos _) hinner_pos).ne',
    Real.log_mul (Real.exp_pos _).ne' hinner_pos.ne', Real.log_exp, ← hZ]
  have hlog : Real.log (∑ b, p.prob b * Real.exp (η * (q t b - μ))) ≤ η ^ 2 * V := by
    calc Real.log (∑ b, p.prob b * Real.exp (η * (q t b - μ))) ≤ Real.log (1 + η ^ 2 * V) :=
          Real.log_le_log hinner_pos hexp
      _ ≤ η ^ 2 * V := by
          have := Real.log_le_sub_one_of_pos (show 0 < 1 + η ^ 2 * V by positivity)
          linarith
  linarith

/-- Second-order regret bound of Hedge. -/
theorem hedge_second_order_regret {n : ℕ} (hn : 0 < n) {η R : ℝ} (hη : 0 < η) (hηR : η * R ≤ 1)
    (q : ℕ → Fin n → ℝ) (T : ℕ) (hq0 : ∀ t < T, ∀ b, 0 ≤ q t b) (hq1 : ∀ t < T, ∀ b, q t b ≤ R)
    (b : Fin n) :
    ∑ t ∈ range T, q t b ≤ Real.log n / η + ∑ t ∈ range T, wmean (hedgeIter hn η q t) (q t) +
      η * ∑ t ∈ range T, wvar (hedgeIter hn η q t) (q t) := by
  -- telescoping the potential
  have htel : potential η q T ≤ Real.log n + η * ∑ t ∈ range T, wmean (hedgeIter hn η q t) (q t) +
      η ^ 2 * ∑ t ∈ range T, wvar (hedgeIter hn η q t) (q t) := by
    induction T with
    | zero =>
      simp [potential, cumGain]
    | succ T ih =>
      have ih' := ih (fun t ht => hq0 t (by omega)) (fun t ht => hq1 t (by omega))
      have hs := potential_step hn hη hηR q T (hq0 T (by omega)) (hq1 T (by omega))
      rw [sum_range_succ, sum_range_succ]
      nlinarith
  have hlow : η * ∑ t ∈ range T, q t b ≤ potential η q T := by
    unfold potential
    have hpos : 0 < ∑ c, Real.exp (η * cumGain q T c) :=
      sum_pos (fun c _ => Real.exp_pos _) ⟨⟨0, hn⟩, mem_univ _⟩
    rw [← Real.log_exp (η * ∑ t ∈ range T, q t b)]
    refine Real.log_le_log (Real.exp_pos _) ?_
    exact single_le_sum (f := fun c => Real.exp (η * cumGain q T c))
      (fun c _ => (Real.exp_pos _).le) (mem_univ b)
  have h := hlow.trans htel
  have h2 : ∑ t ∈ range T, q t b ≤ (Real.log n + η * ∑ t ∈ range T, wmean (hedgeIter hn η q t) (q t) +
      η ^ 2 * ∑ t ∈ range T, wvar (hedgeIter hn η q t) (q t)) / η := by
    rw [le_div_iff₀ hη]; linarith
  refine h2.trans (le_of_eq ?_)
  field_simp

end StatisticalRL.Online.Hedge
