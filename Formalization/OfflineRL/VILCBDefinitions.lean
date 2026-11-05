import Formalization.Probability.VarianceDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Lattice.Fold

/-! Definition-only boundary for the offline VI-LCB model.

Source: `chapters/offlineRL.tex:714, 811–852, 728–746`; the source penalty's
zero-count convention is included in the model.
-/

open scoped BigOperators NNReal

namespace StatisticalRL.OfflineVILCB

open StatisticalRL

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Data of one VI-LCB run: discount, sample size, counts, empirical rows,
rewards, and the penalty constants `c_b > 0`, `δ ∈ (0,1)`. -/
structure Input (S A : Type*) [Fintype S] [Fintype A] where
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1
  N : ℕ
  N_pos : 0 < N
  count : S → A → ℕ
  Phat : S → A → FiniteDistribution S
  r : S → A → ℝ
  r_nonneg : ∀ s a, 0 ≤ r s a
  r_le_one : ∀ s a, r s a ≤ 1
  cb : ℝ
  cb_pos : 0 < cb
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt_one : δ < 1

namespace Input

variable (M : Input S A)

/-- `log (N / ((1-γ) δ))`. -/
noncomputable def logTerm : ℝ := Real.log (M.N / ((1 - M.γ) * M.δ))

/-- The source Bernstein penalty `b(s,a;V)` with the zero-count convention. -/
noncomputable def bonus (s : S) (a : A) (V : S → ℝ) : ℝ :=
  if M.count s a = 0 then 1 / (1 - M.γ) + 5 / M.N
  else min (max (Real.sqrt (M.cb * M.logTerm / M.count s a * (M.Phat s a).variance V))
      (2 * M.cb * M.logTerm / ((1 - M.γ) * M.count s a))) (1 / (1 - M.γ)) + 5 / M.N

/-- Unclipped pessimistic backup `r + γ P̂ V − b(V)`. -/
noncomputable def tilde (s : S) (a : A) (V : S → ℝ) : ℝ :=
  M.r s a + M.γ * (M.Phat s a).expectation V - M.bonus s a V

variable [Nonempty A]

/-- `V(s) = max_a Q(s,a)`. -/
noncomputable def value (Q : S → A → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (Q s)

/-- The pessimistic Bellman operator `T_pess`. -/
noncomputable def pess (Q : S → A → ℝ) : S → A → ℝ :=
  fun s a => max (M.tilde s a (value Q)) 0

/-- VI-LCB iterates from `Q̂_0 = 0`. -/
noncomputable def iter (τ : ℕ) : S → A → ℝ := M.pess^[τ] 0

end Input

end StatisticalRL.OfflineVILCB
