import Formalization.OfflineRL.VILCBDefinitions

/-! Definition-only bridge from an offline dataset to a VI-LCB run.

Source: `chapters/offlineRL.tex`. The dataset is `𝒟 = {(s_i,a_i,s_i')}_{i ≤ N}`
(`eq:sampling-offline-inf-iid`, `:28–37`), the visit counts are `N_{s,a}`
(`eq:defn-Nsa-infinite`, `:676–678`), and the empirical kernel is `P̂(·|s,a)`
(`eq:empirical-P-infinite`, `:685–695`), with the uniform row `1/S` when `N_{s,a} = 0`.
The data-independent inputs of `alg:vi-lcb-infinite` (`:827–852`) are bundled in `Params`.
The only proofs here are the probability-vector obligations of the defined rows.
-/

open scoped BigOperators

namespace StatisticalRL.OfflineVILCB

open StatisticalRL

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The uniform row `1/S`, the zero-count branch of `eq:empirical-P-infinite` (`:693–695`). -/
noncomputable def uniformRow (S : Type*) [Fintype S] [Nonempty S] : FiniteDistribution S where
  prob _ := 1 / Fintype.card S
  prob_nonneg _ := by positivity
  sum_prob := by
    have h : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

open Classical in
/-- The visit count `N_{s,a} = Σ_i 1{(s_i,a_i) = (s,a)}` (`eq:defn-Nsa-infinite`, `:676–678`). -/
noncomputable def dataCount {N : ℕ} (x : Fin N → (S × A) × S) (s : S) (a : A) : ℕ :=
  (Finset.univ.filter fun i => (x i).1 = (s, a)).card

open Classical in
/-- The empirical kernel `P̂(·|s,a)` (`eq:empirical-P-infinite`, `:685–695`):
`P̂(s'|s,a) = N_{s,a}⁻¹ Σ_i 1{(s_i,a_i,s_i') = (s,a,s')}` when `N_{s,a} > 0`, and the uniform
row otherwise. -/
noncomputable def dataPhat [Nonempty S] {N : ℕ} (x : Fin N → (S × A) × S) (s : S) (a : A) :
    FiniteDistribution S :=
  if h : dataCount x s a = 0 then uniformRow S else
  { prob := fun t => ((dataCount x s a : ℕ) : ℝ)⁻¹ * ∑ i, if x i = ((s, a), t) then 1 else 0
    prob_nonneg := fun t => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => by split <;> norm_num)
    sum_prob := by
      have key : ∀ y : (S × A) × S,
          ∑ t : S, (if y = ((s, a), t) then (1 : ℝ) else 0) =
            if y.1 = (s, a) then 1 else 0 := by
        intro y
        obtain ⟨p, u⟩ := y
        by_cases hp : p = (s, a)
        · subst hp
          simp [Prod.mk.injEq]
        · simp [Prod.mk.injEq, hp]
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [key]
      have hc : ((dataCount x s a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h
      have hsum : (∑ i : Fin N, if (x i).1 = (s, a) then (1 : ℝ) else 0) =
          ((dataCount x s a : ℕ) : ℝ) := by
        rw [Finset.sum_boole]
        rfl
      rw [hsum]
      exact inv_mul_cancel₀ hc }

/-- Data-independent inputs of `alg:vi-lcb-infinite` (`:827–852`): discount `γ ∈ [0,1)`,
sample size `N > 0`, known rewards in `[0,1]`, and penalty constants `c_b > 0`, `δ ∈ (0,1)`. -/
structure Params (S A : Type*) [Fintype S] [Fintype A] where
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1
  N : ℕ
  N_pos : 0 < N
  r : S → A → ℝ
  r_nonneg : ∀ s a, 0 ≤ r s a
  r_le_one : ∀ s a, r s a ≤ 1
  cb : ℝ
  cb_pos : 0 < cb
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt_one : δ < 1

/-- The VI-LCB run on dataset `x`: counts `dataCount x` and empirical rows `dataPhat x`. -/
noncomputable def Params.input [Nonempty S] (p : Params S A) (x : Fin p.N → (S × A) × S) :
    Input S A where
  γ := p.γ
  γ_nonneg := p.γ_nonneg
  γ_lt_one := p.γ_lt_one
  N := p.N
  N_pos := p.N_pos
  count := dataCount x
  Phat := dataPhat x
  r := p.r
  r_nonneg := p.r_nonneg
  r_le_one := p.r_le_one
  cb := p.cb
  cb_pos := p.cb_pos
  δ := p.δ
  δ_pos := p.δ_pos
  δ_lt_one := p.δ_lt_one

end StatisticalRL.OfflineVILCB
