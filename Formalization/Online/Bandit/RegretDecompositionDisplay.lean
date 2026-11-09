import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-!
# Pathwise regret decomposition for multi-armed bandits (`eqn:regret-decomposition-ucb`)

Source: `chapters/bandits.tex:58–82`. For any finite arm set with mean rewards `r`, optimal mean
`r⋆ = max_a r(a)` and any realized arm sequence `a_1, …, a_T` (whatever algorithm produced it),
`Regret(T) = T r⋆ − Σ_t r(a_t)` satisfies

* `Regret(T) = Σ_t Δ(a_t) = Σ_a Δ(a) N_T(a)` with `Δ(a) = r⋆ − r(a)` and
  `N_T(a) = #{t ≤ T : a_t = a}` (`eqn:regret-decomposition-ucb`, `:76–82`);
* `Regret(T) ≥ 0` (`:72`, the use of mean rewards "ensures non-negativity").

Both are deterministic identities about the realized arm sequence.
-/

open Finset

namespace StatisticalRL.Bandit

variable {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜]

/-- `eqn:regret-decomposition-ucb` and the nonnegativity of regret, pathwise. -/
theorem regret_decomposition (r : 𝒜 → ℝ) (T : ℕ) (arm : Fin T → 𝒜) :
    let rstar := ⨆ a, r a
    let Δ := fun a ↦ rstar - r a
    (T : ℝ) * rstar - ∑ t, r (arm t) = ∑ t, Δ (arm t) ∧
      ∑ t, Δ (arm t) = ∑ a, Δ a * ((univ.filter fun t ↦ arm t = a).card : ℝ) ∧
      0 ≤ (T : ℝ) * rstar - ∑ t, r (arm t) := by
  intro rstar Δ
  have hfirst : (T : ℝ) * rstar - ∑ t, r (arm t) = ∑ t, Δ (arm t) := by
    simp only [Δ, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hle : ∀ a, r a ≤ rstar := fun a ↦ le_ciSup (Set.finite_range r).bddAbove a
  refine ⟨hfirst, ?_, ?_⟩
  · rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := arm) (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [sum_congr rfl (g := fun _ ↦ Δ a) (fun t ht ↦ by rw [(mem_filter.mp ht).2]), sum_const,
      nsmul_eq_mul, mul_comm]
  · rw [hfirst]
    exact sum_nonneg fun t _ ↦ sub_nonneg.mpr (hle (arm t))

end StatisticalRL.Bandit
