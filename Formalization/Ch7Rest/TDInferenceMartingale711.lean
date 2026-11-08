import Formalization.Ch7Rest.TDInferenceNoise711

/-!
# Theorem 7.11 support (M3): orthogonality of TD martingale increments

On the i.i.d. path law of `TDInference711Defs.lean` (`inference.tex:54–61`), consider increments
`f_k(V_k, x_{k+1})` that depend on the current TD iterate `V_k` and the next sample `x_{k+1}`, and
are conditionally centred: `∑ₓ p(x) f_k(V, x) = 0` for every `V`. Then (`sum_pathWeight_mul_sq_sum_eq`)

`E (∑_{k<T} f_k(V_k, x_{k+1}))² = ∑_{k<T} E_{length k} ∑ₓ p(x) f_k(V_k, x)²`,

the Pythagorean identity for martingale differences, proved by induction on `T` with the
last-sample decomposition `Fintype.sum_fin_succ_snoc` (M2).
-/

open Finset
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- Adding a centred last increment: `∑ₓ p(x)(S + g(x))² = S² + ∑ₓ p(x) g(x)²`. -/
theorem sum_tupleProb_mul_sq_add_of_centred (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (S : ℝ)
    (g : Tuple State Action → ℝ) (hg : ∑ x, tupleProb M π μ x * g x = 0) :
    ∑ x, tupleProb M π μ x * (S + g x) ^ 2 = S ^ 2 + ∑ x, tupleProb M π μ x * g x ^ 2 := by
  have e : ∀ x, tupleProb M π μ x * (S + g x) ^ 2 =
      S ^ 2 * tupleProb M π μ x + 2 * S * (tupleProb M π μ x * g x) +
        tupleProb M π μ x * g x ^ 2 := fun x ↦ by ring
  simp_rw [e, sum_add_distrib, ← mul_sum, sum_tupleProb, hg]
  ring

/-- **Martingale orthogonality on the TD path law.** -/
theorem sum_pathWeight_mul_sq_sum_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (f : ℕ → (State → ℝ) → Tuple State Action → ℝ)
    (hf : ∀ k V, ∑ x, tupleProb M π μ x * f k V x = 0) (T : ℕ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (∑ k : Fin T, f k (tdIter M η₀ V₀ ω k) (ω k)) ^ 2 =
      ∑ k ∈ range T, ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x * f k (tdIter M η₀ V₀ ω k) x ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Fintype.sum_fin_succ_snoc, sum_range_succ, ← ih, ← sum_add_distrib]
    refine sum_congr rfl fun ω _ ↦ ?_
    have hsplit : ∀ x, ∑ k : Fin (T + 1),
        f k (tdIter M η₀ V₀ (Fin.snoc ω x : Fin (T + 1) → Tuple State Action) k)
          ((Fin.snoc ω x : Fin (T + 1) → Tuple State Action) k) =
        (∑ k : Fin T, f k (tdIter M η₀ V₀ ω k) (ω k)) + f T (tdIter M η₀ V₀ ω T) x := by
      intro x
      rw [Fin.sum_univ_castSucc]
      congr 1
      · refine sum_congr rfl fun k _ ↦ ?_
        simp only [Fin.val_castSucc, Fin.snoc_castSucc]
        rw [tdIter_snoc_of_le M η₀ V₀ ω x k.2.le]
      · simp only [Fin.val_last, Fin.snoc_last]
        rw [tdIter_snoc_of_le M η₀ V₀ ω x le_rfl]
    simp_rw [hsplit, pathWeight_snoc, mul_assoc, ← mul_sum]
    rw [sum_tupleProb_mul_sq_add_of_centred M π μ _ _ (hf T _), mul_add]

end StatisticalRL.Ch7Rest.TDInference
