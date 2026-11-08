import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Fin

/-! # Finite Markov chains: definitions only

Definitions used by the statement of Theorem 4.12 (`thm:infinite-horizon-asyn`,
`chapters/generative_model_model_free.tex:2062–2086`) and its uniform-ergodicity / mixing-time
notions (`assump:ergodicity-asyncQ` :2012–2015, `defn-tmix` :2034–2039). This module contains no
proofs.

* `kpow K t` is the `t`-step transition matrix `K^t` (`K^0 = I`, `K^{t+1} = K K^t`).
* `tvDist p q = ½ ∑_y |p y - q y|` is the total-variation distance of two finite vectors (for
  probability vectors it equals `max_E |p(E) - q(E)|`).
* `pathMass ν K n x = ν(x₀) ∏_{i<n} K(xᵢ, xᵢ₊₁)` is the probability of the path
  `x = (x₀,…,x_n)` of a chain with initial law `ν` and kernel `K`, and `pathMeasure ν K n` is the
  corresponding (discrete) measure on `Fin (n+1) → X`.
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.FiniteMarkov

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `t`-step transition matrix: `K^0 = I`, `K^{t+1}(x,y) = ∑_w K(x,w) K^t(w,y)`. -/
noncomputable def kpow (K : X → X → ℝ) : ℕ → X → X → ℝ
  | 0 => fun x y ↦ if x = y then 1 else 0
  | t + 1 => fun x y ↦ ∑ w, K x w * kpow K t w y

/-- Total-variation distance `½ ∑_y |p y - q y|` of two finite vectors. -/
noncomputable def tvDist (p q : X → ℝ) : ℝ := (1 / 2) * ∑ y, |p y - q y|

/-- Coordinate `i` of a path `x : Fin (n+1) → X`, read as `x_{min i n}`. -/
def pathAt {n : ℕ} (x : Fin (n + 1) → X) (i : ℕ) : X := x ⟨min i n, by omega⟩

/-- Mass `ν(x₀) ∏_{i<n} K(xᵢ, xᵢ₊₁)` of a path of length `n + 1`. -/
noncomputable def pathMass (ν : X → ℝ) (K : X → X → ℝ) (n : ℕ) (x : Fin (n + 1) → X) : ℝ :=
  ν (x 0) * ∏ i : Fin n, K (x i.castSucc) (x i.succ)

/-- Law of the path `(X₀,…,X_n)` of the chain with initial law `ν` and kernel `K`, as a finite sum
of point masses. -/
noncomputable def pathMeasure [MeasurableSpace X] (ν : X → ℝ) (K : X → X → ℝ) (n : ℕ) :
    Measure (Fin (n + 1) → X) :=
  ∑ x : Fin (n + 1) → X, ENNReal.ofReal (pathMass ν K n x) • Measure.dirac x

end StatisticalRL.FiniteMarkov
