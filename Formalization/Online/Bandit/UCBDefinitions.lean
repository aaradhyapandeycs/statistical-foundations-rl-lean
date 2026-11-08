import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# UCB for Gaussian multi-armed bandits: definitions

Definitions for Theorem 5.1 (`thm:bandit-pure-ucb`, `chapters/bandits.tex:258–277`) and
Algorithm 5.1 (`alg:main-ucb-bandits`, `chapters/bandits.tex:207–251`).

* The noise model is the round-indexed table of `chapters/bandits.tex:37–42`: at every round `t`
  nature draws a noise `z t a ~ N(0,1)` for every arm `a`, all independent; only the noise of the
  pulled arm enters the algorithm (bandit feedback, `:47–48`).
* The UCB index of an arm with `N(a) = 0` is `⊤` (the convention `r^ucb = ∞` of `:387`).
* `a_t` is any element of the argmax set chosen by a tie rule `tie t : Finset (Fin A) → Fin A`
  that may depend on the round (`:232` leaves the selection inside the argmax unspecified).
* Rounds are `0`-indexed: round `t : ℕ` here is round `t + 1` of the source, and
  `ucbState … t` holds the running counts `N` and reward sums `r^sum` before that round.
-/

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace StatisticalRL.Bandit

variable {A : ℕ}

/-- The round-indexed noise table: `z t a` is the noise of arm `a` at round `t`; all entries are
independent standard Gaussians (`chapters/bandits.tex:37–42`). -/
def gaussianNoiseTable (T A : ℕ) : Measure (Fin T → Fin A → ℝ) :=
  Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin A => gaussianReal 0 1

instance (T A : ℕ) : IsProbabilityMeasure (gaussianNoiseTable T A) := by
  unfold gaussianNoiseTable; infer_instance

/-- The UCB index `r̄(a) + √(2 L / N(a))` with `r̄(a) = r^sum(a) / N(a)`, and `⊤` when `N(a) = 0`.
In Theorem 5.1, `L = log (T² / δ)`. -/
def ucbIndex (L : ℝ) (N : Fin A → ℕ) (S : Fin A → ℝ) (a : Fin A) : WithTop ℝ :=
  if N a = 0 then ⊤ else ((S a / (N a : ℝ) + Real.sqrt (2 * L / (N a : ℝ)) : ℝ) : WithTop ℝ)

/-- The set of arms maximizing the UCB index. -/
def ucbArgmax (L : ℝ) (N : Fin A → ℕ) (S : Fin A → ℝ) : Finset (Fin A) :=
  univ.filter fun a => ∀ b, ucbIndex L N S b ≤ ucbIndex L N S a

/-- Running state `(N, r^sum)` of Algorithm 5.1 before round `t` (0-indexed), driven by the
noise sequence `ζ`: the arm pulled at round `t` is `tie t (argmax)` and its reward is
`r a + ζ t a`. -/
def ucbState (tie : ℕ → Finset (Fin A) → Fin A) (L : ℝ) (r : Fin A → ℝ)
    (ζ : ℕ → Fin A → ℝ) : ℕ → (Fin A → ℕ) × (Fin A → ℝ)
  | 0 => (fun _ => 0, fun _ => 0)
  | t + 1 =>
    let st := ucbState tie L r ζ t
    let a := tie t (ucbArgmax L st.1 st.2)
    (Function.update st.1 a (st.1 a + 1), Function.update st.2 a (st.2 a + (r a + ζ t a)))

/-- The arm pulled at round `t` (0-indexed). -/
def ucbArm (tie : ℕ → Finset (Fin A) → Fin A) (L : ℝ) (r : Fin A → ℝ) (ζ : ℕ → Fin A → ℝ)
    (t : ℕ) : Fin A :=
  tie t (ucbArgmax L (ucbState tie L r ζ t).1 (ucbState tie L r ζ t).2)

/-- Extend a finite noise table by zero after the horizon (never read by rounds `< T`). -/
def extendNoise {T : ℕ} (z : Fin T → Fin A → ℝ) : ℕ → Fin A → ℝ :=
  fun t => if h : t < T then z ⟨t, h⟩ else 0

/-- The arm `a_{t+1}` pulled by Algorithm 5.1 at round `t : Fin T` on the noise table `z`. -/
def ucbAction (tie : ℕ → Finset (Fin A) → Fin A) (L : ℝ) (r : Fin A → ℝ) {T : ℕ}
    (z : Fin T → Fin A → ℝ) (t : Fin T) : Fin A :=
  ucbArm tie L r (extendNoise z) t

end StatisticalRL.Bandit

/-!
## Gaussian bandits with a general learner: definitions (Remark 5.12)

Definitions only. They are used by the statement-index entries for Remark 5.12
(`chapters/onlineRL.tex:2725–2729`), in the Gaussian bandit setting of `sec:bandits-UCB`
(`chapters/bandits.tex:15–48`).

* A learner is given by a seed `σ` drawn once from an arbitrary probability space, independent of
  the noise, together with arm maps `arm t σ h : Fin A`, where `h : Fin t → Fin A × ℝ` is the
  history of the `t` previous (arm, observed reward) pairs. The typing makes the learner causal:
  the arm at round `t` reads only the seed and the past. Per-round randomization is a special case
  (take the seed to be a sequence of independent uniforms).
* Nature's noise is the round-indexed table `ζ t a` of `gaussianNoiseTable`
  (`chapters/bandits.tex:37–42`). The learner sees only the reward `μ a_t + ζ t a_t` of the pulled
  arm (`:47–48`).
* Rounds are `0`-indexed.
-/

open MeasureTheory Finset

noncomputable section

namespace StatisticalRL.GaussianBanditLB

variable {A : ℕ} {Seed : Type*}

/-- The history of the first `t` rounds (pairs `(a_s, R_s)` for `s < t`) produced by the arm maps
`arm` with seed `σ`, mean rewards `μ` and noise sequence `ζ`: the reward observed at round `s` is
`μ a_s + ζ s a_s`. -/
def history (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A) (μ : Fin A → ℝ) (σ : Seed)
    (ζ : ℕ → Fin A → ℝ) : (t : ℕ) → Fin t → Fin A × ℝ
  | 0 => Fin.elim0
  | t + 1 =>
    Fin.snoc (α := fun _ => Fin A × ℝ) (history arm μ σ ζ t)
      (arm t σ (history arm μ σ ζ t), μ (arm t σ (history arm μ σ ζ t))
        + ζ t (arm t σ (history arm μ σ ζ t)))

/-- The arm `a_t` pulled at round `t` (0-indexed). -/
def armAt (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A) (μ : Fin A → ℝ) (σ : Seed)
    (ζ : ℕ → Fin A → ℝ) (t : ℕ) : Fin A :=
  arm t σ (history arm μ σ ζ t)

/-- Pseudo-regret `T r⋆ − Σ_{s<T} μ(a_s)` (`chapters/bandits.tex:66–70`) at seed `σ` and noise
table `z : Fin T → Fin A → ℝ` (extended by zero after the horizon; those rows are never read). -/
def regret (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A) (μ : Fin A → ℝ) (T : ℕ)
    (σ : Seed) (z : Fin T → Fin A → ℝ) : ℝ :=
  (T : ℝ) * (⨆ a, μ a) - ∑ s : Fin T, μ (armAt arm μ σ (Bandit.extendNoise z) s)

/-- The hard instance family: arm `0` (index value `0`) has mean `ε/2`, arm `i ≠ 0` has mean `ε` in
instance `i`, all other arms have mean `0`. Instance `0` is the reference. -/
def hardMean (ε : ℝ) (i : Fin A) (a : Fin A) : ℝ :=
  if a = i ∧ i.val ≠ 0 then ε else if a.val = 0 then ε / 2 else 0

end StatisticalRL.GaussianBanditLB
