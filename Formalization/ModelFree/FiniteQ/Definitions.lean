import Formalization.Generative.FiniteHorizonSamplingDefinitions

/-! # Finite-horizon synchronous Q-learning (definitions)

Source: `sec:finite-horizon-Q-learning`, `chapters/generative_model_model_free.tex:2167–2213`,
update `eqn:q-learning-finite` (:2176–2179), empirical Bellman operator (:2181–2194),
`defn:Vt-finite` (:2196–2200).

For each iteration `t = 1, …, T` the stages are swept backward `h = H, …, 1` and
`Q_{t,h} = (1 - η_t) Q_{t-1,h} + η_t (r_h + max_{a'} Q_{t,h+1}(s_{t,h}(s,a), a'))`, where the target
uses the *current* iteration's `Q_{t,h+1}`. The terminal convention `Q_{t,H+1} ≡ 0` (left implicit in
the source) is the empty-list case below.

Representation: the stages `h, h+1, …, H` form a list; `iterate η L t` is `Q_{t,h}` for the first
stage `h` of `L`. Stage `h` (0-based in Lean) uses, at iteration `t + 1`, the generative-model draw
`data ((h,s,a), t)`, i.e. the zero-based sample index `t`, exactly `SAH` fresh draws per iteration.
-/

namespace StatisticalRL.FiniteQLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- One stage of finite-horizon synchronous Q-learning: the environment stage `(P_h, r_h)`, the
stream of next-state draws (iteration `t + 1` uses `sample t s a`, the source `s_{t+1,h}(s,a)`),
and the initialization `Q_{0,h}`. -/
structure LearningStage (State Action : Type*) [Fintype State] [Fintype Action] where
  env : EnvironmentStage State Action
  sample : ℕ → State → Action → State
  init : State → Action → ℝ

/-- The iterates `t ↦ Q_{t,h}` of the first stage `x`, given the iterates `next t = Q_{t,h+1}`
of the following stage: `Q_{0,h} = init` and
`Q_{t+1,h}(s,a) = (1 - η_{t+1}) Q_{t,h}(s,a) + η_{t+1} (r_h(s,a) + max_{a'} Q_{t+1,h+1}(s', a'))`
with `s' = sample t s a`. -/
noncomputable def headIterate (η : ℕ → ℝ) (x : LearningStage State Action)
    (next : ℕ → State → Action → ℝ) : ℕ → State → Action → ℝ
  | 0 => x.init
  | t + 1 => fun s a =>
      (1 - η (t + 1)) * headIterate η x next t s a +
        η (t + 1) * (x.env.reward s a +
          letI : Nonempty Action := x.env.action_nonempty
          actionMaximum (next (t + 1) (x.sample t s a)))

/-- `iterate η L t` is the iterate `Q_{t,h}` of the first stage of the stage list `L`; the empty
list is the terminal stage `H + 1` with `Q_{t,H+1} ≡ 0`. -/
noncomputable def iterate (η : ℕ → ℝ) : List (LearningStage State Action) → ℕ → State → Action → ℝ
  | [] => fun _ _ _ ↦ 0
  | x :: xs => headIterate η x (iterate η xs)

open FiniteHorizonGenerative

/-- The stage list of the actual algorithm run on generative-model data `data` with `T` draws per
`(h,s,a)`: stage `h` uses the draw `data ((h,s,a), t)` at iteration `t + 1` (`t < T`); the value
for `t ≥ T` is never used by the first `T` iterations. -/
def sampledStages {H : ℕ} (E : Fin H → EnvironmentStage State Action) (T : ℕ)
    (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T) :
    List (LearningStage State Action) :=
  List.ofFn fun h ↦
    { env := E h
      sample := fun t s a ↦ if ht : t < T then data ((h, s, a), ⟨t, ht⟩) else s
      init := Q₀ h }

/-- `Q_{t,h}` of synchronous Q-learning on the data `data`, at 0-based stage `h : ℕ`
(source stage `h + 1`); stages `h ≥ H` are terminal and give `0`. -/
noncomputable def sampledIterateAt {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (η : ℕ → ℝ) (T : ℕ) (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T)
    (t h : ℕ) : State → Action → ℝ :=
  iterate η ((sampledStages E T Q₀ data).drop h) t

/-- The output `Q_{T,h}` of `T` iterations of finite-horizon synchronous Q-learning at stage
`h : Fin H` (source stage `h + 1`). -/
noncomputable def sampledIterate {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (η : ℕ → ℝ) (T : ℕ) (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T)
    (h : Fin H) : State → Action → ℝ :=
  sampledIterateAt E η T Q₀ data T h.val

end StatisticalRL.FiniteQLearning
