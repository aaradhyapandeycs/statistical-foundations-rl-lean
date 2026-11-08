import Formalization.Ch7Rest.TDInference711Defs

/-!
# Printed Theorem 7.11 (`thm:Berry-Esseen-linear`) as Lean propositions (definitions only)

Source: `chapters/inference.tex:132–141` (setting :47–90, `Λ⋆`, `A`, `Γ` :99–117, convex distance
:124–127); `prelim.tex:405–419` (`P_π`, `r_π`). This file proves only trivial implications
between readings. The printed statement is refuted in `TDInferenceZeroNoise711.lean`
(SOURCE-ISSUES C43).

Readings (each can only make the printed claim *easier* to satisfy, so refuting these
propositions refutes the literal text):
* `≲` is a universal constant `c > 0` chosen before every problem quantity
  (`Thm7_11_printed`); `Thm7_11_printed_instWise` even lets `c` depend on the whole instance.
* `C̃` ("problem-related quantity independent of `T`") may depend on every problem quantity
  including `V₀`, but not on `T`; its "polynomial in salient parameters" qualifier is dropped.
* `V₀` is unspecified in the source; the primary reading is "every `V₀`".
  `Thm7_11_printed_someInit` is the weakest reading (some `V₀` per instance; it covers the
  convention `V₀ = 0`).
* `r(s)` in `Γ` is `r_π(s)` (`printedGamma`). `Γ ≻ 0` (`∀ s, 0 < Γ_ss`) is assumed as a
  *definedness* condition: `‖Γ⁻¹‖` and `κ(Γ)` are infinite otherwise (and Lean's `x / 0 = 0`
  would make the junk right-hand side small).
* The printed class `𝒞_d` is *all* convex sets; `d_cvx ≤ ε` is written as
  `∀ C, |P(C) − Q(C)| ≤ ε`. `Thm7_11_printed_allConvex` is that literal class. The refuted
  propositions quantify only over *closed* convex sets (check-file fix F4); this is implied by
  the all-convex reading (`thm7_11_printed_allConvex_imp`), so its refutation is stronger and
  avoids any outer-measure question for non-measurable convex sets.
* The data law is the exact i.i.d. sampling law (:54–61), `lawProb`; the Gaussian
  `N(0, A⁻¹ΓA⁻ᵀ)` is `gaussCov (tdA M π μ) (printedGamma M π μ)`.
-/

namespace StatisticalRL.Ch7Rest.TDInference

/-- Literal reading of Theorem 7.11 over all convex sets (`thm:Berry-Esseen-linear`,
`chapters/inference.tex:132–141`), with universal `c` first, `C̃` per instance (including `V₀`),
every `V₀`, `r(s) = r_π(s)`, and `Γ ≻ 0` as the definedness condition of `‖Γ⁻¹‖, κ(Γ)`. -/
def Thm7_11_printed_allConvex : Prop :=
  ∃ c : ℝ, 0 < c ∧
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    (∀ s, 0 < printedGamma M π μ s) →
    ∃ Ct : ℝ, 0 < Ct ∧
    ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (printedGamma M π μ)).real C| ≤
        c * printedRate M μ (printedGamma M π μ) η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
          Ct * (T : ℝ) ^ (-(1 / 2 : ℝ))

/-- Theorem 7.11 as printed (`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`),
restricted to closed convex sets (a weakening of the printed all-convex class, check fix F4).
Universal `c` first; `C̃` per instance including `V₀`, not shown polynomial; every `V₀`;
`r(s) = r_π(s)`; `Γ ≻ 0` as the definedness condition. Refuted by `not_thm7_11_printed`. -/
def Thm7_11_printed : Prop :=
  ∃ c : ℝ, 0 < c ∧
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    (∀ s, 0 < printedGamma M π μ s) →
    ∃ Ct : ℝ, 0 < Ct ∧
    ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C → IsClosed C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (printedGamma M π μ)).real C| ≤
        c * printedRate M μ (printedGamma M π μ) η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
          Ct * (T : ℝ) ^ (-(1 / 2 : ℝ))

/-- Instance-wise reading (check fix F3): the constant `c` of `≲` as well as `C̃` may depend on
the whole instance `(M, π, μ, η₀, V₀)`; closed convex sets only. Weaker than `Thm7_11_printed`.
Refuted by `not_thm7_11_printed_instWise`. -/
def Thm7_11_printed_instWise : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    (∀ s, 0 < printedGamma M π μ s) →
    ∃ c : ℝ, 0 < c ∧ ∃ Ct : ℝ, 0 < Ct ∧
    ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C → IsClosed C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (printedGamma M π μ)).real C| ≤
        c * printedRate M μ (printedGamma M π μ) η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
          Ct * (T : ℝ) ^ (-(1 / 2 : ℝ))

/-- Weakest initialization reading: some `V₀` per instance (covers the convention `V₀ = 0`);
closed convex sets only. Refuted (under `r(s) = r_π(s)`) by `not_thm7_11_printed_someInit` in
`TDInferenceAnyInit711.lean`. -/
def Thm7_11_printed_someInit : Prop :=
  ∃ c : ℝ, 0 < c ∧
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    (∀ s, 0 < printedGamma M π μ s) →
    ∃ V₀ : State → ℝ, ∃ Ct : ℝ, 0 < Ct ∧
    ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C → IsClosed C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (printedGamma M π μ)).real C| ≤
        c * printedRate M μ (printedGamma M π μ) η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
          Ct * (T : ℝ) ^ (-(1 / 2 : ℝ))

/-- The literal all-convex reading implies the closed-convex reading. -/
theorem thm7_11_printed_allConvex_imp (h : Thm7_11_printed_allConvex) : Thm7_11_printed := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, ?_⟩
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ hη₀ hη₁ hΓ
  obtain ⟨Ct, hCt, hT⟩ := h State Action M π μ η₀ V₀ hμ hη₀ hη₁ hΓ
  exact ⟨Ct, hCt, fun T hT1 C hC _ ↦ hT T hT1 C hC⟩

/-- The universal-constant reading implies the instance-wise reading. -/
theorem thm7_11_printed_imp_instWise (h : Thm7_11_printed) : Thm7_11_printed_instWise := by
  obtain ⟨c, hc, h⟩ := h
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ hη₀ hη₁ hΓ
  obtain ⟨Ct, hCt, hT⟩ := h State Action M π μ η₀ V₀ hμ hη₀ hη₁ hΓ
  exact ⟨c, hc, Ct, hCt, hT⟩

/-- The every-`V₀` reading implies the some-`V₀` reading (take `V₀ = 0`). -/
theorem thm7_11_printed_imp_someInit (h : Thm7_11_printed) : Thm7_11_printed_someInit := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, ?_⟩
  intro State Action _ _ _ _ _ M π μ η₀ hμ hη₀ hη₁ hΓ
  exact ⟨0, h State Action M π μ η₀ 0 hμ hη₀ hη₁ hΓ⟩

end StatisticalRL.Ch7Rest.TDInference
