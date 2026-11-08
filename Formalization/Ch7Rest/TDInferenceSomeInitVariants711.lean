import Formalization.Ch7Rest.TDInferencePrinted711

/-!
# Theorem 7.11 (`thm:Berry-Esseen-linear`): the weakest initialization reading with
instance-wise constants (definitions and trivial implications only)

Source: `chapters/inference.tex:132–141`. The reviewed M1 module `TDInferencePrinted711.lean`
defines `Thm7_11_printed_someInit` (universal `c`, some `V₀` per instance). This file adds the
reading in which *both* the `≲` constant `c` and `C̃` may be chosen after the instance and after
`V₀` (check-file fix F3 applied to the some-`V₀` reading). It is implied by every other reading
(`thm7_11_printed_someInit_imp_someInitInstWise`, `thm7_11_printed_instWise_imp_someInitInstWise`),
so its refutation (`not_thm7_11_printed_someInit_instWise`, milestone M2) is the strongest one.
-/

namespace StatisticalRL.Ch7Rest.TDInference

/-- Weakest reading of Theorem 7.11 (`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`):
for each instance there are *some* initialization `V₀` and constants `c, C̃` (all chosen after the
instance) such that the printed bound holds on every closed convex set for every `T ≥ 1`.
`r(s) = r_π(s)` in `Γ`; `Γ ≻ 0` as the definedness condition of `‖Γ⁻¹‖, κ(Γ)`. -/
def Thm7_11_printed_someInit_instWise : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    (∀ s, 0 < printedGamma M π μ s) →
    ∃ V₀ : State → ℝ, ∃ c : ℝ, 0 < c ∧ ∃ Ct : ℝ, 0 < Ct ∧
    ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C → IsClosed C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (printedGamma M π μ)).real C| ≤
        c * printedRate M μ (printedGamma M π μ) η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
          Ct * (T : ℝ) ^ (-(1 / 2 : ℝ))

/-- Even weaker reading (critic O1): "for some `0 < η₀ < 1/4`" read as letting the step-size
parameter `η₀` also be chosen per instance. For each instance there are `η₀ ∈ (0, 1/4)`, `V₀` and
constants `c, C̃` such that the printed bound holds on every closed convex set for every `T ≥ 1`.
Implied by `Thm7_11_printed_someInit_instWise` (`thm7_11_printed_someInitInstWise_imp_someEta`);
refuted by `not_thm7_11_printed_someEta_someInit`. `r(s) = r_π(s)`; `Γ ≻ 0` as definedness. -/
def Thm7_11_printed_someEta_someInit : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State),
    (∀ s, 0 < μ.prob s) → (∀ s, 0 < printedGamma M π μ s) →
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 / 4 ∧
    ∃ V₀ : State → ℝ, ∃ c : ℝ, 0 < c ∧ ∃ Ct : ℝ, 0 < Ct ∧
    ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C → IsClosed C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (printedGamma M π μ)).real C| ≤
        c * printedRate M μ (printedGamma M π μ) η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
          Ct * (T : ℝ) ^ (-(1 / 2 : ℝ))

/-- The instance-wise some-`V₀` reading implies the some-`η₀`, some-`V₀` reading (take `η₀ = 1/8`). -/
theorem thm7_11_printed_someInitInstWise_imp_someEta (h : Thm7_11_printed_someInit_instWise) :
    Thm7_11_printed_someEta_someInit := by
  intro State Action _ _ _ _ _ M π μ hμ hΓ
  exact ⟨1 / 8, by norm_num, by norm_num, h State Action M π μ (1 / 8) hμ (by norm_num)
    (by norm_num) hΓ⟩

/-- The universal-constant some-`V₀` reading implies the instance-wise some-`V₀` reading. -/
theorem thm7_11_printed_someInit_imp_someInitInstWise (h : Thm7_11_printed_someInit) :
    Thm7_11_printed_someInit_instWise := by
  obtain ⟨c, hc, h⟩ := h
  intro State Action _ _ _ _ _ M π μ η₀ hμ hη₀ hη₁ hΓ
  obtain ⟨V₀, Ct, hCt, hT⟩ := h State Action M π μ η₀ hμ hη₀ hη₁ hΓ
  exact ⟨V₀, c, hc, Ct, hCt, hT⟩

/-- The instance-wise every-`V₀` reading implies the instance-wise some-`V₀` reading. -/
theorem thm7_11_printed_instWise_imp_someInitInstWise (h : Thm7_11_printed_instWise) :
    Thm7_11_printed_someInit_instWise := by
  intro State Action _ _ _ _ _ M π μ η₀ hμ hη₀ hη₁ hΓ
  obtain ⟨c, hc, Ct, hCt, hT⟩ := h State Action M π μ η₀ 0 hμ hη₀ hη₁ hΓ
  exact ⟨0, c, hc, Ct, hCt, hT⟩

end StatisticalRL.Ch7Rest.TDInference
