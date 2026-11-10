import Formalization.MultiAgent.ModelBased.Planner
import Formalization.MultiAgent.Hedge.Main
import Formalization.MultiAgent.Equilibria

/-!
# Theorem 7.6, clause (b): a causal Nash-equilibrium oracle for two-player constant-sum games

Clause (b) of `Thm7_6_restricted` quantifies over causal product-policy oracles returning an exact
Nash equilibrium (`IsNE`, `eq:defn-Nash-E`, `chapters/marl.tex:213–221`) of every empirical game.
This file shows that for two-player constant-sum games such an oracle exists, with no minimax theorem
and no Nash theorem:

* `neOracle hA G := margProd (ccePlanner hA G)`: the product of the per-step marginals of the
  backward-induction CCE planner (`MultiAgent/ModelBased/Planner.lean`). It is causal (`neOracle_causal`), because
  `margProd` acts pointwise in the step `h`.
* `neOracle_isNE`: if `r₀ + r₁ = c` on steps `1..H` (any constant `c`; `c = 0` is zero-sum, `c = 1`
  is compatible with rewards in `[0,1]`), then `neOracle hA G` is an exact Nash equilibrium of `G`.
  Proof: an exact CCE has `gapJ ≤ 0`; shifting player 1's reward by `−c` changes no gap
  (`gapJ_shift`); `gap_margProd_le_two_mul` gives `gap(margProd π) ≤ 2·gapJ(π) ≤ 0`; and
  `value ≤ bestResponseValue` always, so equality holds at every `(s, i)`.
* `exists_causalNEOracle_constSum`, `exists_causalNEOracle_zeroSum`: the oracle exists.
* `thm7_6_clauseB_hypotheses_constSum`: for every two-player constant-sum game `G`, every `N`, the
  hypotheses of clause (b) (causality and `IsNE` for every empirical game, written as in the clause)
  are satisfiable, since `empiricalGame` keeps the true reward.

The m ≥ 3 and general-sum two-player cases are not covered (they need Nash's existence theorem).
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl77

variable {S H : ℕ} {A : Fin 2 → ℕ}

/-- The product of the marginals of the causal backward-induction CCE planner. -/
noncomputable def neOracle (hA : ∀ i, 0 < A i) (G : MarkovGame 2 S H A) : ProductPolicy 2 S A :=
  margProd (ccePlanner hA G)

theorem neOracle_causal (hA : ∀ i, 0 < A i) :
    CausalProductOracle (neOracle (S := S) (H := H) hA) := by
  intro G G' h hag i
  have := ccePlanner_causal hA G G' h hag
  funext s
  simp only [neOracle, margProd, this]

theorem bestResponseValueJ_toJoint_eq {m : ℕ} {B : Fin m → ℕ} (G : MarkovGame m S H B)
    (σ : ProductPolicy m S B) (i : Fin m) (s : Fin S) :
    bestResponseValueJ G (toJoint σ) i s = bestResponseValue G σ i s := by
  unfold bestResponseValueJ bestResponseValue
  refine iSup_congr fun π' => ?_
  rw [valueJ_congr G _ _ i (deviate_toJoint_sum σ i π') H 1 s, valueJ_toJoint]

theorem gapJ_nonpos_of_isCCE (hS : 0 < S) (G : MarkovGame 2 S H A) (π : JointPolicy 2 S A)
    (hπ : IsCCE G π) : gapJ G π ≤ 0 := by
  haveI : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  unfold gapJ
  exact ciSup_le fun s => ciSup_le fun i => by linarith [hπ s i]

/-- Player 1's reward shifted by `−c`. -/
def shiftGame (G : MarkovGame 2 S H A) (c : ℝ) : MarkovGame 2 S H A where
  transition := G.transition
  reward i h s a := G.reward i h s a - (if i = 1 then c else 0)

/-- In a two-player game with `r₀ + r₁ = c` on steps `1..H`, the product of the marginals of an
exact CCE is an exact Nash equilibrium. -/
theorem isNE_margProd_of_isCCE (hA : ∀ i, 0 < A i) (G : MarkovGame 2 S H A) (c : ℝ)
    (hcs : ∀ h, 1 ≤ h → h ≤ H → ∀ s a, G.reward 0 h s a + G.reward 1 h s a = c)
    (π : JointPolicy 2 S A) (hπ : IsCCE G π) : IsNE G (margProd π) := by
  intro s i
  have hS : 0 < S := Nat.lt_of_le_of_lt (Nat.zero_le _) s.2
  set G' := shiftGame G c
  have hzs : ∀ h, 1 ≤ h → h ≤ H → ∀ s a, G'.reward 1 h s a = -G'.reward 0 h s a := by
    intro h h1 hH s a
    have := hcs h h1 hH s a
    simp only [G', shiftGame]
    simp
    linarith
  have hshift : ∀ ρ : JointPolicy 2 S A, gapJ G ρ = gapJ G' ρ := fun ρ =>
    gapJ_shift G' G rfl hA (fun i => if i = 1 then c else 0)
      (fun i h s a => by simp only [G', shiftGame]; ring) ρ
  have hgap : gap G (margProd π) ≤ 0 := by
    rw [← gapJ_toJoint, hshift, gapJ_toJoint]
    have h2 := gap_margProd_le_two_mul hS hA G' hzs π
    have h3 := gapJ_nonpos_of_isCCE hS G π hπ
    rw [hshift] at h3
    linarith
  have hterm : bestResponseValue G (margProd π) i s - value G (margProd π) i 1 H s ≤
      gap G (margProd π) := by
    unfold gap
    exact le_ciSup_of_le (Set.finite_range _).bddAbove s
      (le_ciSup (f := fun i => bestResponseValue G (margProd π) i s -
        value G (margProd π) i 1 H s) (Set.finite_range _).bddAbove i)
  have hle := value_le_bestResponseValue G (margProd π) i s
  linarith

/-- The oracle returns an exact Nash equilibrium of every two-player game with `r₀ + r₁ = c` on
steps `1..H`. -/
theorem neOracle_isNE (hA : ∀ i, 0 < A i) (G : MarkovGame 2 S H A) (c : ℝ)
    (hcs : ∀ h, 1 ≤ h → h ≤ H → ∀ s a, G.reward 0 h s a + G.reward 1 h s a = c) :
    IsNE G (neOracle hA G) :=
  isNE_margProd_of_isCCE hA G c hcs _ (ccePlanner_isCCE hA G)

/-- A causal product-policy oracle returning an exact Nash equilibrium of every two-player
constant-sum game exists (one oracle for all constants `c`). -/
theorem exists_causalNEOracle_constSum (hA : ∀ i, 0 < A i) :
    ∃ O : MarkovGame 2 S H A → ProductPolicy 2 S A, CausalProductOracle O ∧
      ∀ (c : ℝ) (G : MarkovGame 2 S H A),
        (∀ h, 1 ≤ h → h ≤ H → ∀ s a, G.reward 0 h s a + G.reward 1 h s a = c) → IsNE G (O G) :=
  ⟨neOracle hA, neOracle_causal hA, fun c G hcs => neOracle_isNE hA G c hcs⟩

/-- Zero-sum form (`r₁ = −r₀` on steps `1..H`). -/
theorem exists_causalNEOracle_zeroSum (hA : ∀ i, 0 < A i) :
    ∃ O : MarkovGame 2 S H A → ProductPolicy 2 S A, CausalProductOracle O ∧
      ∀ G : MarkovGame 2 S H A,
        (∀ h, 1 ≤ h → h ≤ H → ∀ s a, G.reward 1 h s a = -G.reward 0 h s a) → IsNE G (O G) :=
  ⟨neOracle hA, neOracle_causal hA, fun G hzs =>
    neOracle_isNE hA G 0 fun h h1 hH s a => by rw [hzs h h1 hH s a]; ring⟩

/-- Non-vacuity of clause (b) of `Thm7_6_restricted` for two-player constant-sum games: the
oracle hypotheses of clause (b), written exactly as there, are satisfiable. -/
theorem thm7_6_clauseB_hypotheses_constSum (hA : ∀ i, 0 < A i) (G : MarkovGame 2 S H A) (c : ℝ)
    (hcs : ∀ h, 1 ≤ h → h ≤ H → ∀ s a, G.reward 0 h s a + G.reward 1 h s a = c)
    (N : ℕ) (hN : 0 < N) :
    ∃ One : MarkovGame 2 S H A → ProductPolicy 2 S A,
      (∀ (G₁ G₂ : MarkovGame 2 S H A) (h : ℕ),
        (∀ t, h ≤ t → G₁.transition t = G₂.transition t ∧ ∀ i, G₁.reward i t = G₂.reward i t) →
        ∀ i, One G₁ i h = One G₂ i h) ∧
      (∀ data, ∀ (s : Fin S) (i : Fin 2),
        value (empiricalGame G N hN data) (One (empiricalGame G N hN data)) i 1 H s =
          bestResponseValue (empiricalGame G N hN data) (One (empiricalGame G N hN data)) i s) :=
  ⟨neOracle hA, neOracle_causal hA, fun data =>
    neOracle_isNE hA (empiricalGame G N hN data) c hcs⟩

end StatisticalRL.Ch7Rest.Marl76
