import Formalization.MultiAgent.ModelBased.Definitions
import Formalization.MultiAgent.LowerBound.Product

/-!
# Theorem 7.6: best responses and the gap decomposition

* `valueJ_congr_from`: `valueJ` at step `h` only depends on the policy, kernels and rewards at
  steps `≥ h`.
* `brW`: the backward best-response recursion of player `i` against `π_{-i}`;
  `valueJ_deviate_le_brW`: every Markov deviation is dominated; `brPolicy`: the greedy
  deterministic best response, attaining `brW` at all steps simultaneously (`marl.tex:128–129`).
* `gap_decomposition`: if `π` is an (h = 1) CCE of `Ĝ`, then
  `V^{⋆,π_{-i}}_{i,1} − V^π_{i,1} ≤ (V^{ρ}_{i,1} − V̂^{ρ}_{i,1}) + (V̂^π_{i,1} − V^π_{i,1})` with
  `ρ = brPolicy × π_{-i}`.
* `bestResponseValueJ_eq_of_one`: a player with one action has zero gain.
* NE ⇒ CCE for `toJoint`, causal product oracles give causal joint oracles.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- `valueJ` from step `h` depends only on data at steps `≥ h`. -/
theorem valueJ_congr_from (G G' : MarkovGame m S H A) (π π' : JointPolicy m S A) (i : Fin m) :
    ∀ k h, (∀ t, h ≤ t → π t = π' t) → (∀ t, h ≤ t → G.transition t = G'.transition t) →
      (∀ t, h ≤ t → G.reward i t = G'.reward i t) →
      valueJ G π i h k = valueJ G' π' i h k := by
  intro k
  induction k with
  | zero => intro h _ _ _; funext s; rfl
  | succ k ih =>
    intro h hπ hP hr
    have hnext := ih (h + 1) (fun t ht => hπ t (by omega)) (fun t ht => hP t (by omega))
      (fun t ht => hr t (by omega))
    funext s
    simp only [valueJ]
    rw [hnext, hπ h le_rfl, hP h le_rfl, hr h le_rfl]

/-! ### Best-response recursion -/

/-- Deviation `Q`-value of action `b` of player `i` against `π_{-i}` with continuation `W`. -/
noncomputable def brQ (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (W : Fin S → ℝ) (h : ℕ) (s : Fin S) (b : Fin (A i)) : ℝ :=
  ∑ a', (π h s).prob a' * (G.reward i h s (Function.update a' i b) +
    (G.transition h s (Function.update a' i b)).expectation W)

/-- Backward best-response value `W_{i,h}` over `k` steps. -/
noncomputable def brW (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m) :
    ℕ → ℕ → Fin S → ℝ
  | _, 0, _ => 0
  | h, k + 1, s => ⨆ b : Fin (A i), brQ G π i (brW G π i (h + 1) k) h s b

theorem expectation_mono {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω) {f g : Ω → ℝ}
    (hfg : ∀ x, f x ≤ g x) : d.expectation f ≤ d.expectation g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (d.prob_nonneg x)

theorem brQ_mono (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    {W W' : Fin S → ℝ} (hW : ∀ s, W s ≤ W' s) (h : ℕ) (s : Fin S) (b : Fin (A i)) :
    brQ G π i W h s b ≤ brQ G π i W' h s b :=
  Finset.sum_le_sum fun a' _ => mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (expectation_mono _ hW)) ((π h s).prob_nonneg a')

/-- Every Markov deviation is dominated by the best-response recursion. -/
theorem valueJ_deviate_le_brW (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (π' : PlayerPolicy S (A i)) : ∀ k h s, valueJ G (deviate π i π') i h k s ≤ brW G π i h k s := by
  intro k
  induction k with
  | zero => intro h s; simp [valueJ, brW]
  | succ k ih =>
    intro h s
    simp only [valueJ, brW]
    rw [deviate_sum]
    calc ∑ a', ∑ b, (π h s).prob a' * (π' h s).prob b *
          (G.reward i h s (Function.update a' i b) +
            (G.transition h s (Function.update a' i b)).expectation
              (valueJ G (deviate π i π') i (h + 1) k))
        ≤ ∑ a', ∑ b, (π h s).prob a' * (π' h s).prob b *
          (G.reward i h s (Function.update a' i b) +
            (G.transition h s (Function.update a' i b)).expectation (brW G π i (h + 1) k)) :=
          Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b _ =>
            mul_le_mul_of_nonneg_left (add_le_add le_rfl (expectation_mono _ (ih (h + 1))))
              (mul_nonneg ((π h s).prob_nonneg a') ((π' h s).prob_nonneg b))
      _ = ∑ b, (π' h s).prob b * brQ G π i (brW G π i (h + 1) k) h s b := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [brQ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a' _ => ?_
          ring
      _ ≤ ∑ b, (π' h s).prob b * ⨆ b : Fin (A i), brQ G π i (brW G π i (h + 1) k) h s b :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (le_ciSup (Set.finite_range _).bddAbove b) ((π' h s).prob_nonneg b)
      _ = ⨆ b : Fin (A i), brQ G π i (brW G π i (h + 1) k) h s b := by
          rw [← Finset.sum_mul, (π' h s).sum_prob, one_mul]

/-- The greedy deterministic best response (least-effort choice by `Classical.choose`),
for the horizon ending at step `H`: at step `h` the continuation has `H - h` steps. -/
noncomputable def brPolicy (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) : PlayerPolicy S (A i) := fun h s =>
  haveI : Nonempty (Fin (A i)) := ⟨⟨0, hAi⟩⟩
  EnvironmentStage.pointMass
    (Classical.choose (Finite.exists_max (fun b => brQ G π i (brW G π i (h + 1) (H - h)) h s b)))

theorem pointMass_sum {n : ℕ} (b₀ : Fin n) (f : Fin n → ℝ) :
    ∑ b, (EnvironmentStage.pointMass b₀).prob b * f b = f b₀ := by
  classical
  unfold EnvironmentStage.pointMass
  simp only
  rw [Finset.sum_eq_single b₀]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- The greedy best response attains the recursion at every step (`marl.tex:128–129`). -/
theorem valueJ_brPolicy (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) : ∀ k h, h + k = H + 1 →
      valueJ G (deviate π i (brPolicy G π i hAi)) i h k = brW G π i h k := by
  haveI : Nonempty (Fin (A i)) := ⟨⟨0, hAi⟩⟩
  intro k
  induction k with
  | zero => intro h _; funext s; simp [valueJ, brW]
  | succ k ih =>
    intro h hk
    funext s
    have hnext := ih (h + 1) (by omega)
    have hk' : H - h = k := by omega
    simp only [valueJ, brW]
    rw [deviate_sum, hnext]
    set f := fun b => brQ G π i (brW G π i (h + 1) k) h s b with hf
    have hspec := Classical.choose_spec (Finite.exists_max f)
    have hpol : brPolicy G π i hAi h s =
        EnvironmentStage.pointMass (Classical.choose (Finite.exists_max f)) := by
      simp only [brPolicy, hk', hf]
    rw [hpol]
    have hsum : ∑ a', ∑ b, (π h s).prob a' *
          (EnvironmentStage.pointMass (Classical.choose (Finite.exists_max f))).prob b *
          (G.reward i h s (Function.update a' i b) +
            (G.transition h s (Function.update a' i b)).expectation (brW G π i (h + 1) k)) =
        f (Classical.choose (Finite.exists_max f)) := by
      rw [Finset.sum_comm]
      have : ∀ b, ∑ a', (π h s).prob a' *
            (EnvironmentStage.pointMass (Classical.choose (Finite.exists_max f))).prob b *
            (G.reward i h s (Function.update a' i b) +
              (G.transition h s (Function.update a' i b)).expectation (brW G π i (h + 1) k)) =
          (EnvironmentStage.pointMass (Classical.choose (Finite.exists_max f))).prob b * f b := by
        intro b
        show _ = _ * brQ G π i (brW G π i (h + 1) k) h s b
        rw [brQ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        ring
      simp_rw [this]
      exact pointMass_sum _ f
    rw [hsum]
    apply le_antisymm
    · exact le_ciSup (Set.finite_range _).bddAbove _
    · exact ciSup_le hspec

/-- The best-response value is attained by the greedy best response. -/
theorem bestResponseValueJ_eq_brPolicy (G : MarkovGame m S H A) (π : JointPolicy m S A)
    (i : Fin m) (hAi : 0 < A i) (s : Fin S) :
    bestResponseValueJ G π i s = valueJ G (deviate π i (brPolicy G π i hAi)) i 1 H s := by
  have hatt := congrFun (valueJ_brPolicy G π i hAi H 1 (by omega)) s
  unfold bestResponseValueJ
  apply le_antisymm
  · haveI : Nonempty (PlayerPolicy S (A i)) := ⟨brPolicy G π i hAi⟩
    refine ciSup_le fun π' => ?_
    rw [hatt]
    exact valueJ_deviate_le_brW G π i π' H 1 s
  · refine le_ciSup (f := fun π' : PlayerPolicy S (A i) => valueJ G (deviate π i π') i 1 H s)
      ⟨brW G π i 1 H s, ?_⟩ (brPolicy G π i hAi)
    rintro _ ⟨π', rfl⟩
    exact valueJ_deviate_le_brW G π i π' H 1 s

/-- Any deviation value is at most the best-response value. -/
theorem valueJ_deviate_le_bestResponseValueJ (G : MarkovGame m S H A) (π : JointPolicy m S A)
    (i : Fin m) (π' : PlayerPolicy S (A i)) (s : Fin S) :
    valueJ G (deviate π i π') i 1 H s ≤ bestResponseValueJ G π i s :=
  le_ciSup (f := fun π' : PlayerPolicy S (A i) => valueJ G (deviate π i π') i 1 H s)
    ⟨brW G π i 1 H s, by rintro _ ⟨π'', rfl⟩; exact valueJ_deviate_le_brW G π i π'' H 1 s⟩ π'

/-- Gap decomposition (D): only the step-1 CCE property of `π` in `Ĝ` is used. -/
theorem gap_decomposition (G Ĝ : MarkovGame m S H A) (π : JointPolicy m S A) (hπ : IsCCE Ĝ π)
    (i : Fin m) (hAi : 0 < A i) (s : Fin S) :
    bestResponseValueJ G π i s - valueJ G π i 1 H s ≤
      (valueJ G (deviate π i (brPolicy G π i hAi)) i 1 H s -
          valueJ Ĝ (deviate π i (brPolicy G π i hAi)) i 1 H s) +
        (valueJ Ĝ π i 1 H s - valueJ G π i 1 H s) := by
  rw [bestResponseValueJ_eq_brPolicy G π i hAi s]
  have h1 := valueJ_deviate_le_bestResponseValueJ Ĝ π i (brPolicy G π i hAi) s
  have h2 := hπ s i
  linarith

/-- With a single action, a deviation is the policy itself. -/
theorem deviate_sum_of_one (π : JointPolicy m S A) (i : Fin m) (hAi : A i = 1)
    (π' : PlayerPolicy S (A i)) (h : ℕ) (s : Fin S) (g : ((j : Fin m) → Fin (A j)) → ℝ) :
    ∑ a, (deviate π i π' h s).prob a * g a = ∑ a, (π h s).prob a * g a := by
  rw [deviate_sum]
  have hsub : ∀ (a' : (j : Fin m) → Fin (A j)) (b : Fin (A i)), Function.update a' i b = a' := by
    intro a' b
    have : b = a' i := by
      apply Fin.ext
      have h1 := b.isLt
      have h2 := (a' i).isLt
      omega
    rw [this, Function.update_eq_self]
  simp_rw [hsub]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, (π' h s).sum_prob, mul_one]

theorem bestResponseValueJ_eq_of_one (G : MarkovGame m S H A) (π : JointPolicy m S A)
    (i : Fin m) (hAi : A i = 1) (s : Fin S) :
    bestResponseValueJ G π i s = valueJ G π i 1 H s := by
  have hc : ∀ π' : PlayerPolicy S (A i), valueJ G (deviate π i π') i 1 H s = valueJ G π i 1 H s :=
    fun π' => valueJ_congr G _ _ i (deviate_sum_of_one π i hAi π') H 1 s
  unfold bestResponseValueJ
  simp_rw [hc]
  haveI : Nonempty (PlayerPolicy S (A i)) :=
    ⟨fun _ _ => EnvironmentStage.pointMass ⟨0, by omega⟩⟩
  exact ciSup_const

/-! ### Product policies -/

theorem bestResponseValueJ_toJoint (G : MarkovGame m S H A) (σ : ProductPolicy m S A)
    (i : Fin m) (s : Fin S) :
    bestResponseValueJ G (toJoint σ) i s = bestResponseValue G σ i s := by
  unfold bestResponseValueJ bestResponseValue
  refine iSup_congr fun π' => ?_
  rw [valueJ_congr G _ _ i (deviate_toJoint_sum σ i π') H 1 s, valueJ_toJoint]

/-- A Nash equilibrium is a CCE (`marl.tex:238`). -/
theorem IsNE.isCCE {G : MarkovGame m S H A} {σ : ProductPolicy m S A} (h : IsNE G σ) :
    IsCCE G (toJoint σ) := by
  intro s i
  rw [bestResponseValueJ_toJoint, valueJ_toJoint, h s i]

theorem toJoint_eq_of_step (σ σ' : ProductPolicy m S A) (h : ℕ) (hσ : ∀ i, σ i h = σ' i h) :
    toJoint σ h = toJoint σ' h := by
  funext s
  have hp : ∀ a, (toJoint σ h s).prob a = (toJoint σ' h s).prob a := by
    intro a
    simp only [toJoint, jointProb, hσ]
  cases h1 : toJoint σ h s
  cases h2 : toJoint σ' h s
  rw [h1, h2] at hp
  simp only [FiniteDistribution.mk.injEq]
  exact funext hp

theorem CausalProductOracle.toJoint {O : MarkovGame m S H A → ProductPolicy m S A}
    (hO : CausalProductOracle O) : CausalOracle (fun G => toJoint (O G)) := by
  intro G G' h hagree
  exact toJoint_eq_of_step _ _ h (hO G G' h hagree)

end StatisticalRL.Ch7Rest.Marl76
