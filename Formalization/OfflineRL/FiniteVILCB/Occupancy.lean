import Formalization.OfflineRL.FiniteVILCB.Definitions
import Formalization.MDP.Basic

/-!
# Marginals of the trajectory law

`trajProb` is normalized; the stage-`h` state marginal starts at `ρ`; the stage-`h` state-action
occupancy factorizes as `d_h(s) π_h(a|s)`; and the next-state marginal is the one-step push
forward (the flow `d_{h+1} = d_h P^π_h`). Proofs: split off the last stage (`Fin.snoc`) and induct
on the horizon.
-/

open scoped BigOperators

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A]
set_option linter.unusedSectionVars false

noncomputable local instance occDecS : DecidableEq S := Classical.decEq S
noncomputable local instance occDecA : DecidableEq A := Classical.decEq A

/-- Stage-`i` state marginal `P(s_i = s)` of the trajectory law. -/
noncomputable def stateMarg {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (i : Fin (H + 1)) (s : S) : ℝ :=
  ∑ τ : Traj S A H, trajProb E π ρ τ * (if τ.1 i = s then 1 else 0)

/-- Splitting off the last stage. -/
def trajSnoc (H : ℕ) : Traj S A H × A × S ≃ Traj S A (H + 1) where
  toFun x := (Fin.snoc x.1.1 x.2.2, Fin.snoc x.1.2 x.2.1)
  invFun τ := ((Fin.init τ.1, Fin.init τ.2), τ.2 (Fin.last H), τ.1 (Fin.last (H + 1)))
  left_inv x := by
    rcases x with ⟨⟨st, ac⟩, a, s⟩
    simp [Fin.init_snoc, Fin.snoc_last]
  right_inv τ := by
    rcases τ with ⟨st, ac⟩
    simp [Fin.snoc_init_self]

theorem trajProb_snoc {H : ℕ} (E : Fin (H + 1) → EnvironmentStage S A)
    (π : Fin (H + 1) → StationaryPolicy S A) (ρ : FiniteDistribution S)
    (τ : Traj S A H) (a : A) (s' : S) :
    trajProb E π ρ (trajSnoc H (τ, a, s')) =
      trajProb (fun h ↦ E h.castSucc) (fun h ↦ π h.castSucc) ρ τ *
        ((π (Fin.last H) (τ.1 (Fin.last H))).prob a *
          ((E (Fin.last H)).transition (τ.1 (Fin.last H)) a).prob s') := by
  unfold trajProb
  simp only [trajSnoc, Equiv.coe_fn_mk]
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc τ.1 s' : Fin (H + 2) → S) 0 = τ.1 0 := by
    rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, h0]
  rw [show Fin.succ (Fin.last H) = Fin.last (H + 1) from rfl, Fin.snoc_last]
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
  ring

/-- Summing over trajectories with the last stage split off. -/
theorem sum_traj_snoc {H : ℕ} (F : Traj S A (H + 1) → ℝ) :
    ∑ τ, F τ = ∑ τ : Traj S A H, ∑ a : A, ∑ s' : S, F (trajSnoc H (τ, a, s')) := by
  rw [← (trajSnoc (S := S) (A := A) H).sum_comp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [Fintype.sum_prod_type]

theorem trajSnoc_init {H : ℕ} (τ : Traj S A H) (a : A) (s' : S) (i : Fin (H + 1)) :
    (trajSnoc H (τ, a, s')).1 i.castSucc = τ.1 i := by
  simp [trajSnoc, Fin.snoc_castSucc]

theorem trajSnoc_lastAct {H : ℕ} (τ : Traj S A H) (a : A) (s' : S) :
    (trajSnoc H (τ, a, s')).2 (Fin.last H) = a := by
  simp [trajSnoc, Fin.snoc_last]

theorem trajSnoc_lastState {H : ℕ} (τ : Traj S A H) (a : A) (s' : S) :
    (trajSnoc H (τ, a, s')).1 (Fin.last (H + 1)) = s' := by
  simp [trajSnoc, Fin.snoc_last]

/-- **Prefix lemma.** A function of the first `H` stages has the same expectation under the
`(H+1)`-stage law as under the `H`-stage law. -/
theorem sum_traj_prefix {H : ℕ} (E : Fin (H + 1) → EnvironmentStage S A)
    (π : Fin (H + 1) → StationaryPolicy S A) (ρ : FiniteDistribution S)
    (F : Traj S A H → ℝ) :
    ∑ τ, trajProb E π ρ τ * F (Fin.init τ.1, Fin.init τ.2) =
      ∑ τ : Traj S A H, trajProb (fun h ↦ E h.castSucc) (fun h ↦ π h.castSucc) ρ τ * F τ := by
  rw [sum_traj_snoc]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  have hinit : ∀ a s', ((Fin.init (trajSnoc H (τ, a, s')).1, Fin.init (trajSnoc H (τ, a, s')).2) :
      Traj S A H) = τ := by
    intro a s'
    simp [trajSnoc, Fin.init_snoc]
  simp_rw [hinit, trajProb_snoc]
  set X := trajProb (fun h ↦ E h.castSucc) (fun h ↦ π h.castSucc) ρ τ * F τ
  set x := τ.1 (Fin.last H)
  have h1 : ∀ a : A, ∑ s' : S, trajProb (fun h ↦ E h.castSucc) (fun h ↦ π h.castSucc) ρ τ *
      ((π (Fin.last H) x).prob a * ((E (Fin.last H)).transition x a).prob s') * F τ =
      X * (π (Fin.last H) x).prob a := by
    intro a
    calc _ = ∑ s' : S, X * (π (Fin.last H) x).prob a *
          ((E (Fin.last H)).transition x a).prob s' :=
          Finset.sum_congr rfl fun s' _ ↦ by simp only [X]; ring
      _ = X * (π (Fin.last H) x).prob a := by
          rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]
  simp_rw [h1]
  rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]

/-- One-step conditional expectation at stage `h` from state `x`. -/
noncomputable def stepExp {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (h : Fin H) (g : S → A → S → ℝ) (x : S) : ℝ :=
  ∑ a, (π h x).prob a * ∑ s', ((E h).transition x a).prob s' * g x a s'

/-- **Markov step.** The stage-`h` transition is drawn from `π_h` and `P_h` at the current state. -/
theorem sum_traj_step {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (h : Fin H)
    (g : S → A → S → ℝ) :
    ∑ τ, trajProb E π ρ τ * g (τ.1 h.castSucc) (τ.2 h) (τ.1 h.succ) =
      ∑ τ, trajProb E π ρ τ * stepExp E π h g (τ.1 h.castSucc) := by
  induction H with
  | zero => exact h.elim0
  | succ H ih =>
    induction h using Fin.lastCases with
    | last =>
      have hR := sum_traj_prefix E π ρ (fun τ' : Traj S A H ↦
        stepExp E π (Fin.last H) g (τ'.1 (Fin.last H)))
      have hR' : ∑ τ, trajProb E π ρ τ * stepExp E π (Fin.last H) g (τ.1 (Fin.last H).castSucc) =
          ∑ τ, trajProb E π ρ τ * stepExp E π (Fin.last H) g ((Fin.init τ.1) (Fin.last H)) := rfl
      rw [hR', hR, sum_traj_snoc]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      have hs : ∀ a s', (trajSnoc H (τ, a, s')).1 (Fin.last H).succ = s' := by
        intro a s'
        exact trajSnoc_lastState τ a s'
      simp only [trajProb_snoc, trajSnoc_init, trajSnoc_lastAct, hs]
      unfold stepExp
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ ↦ ?_
      ring
    | cast h0 =>
      let F : Traj S A H → ℝ := fun τ' ↦ g (τ'.1 h0.castSucc) (τ'.2 h0) (τ'.1 h0.succ)
      have hL : ∑ τ, trajProb E π ρ τ * g (τ.1 h0.castSucc.castSucc) (τ.2 h0.castSucc)
          (τ.1 h0.castSucc.succ) = ∑ τ, trajProb E π ρ τ * F (Fin.init τ.1, Fin.init τ.2) := by
        refine Finset.sum_congr rfl fun τ _ ↦ ?_
        simp only [F, Fin.init, Fin.succ_castSucc]
      let G : Traj S A H → ℝ := fun τ' ↦
        stepExp (fun h ↦ E h.castSucc) (fun h ↦ π h.castSucc) h0 g (τ'.1 h0.castSucc)
      have hR : ∑ τ, trajProb E π ρ τ * stepExp E π h0.castSucc g (τ.1 h0.castSucc.castSucc) =
          ∑ τ, trajProb E π ρ τ * G (Fin.init τ.1, Fin.init τ.2) := rfl
      rw [hL, hR, sum_traj_prefix, sum_traj_prefix]
      exact ih (fun h ↦ E h.castSucc) (fun h ↦ π h.castSucc) h0

/-- Normalization of the trajectory law. -/
theorem sum_trajProb {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) :
    ∑ τ, trajProb E π ρ τ = 1 := by
  induction H with
  | zero =>
    simp only [trajProb, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]
    rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
    simpa using ρ.sum_prob
  | succ H ih =>
    have := sum_traj_prefix E π ρ (fun _ ↦ 1)
    simp only [mul_one] at this
    rw [this, ih]

/-- Rearranging an expectation of a stage-`i` state function by the marginal. -/
theorem sum_stateMarg {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (i : Fin (H + 1))
    (F : S → ℝ) :
    ∑ s, stateMarg E π ρ i s * F s = ∑ τ, trajProb E π ρ τ * F (τ.1 i) := by
  unfold stateMarg
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  simp [mul_assoc]

theorem stateMarg_nonneg {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (i : Fin (H + 1)) (s : S) :
    0 ≤ stateMarg E π ρ i s := by
  unfold stateMarg
  refine Finset.sum_nonneg fun τ _ ↦ mul_nonneg ?_ (by split_ifs <;> norm_num)
  exact mul_nonneg (ρ.prob_nonneg _) (Finset.prod_nonneg fun h _ ↦
    mul_nonneg ((π h _).prob_nonneg _) (((E h).transition _ _).prob_nonneg _))

/-- The initial marginal is `ρ`. -/
theorem stateMarg_zero {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (s : S) :
    stateMarg E π ρ 0 s = ρ.prob s := by
  induction H with
  | zero =>
    unfold stateMarg
    simp only [trajProb, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]
    rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
    simp
  | succ H ih =>
    unfold stateMarg
    have := sum_traj_prefix E π ρ (fun τ' ↦ if τ'.1 0 = s then (1 : ℝ) else 0)
    have h0 : ∀ τ : Traj S A (H + 1), (Fin.init τ.1) 0 = τ.1 0 := fun τ ↦ rfl
    simp only [h0] at this
    rw [this]
    exact ih _ _

/-- **Occupancy factorization** `d_h(s,a) = d_h(s) π_h(a|s)`. -/
theorem occupancy_eq {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (h : Fin H) (s : S) (a : A) :
    occupancy E π ρ h s a = stateMarg E π ρ h.castSucc s * (π h s).prob a := by
  unfold occupancy
  have := sum_traj_step E π ρ h (fun x b _ ↦ if x = s ∧ b = a then (1 : ℝ) else 0)
  simp only at this
  rw [this, ← sum_stateMarg E π ρ h.castSucc (fun x ↦ stepExp E π h
    (fun x b _ ↦ if x = s ∧ b = a then (1 : ℝ) else 0) x)]
  rw [Finset.sum_eq_single s]
  · congr 1
    unfold stepExp
    simp_rw [← Finset.sum_mul, FiniteDistribution.sum_prob, one_mul]
    simp
  · intro x _ hx
    unfold stepExp
    simp [hx]
  · simp

/-- **Flow** `d_{h+1} = d_h P^π_h`, tested against any function. -/
theorem stateMarg_succ {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (h : Fin H) (f : S → ℝ) :
    ∑ s, stateMarg E π ρ h.succ s * f s =
      ∑ s, stateMarg E π ρ h.castSucc s *
        ∑ a, (π h s).prob a * ((E h).transition s a).expectation f := by
  rw [sum_stateMarg, sum_stateMarg]
  have := sum_traj_step E π ρ h (fun _ _ s' ↦ f s')
  simp only at this
  rw [this]
  rfl

end StatisticalRL.FiniteVILCB
