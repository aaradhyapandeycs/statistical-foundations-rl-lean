import Formalization.OfflineRL.FiniteVILCB.Deterministic
import Formalization.OfflineRL.FiniteVILCB.Occupancy
import Formalization.MDP.FiniteOptimal
import Formalization.MDP.FiniteOccupancy

/-!
# Bridges to the library's finite-horizon values and occupancies

The Theorem 6.16 development uses its own backward recursions `optV`, `polV` and the trajectory
probability `occupancy`. This file proves that they coincide with the library's
`EnvironmentStage.optimalValue`, `DecisionStage.trajectoryValue` (the expectation of cumulative
reward under the trajectory law, `prelim.tex:706–720`) and `DecisionStage.stateActionOccupancy`
(`eq:dh-pi-defn`, `prelim.tex:751–757`). It also proves that a policy optimal at every stage and
state is greedy for `Q⋆` (`prelim.tex:740–745`), so the analysis covers the source's `π⋆`.

The bridge lemmas are adapted from the independent review probe for Theorem 6.16.
-/

open scoped BigOperators ENNReal

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance brDecS : DecidableEq S := Classical.decEq S
noncomputable local instance brDecA : DecidableEq A := Classical.decEq A

/-- `optV E h = optimalValue ((List.ofFn E).drop h)`. -/
theorem optV_eq_optimalValue {H : ℕ} (E : Fin H → EnvironmentStage S A) :
    ∀ n h, h + n = H → optV E h = EnvironmentStage.optimalValue ((List.ofFn E).drop h) := by
  intro n
  induction n with
  | zero =>
    intro h hh
    funext s
    rw [optV_of_ge E (by omega)]
    have : (List.ofFn E).drop h = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]; rfl
  | succ n ih =>
    intro h hh
    have hlt : h < H := by omega
    funext s
    have hd : (List.ofFn E).drop h = E ⟨h, hlt⟩ :: (List.ofFn E).drop (h + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [hd]
    refine (optV_of_lt E ⟨h, hlt⟩ s).trans ?_
    simp only
    rw [ih (h + 1) (by omega)]
    rfl

theorem optV_zero_eq {H : ℕ} (E : Fin H → EnvironmentStage S A) :
    optV E 0 = EnvironmentStage.optimalValue (List.ofFn E) := by
  simpa using optV_eq_optimalValue E H 0 (by omega)

/-- `polV E π h` is the trajectory value of the deterministic policy on the suffix from `h`. -/
theorem polV_eq_trajectoryValue {H : ℕ} (E : Fin H → EnvironmentStage S A) (π : Fin H → S → A) :
    ∀ n h, h + n = H → polV E π h =
      DecisionStage.trajectoryValue
        (EnvironmentStage.controlled ((List.ofFn E).drop h)
          (fun j ↦ extPolicy (detPolicy π) (h + j))) := by
  intro n
  induction n with
  | zero =>
    intro h hh
    funext s
    rw [polV_of_ge E π (by omega)]
    have : (List.ofFn E).drop h = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]
    exact (DecisionStage.trajectoryValue_nil s).symm
  | succ n ih =>
    intro h hh
    have hlt : h < H := by omega
    funext s
    have hd : (List.ofFn E).drop h = E ⟨h, hlt⟩ :: (List.ofFn E).drop (h + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [hd]
    refine (polV_of_lt E π ⟨h, hlt⟩ s).trans ?_
    simp only [EnvironmentStage.controlled]
    rw [DecisionStage.trajectoryValue_cons]
    have ht := ih (h + 1) (by omega)
    have hfun : (fun j ↦ extPolicy (detPolicy π) (h + (j + 1))) =
        (fun j ↦ extPolicy (detPolicy π) (h + 1 + j)) := by
      funext j; congr 1; omega
    rw [hfun, ← ht]
    simp only [DecisionStage.valueBackup, DecisionStage.qBackup, EnvironmentStage.withPolicy,
      extPolicy, detPolicy, add_zero, dif_pos hlt, EnvironmentStage.expectation_pointMass]

theorem polV_zero_eq {H : ℕ} (E : Fin H → EnvironmentStage S A) (π : Fin H → S → A) :
    polV E π 0 = DecisionStage.trajectoryValue
      (EnvironmentStage.controlled (List.ofFn E) (extPolicy (detPolicy π))) := by
  have := polV_eq_trajectoryValue E π H 0 (by omega)
  simpa using this

/-- The gap in library form. -/
theorem gap_bridge {H : ℕ} (E : Fin H → EnvironmentStage S A) (π : Fin H → S → A)
    (ρ : FiniteDistribution S) :
    ρ.expectation (optV E 0) - ρ.expectation (polV E π 0) =
      ρ.expectation (EnvironmentStage.optimalValue (List.ofFn E)) -
        ρ.expectation (DecisionStage.trajectoryValue
          (EnvironmentStage.controlled (List.ofFn E) (extPolicy (detPolicy π)))) := by
  rw [optV_zero_eq, polV_zero_eq]

/-- A `Q⋆`-greedy `π⋆` attains the library optimum. -/
theorem isOptimal_attains {H : ℕ} (E : Fin H → EnvironmentStage S A) (πs : Fin H → S → A)
    (hπs : IsOptimal E πs) (s : S) :
    DecisionStage.trajectoryValue
        (EnvironmentStage.controlled (List.ofFn E) (extPolicy (detPolicy πs))) s =
      EnvironmentStage.optimalValue (List.ofFn E) s := by
  rw [← polV_zero_eq, ← optV_zero_eq]
  have key : ∀ n h, h + n = H → polV E πs h = optV E h := by
    intro n
    induction n with
    | zero => intro h hh; funext t; rw [polV_of_ge E πs (by omega), optV_of_ge E (by omega)]
    | succ n ih =>
      intro h hh
      have hlt : h < H := by omega
      funext t
      refine (polV_of_lt E πs ⟨h, hlt⟩ t).trans
        (Eq.trans ?_ (optV_eq_of_optimal hπs ⟨h, hlt⟩ t).symm)
      simp only
      rw [ih (h + 1) (by omega)]
  rw [key H 0 (by omega)]

/-- **Converse (critic finding 7).** A deterministic policy optimal at every stage and state (its
trajectory value on every suffix equals the optimal value) is greedy for `Q⋆`. -/
theorem isOptimal_of_optimal {H : ℕ} (E : Fin H → EnvironmentStage S A) (πs : Fin H → S → A)
    (hopt : ∀ (h : Fin H) (s : S), DecisionStage.trajectoryValue
        (EnvironmentStage.controlled ((List.ofFn E).drop h.val)
          (fun j ↦ extPolicy (detPolicy πs) (h.val + j))) s =
      EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s) :
    IsOptimal E πs := by
  have heq : ∀ h, polV E πs h = optV E h := by
    intro h
    by_cases hh : h < H
    · funext s
      rw [polV_eq_trajectoryValue E πs (H - h) h (by omega),
        optV_eq_optimalValue E (H - h) h (by omega)]
      exact hopt ⟨h, hh⟩ s
    · funext s
      rw [polV_of_ge E πs (by omega), optV_of_ge E (by omega)]
  intro h s a
  have h1 := optV_of_lt E h s
  have h2 := polV_of_lt E πs h s
  rw [heq, heq] at h2
  calc (E h).reward s a + ((E h).transition s a).expectation (optV E (h.val + 1))
      ≤ optV E h.val s := by
        rw [h1]
        exact le_actionMaximum (fun a ↦ (E h).reward s a +
          ((E h).transition s a).expectation (optV E (h.val + 1))) a
    _ = _ := h2

/-! ## Occupancy bridge -/

theorem stateAfter_append_single (l : List (DecisionStage S A)) (st : DecisionStage S A)
    (ρ : FiniteDistribution S) :
    DecisionStage.stateAfter (l ++ [st]) ρ =
      (DecisionStage.stateAfter l ρ).bind (fun s ↦ (st.policy s).bind (st.transition s)) := by
  induction l generalizing ρ with
  | nil => rfl
  | cons x l ih => exact ih _

theorem controlled_getElem (es : List (EnvironmentStage S A)) (π : ℕ → StationaryPolicy S A)
    (n : ℕ) (hn : n < (EnvironmentStage.controlled es π).length) :
    (EnvironmentStage.controlled es π)[n] =
      (es[n]'(by simpa [controlled_length] using hn)).withPolicy (π n) := by
  induction es generalizing π n with
  | nil => simp [EnvironmentStage.controlled] at hn
  | cons e es ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [EnvironmentStage.controlled, List.getElem_cons_succ]
      exact ih _ n _

/-- The stage-`n` state marginal equals the library's forward state law. -/
theorem stateMarg_eq_stateAfter {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) :
    ∀ n (hn : n < H + 1) (s : S), stateMarg E π ρ ⟨n, hn⟩ s =
      (DecisionStage.stateAfter
        ((EnvironmentStage.controlled (List.ofFn E) (extPolicy π)).take n) ρ).prob s := by
  classical
  intro n
  induction n with
  | zero => intro hn s; simpa using stateMarg_zero E π ρ s
  | succ n ih =>
    intro hn s
    have hlt : n < H := by omega
    have hlen : n < (EnvironmentStage.controlled (List.ofFn E) (extPolicy π)).length := by
      simp [controlled_length, hlt]
    rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some,
      stateAfter_append_single, controlled_getElem]
    have hf := stateMarg_succ E π ρ ⟨n, hlt⟩ (fun x ↦ if x = s then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at hf
    have h1 : (⟨n, hlt⟩ : Fin H).succ = ⟨n + 1, hn⟩ := rfl
    have h2 : (⟨n, hlt⟩ : Fin H).castSucc = ⟨n, by omega⟩ := rfl
    rw [h1, h2] at hf
    rw [hf]
    simp only [FiniteDistribution.bind, FiniteDistribution.expectation,
      EnvironmentStage.withPolicy, extPolicy, dif_pos hlt, List.getElem_ofFn]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [ih (by omega) x]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp [FiniteDistribution.expectation]

/-- **Occupancy bridge.** -/
theorem occupancy_eq_library {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (h : Fin H) (s : S) (a : A) :
    occupancy E π ρ h s a =
      DecisionStage.stateActionOccupancy
        (EnvironmentStage.controlled (List.ofFn E) (extPolicy π)) ρ
        (stageIndex E (extPolicy π) h) s a := by
  rw [occupancy_eq, DecisionStage.stateActionOccupancy_eq, DecisionStage.stateOccupancy]
  have hlen : h.val < (EnvironmentStage.controlled (List.ofFn E) (extPolicy π)).length := by
    simp [controlled_length]
  have := stateMarg_eq_stateAfter E π ρ h.val (by omega) s
  rw [show h.castSucc = ⟨h.val, by omega⟩ from rfl, this]
  congr 1
  simp only [List.get_eq_getElem]
  show (π h s).prob a =
    (((EnvironmentStage.controlled (List.ofFn E) (extPolicy π))[h.val]'hlen).policy s).prob a
  rw [controlled_getElem _ _ _ hlen]
  simp [EnvironmentStage.withPolicy, extPolicy, h.isLt]

/-- `C⋆` in library form. -/
theorem concentrability_eq_library {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (πb : Fin H → StationaryPolicy S A) (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) :
    concentrability E πb ρb ρ πs = ⨆ (h : Fin H) (s : S) (a : A),
      ENNReal.ofReal (DecisionStage.stateActionOccupancy
          (EnvironmentStage.controlled (List.ofFn E) (extPolicy (detPolicy πs))) ρ
          (stageIndex E (extPolicy (detPolicy πs)) h) s a) /
        ENNReal.ofReal (DecisionStage.stateActionOccupancy
          (EnvironmentStage.controlled (List.ofFn E) (extPolicy πb)) ρb
          (stageIndex E (extPolicy πb) h) s a) := by
  unfold concentrability
  simp only [occupancy_eq_library]

end StatisticalRL.FiniteVILCB
