import Formalization.Online.Bandit.UCBPath

/-!
# UCB: measurability of the action process

The arm pulled at each round, the counts, the reward sums and the first-`k` noise sums of
Algorithm 5.1 are measurable functions of the noise table.
-/

open MeasureTheory Finset

noncomputable section

namespace StatisticalRL.Bandit

variable {A : ℕ} (tie : ℕ → Finset (Fin A) → Fin A) (L : ℝ) (r : Fin A → ℝ)

/-- Selecting a data-dependent index from finitely many measurable branches is measurable. -/
theorem measurable_select_fin {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {n : ℕ}
    {h : α → Fin n} (hh : Measurable h) {G : Fin n → α → β} (hG : ∀ i, Measurable (G i)) :
    Measurable fun x => G (h x) x := by
  have : Measurable fun p : Fin n × α => G p.1 p.2 :=
    measurable_from_prod_countable_right (fun i => hG i)
  exact this.comp (hh.prodMk measurable_id)

theorem measurableSet_ucbIndex_le (N : Fin A → ℕ) (b c : Fin A) :
    MeasurableSet {S : Fin A → ℝ | ucbIndex L N S b ≤ ucbIndex L N S c} := by
  by_cases hc : N c = 0
  · convert MeasurableSet.univ
    ext S; simp [ucbIndex, hc]
  by_cases hb : N b = 0
  · convert MeasurableSet.empty
    ext S; simp [ucbIndex, hc, hb]
  · have : {S : Fin A → ℝ | ucbIndex L N S b ≤ ucbIndex L N S c}
        = {S | S b / (N b : ℝ) + Real.sqrt (2 * L / (N b : ℝ))
            ≤ S c / (N c : ℝ) + Real.sqrt (2 * L / (N c : ℝ))} := by
      ext S; simp only [ucbIndex, hb, hc, if_false, Set.mem_setOf_eq, WithTop.coe_le_coe]
    rw [this]
    exact measurableSet_le (by fun_prop) (by fun_prop)

/-- The UCB selection rule `(N, r^sum) ↦ tie t (argmax)`. -/
def ucbChoose (t : ℕ) (p : (Fin A → ℕ) × (Fin A → ℝ)) : Fin A :=
  tie t (ucbArgmax L p.1 p.2)

theorem measurable_ucbChoose (t : ℕ) : Measurable (ucbChoose tie L t) := by
  classical
  apply measurable_from_prod_countable_right
  intro N
  let cmp : (Fin A → ℝ) → Fin A → Fin A → Bool :=
    fun S b c => decide (ucbIndex L N S b ≤ ucbIndex L N S c)
  have hcmp : Measurable cmp := by
    apply measurable_pi_lambda; intro b
    apply measurable_pi_lambda; intro c
    apply measurable_to_bool
    convert measurableSet_ucbIndex_le L N b c using 1
    ext S; simp [cmp]
  let ψ : (Fin A → Fin A → Bool) → Fin A :=
    fun M => tie t (univ.filter fun a => ∀ b, M b a = true)
  have : (fun S => ucbChoose tie L t (N, S)) = ψ ∘ cmp := by
    ext S
    simp only [ucbChoose, ucbArgmax, Function.comp, ψ, cmp, decide_eq_true_eq]
  rw [this]
  exact (measurable_of_finite ψ).comp hcmp

section State

variable {Ω : Type*} [MeasurableSpace Ω] (ζ : Ω → ℕ → Fin A → ℝ)
  (hζ : ∀ t, Measurable fun ω => ζ ω t)
include hζ

theorem measurable_ucbState (t : ℕ) : Measurable fun ω => ucbState tie L r (ζ ω) t := by
  classical
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    let G : Fin A → ((Fin A → ℕ) × (Fin A → ℝ)) × (Fin A → ℝ) → (Fin A → ℕ) × (Fin A → ℝ) :=
      fun a q => (Function.update q.1.1 a (q.1.1 a + 1),
        Function.update q.1.2 a (q.1.2 a + (r a + q.2 a)))
    have hG : ∀ a, Measurable (G a) := by
      intro a
      apply Measurable.prodMk
      · apply measurable_pi_lambda; intro c
        by_cases hc : c = a
        · subst hc; simp only [Function.update_self]
          exact measurable_from_nat.comp ((measurable_pi_apply c).comp (measurable_fst.comp measurable_fst))
        · simp only [Function.update_of_ne hc]
          exact (measurable_pi_apply c).comp (measurable_fst.comp measurable_fst)
      · apply measurable_pi_lambda; intro c
        by_cases hc : c = a
        · subst hc; simp only [Function.update_self]
          have h1 : Measurable fun q : ((Fin A → ℕ) × (Fin A → ℝ)) × (Fin A → ℝ) => q.1.2 c :=
            (measurable_pi_apply c).comp (measurable_snd.comp measurable_fst)
          have h2 : Measurable fun q : ((Fin A → ℕ) × (Fin A → ℝ)) × (Fin A → ℝ) => q.2 c :=
            (measurable_pi_apply c).comp measurable_snd
          fun_prop
        · simp only [Function.update_of_ne hc]
          exact (measurable_pi_apply c).comp (measurable_snd.comp measurable_fst)
    have hstep : Measurable fun q : ((Fin A → ℕ) × (Fin A → ℝ)) × (Fin A → ℝ) =>
        G (ucbChoose tie L t q.1) q :=
      measurable_select_fin ((measurable_ucbChoose tie L t).comp measurable_fst) hG
    have : (fun ω => ucbState tie L r (ζ ω) (t + 1))
        = (fun q => G (ucbChoose tie L t q.1) q) ∘ (fun ω => (ucbState tie L r (ζ ω) t, ζ ω t)) := by
      ext1 ω; rfl
    rw [this]
    exact hstep.comp (ih.prodMk (hζ t))

theorem measurable_ucbArm (t : ℕ) : Measurable fun ω => ucbArm tie L r (ζ ω) t :=
  (measurable_ucbChoose tie L t).comp (measurable_ucbState tie L r ζ hζ t)

theorem measurable_ucbCount (t : ℕ) (c : Fin A) :
    Measurable fun ω => ucbCount tie L r (ζ ω) t c :=
  (measurable_pi_apply c).comp (measurable_fst.comp (measurable_ucbState tie L r ζ hζ t))

theorem measurable_ucbNoiseSum (T k : ℕ) (c : Fin A) :
    Measurable fun ω => ucbNoiseSum tie L r (ζ ω) T k c := by
  classical
  unfold ucbNoiseSum
  apply Finset.measurable_sum
  intro s _
  apply Measurable.ite
  · have h1 : MeasurableSet {ω | ucbArm tie L r (ζ ω) s = c} :=
      measurable_ucbArm tie L r ζ hζ s (measurableSet_singleton c)
    have h2 : MeasurableSet {ω | ucbCount tie L r (ζ ω) s c < k} :=
      measurable_ucbCount tie L r ζ hζ s c (MeasurableSet.of_discrete (s := {n : ℕ | n < k}))
    exact h1.inter h2
  · exact (measurable_pi_apply c).comp (hζ s)
  · exact measurable_const

end State

theorem measurable_extendNoise {T : ℕ} (t : ℕ) :
    Measurable fun z : Fin T → Fin A → ℝ => extendNoise z t := by
  unfold extendNoise
  by_cases h : t < T
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

end StatisticalRL.Bandit
