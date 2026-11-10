import Formalization.MultiAgent.Hedge.Locality

/-!
# Theorem 7.7: stage-level identities

For a law `μ` of joint actions at step `h`, state `s`, player `i` and continuation `f_{h+1}`:
* `sBell G i f h s μ = E_{a∼μ}[r_{i,h}(s,a) + P_h(s,a)·f_{h+1}]` (so `bellJ G ρ i f h s` is
  `sBell … (ρ h s)`);
* `sSec G i f h s μ c = E_{a∼μ, s′∼P}[(r + f_{h+1}(s′) − c)²]`, `sJvar = sSec` at `c = sBell`
  (so `jvarJ G ρ i f h s` is `sJvar … (ρ h s)`).

Facts: mixtures (`sJvar_avg_ge`), the product/deviation identity `sum_prodDist_eq_sum_dev`,
`devDist` of an average, deviation to point masses, and the range of the algorithm's values.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge StatisticalRL.AdaptiveKL

variable {m S H : ℕ} {A : Fin m → ℕ}

theorem FiniteDistribution.ext_prob {Ω : Type*} [Fintype Ω] {d d' : FiniteDistribution Ω}
    (h : ∀ x, d.prob x = d'.prob x) : d = d' := by
  cases d; cases d'
  simp only [FiniteDistribution.mk.injEq]
  exact funext h

/-! ### Stage-level Bellman value and second moments -/

/-- `E_{a∼μ}[r_{i,h}(s,a) + P_h(s,a)·f_{h+1}]`. -/
noncomputable def sBell (G : MarkovGame m S H A) (i : Fin m) (f : ℕ → Fin S → ℝ) (h : ℕ)
    (s : Fin S) (μ : FiniteDistribution (JointAction m A)) : ℝ :=
  ∑ a, μ.prob a * (G.reward i h s a + (G.transition h s a).expectation (f (h + 1)))

/-- `E_{a∼μ, s′∼P_h(·|s,a)}[(r_{i,h}(s,a) + f_{h+1}(s′) − c)²]`. -/
noncomputable def sSec (G : MarkovGame m S H A) (i : Fin m) (f : ℕ → Fin S → ℝ) (h : ℕ)
    (s : Fin S) (μ : FiniteDistribution (JointAction m A)) (c : ℝ) : ℝ :=
  ∑ a, μ.prob a * (G.transition h s a).expectation
    (fun s' => (G.reward i h s a + f (h + 1) s' - c) ^ 2)

/-- The joint variance under `μ`. -/
noncomputable def sJvar (G : MarkovGame m S H A) (i : Fin m) (f : ℕ → Fin S → ℝ) (h : ℕ)
    (s : Fin S) (μ : FiniteDistribution (JointAction m A)) : ℝ :=
  sSec G i f h s μ (sBell G i f h s μ)

theorem bellJ_eq_sBell (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S) : bellJ G ρ i f h s = sBell G i f h s (ρ h s) := rfl

theorem jvarJ_eq_sJvar (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S) : jvarJ G ρ i f h s = sJvar G i f h s (ρ h s) := rfl

theorem sSec_nonneg (G : MarkovGame m S H A) (i : Fin m) (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S)
    (μ : FiniteDistribution (JointAction m A)) (c : ℝ) : 0 ≤ sSec G i f h s μ c :=
  sum_nonneg fun a _ => mul_nonneg (μ.prob_nonneg a)
    (FiniteDistribution.expectation_nonneg _ fun _ => sq_nonneg _)

/-- Flattening the two-stage law `(a, s′)`. -/
theorem sum_flat (G : MarkovGame m S H A) (h : ℕ) (s : Fin S) (w : JointAction m A → ℝ)
    (F : JointAction m A → Fin S → ℝ) :
    ∑ o : JointAction m A × Fin S, (w o.1 * (G.transition h s o.1).prob o.2) * F o.1 o.2 =
      ∑ a, w a * (G.transition h s a).expectation (F a) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  unfold FiniteDistribution.expectation
  rw [mul_sum]
  refine sum_congr rfl fun s' _ => by ring

/-- The variance is the least second moment: `sJvar μ ≤ sSec μ c`. -/
theorem sJvar_le_sSec (G : MarkovGame m S H A) (i : Fin m) (f : ℕ → Fin S → ℝ) (h : ℕ)
    (s : Fin S) (μ : FiniteDistribution (JointAction m A)) (c : ℝ) :
    sJvar G i f h s μ ≤ sSec G i f h s μ c := by
  have h1 := sum_sq_sub_mean_le (fun o : JointAction m A × Fin S =>
      μ.prob o.1 * (G.transition h s o.1).prob o.2)
    (fun o => G.reward i h s o.1 + f (h + 1) o.2) (by
      rw [Fintype.sum_prod_type]
      simp_rw [← mul_sum, FiniteDistribution.sum_prob, mul_one]
      exact μ.sum_prob) c
  have hmean : ∑ o : JointAction m A × Fin S, μ.prob o.1 * (G.transition h s o.1).prob o.2 *
      (G.reward i h s o.1 + f (h + 1) o.2) = sBell G i f h s μ := by
    rw [sum_flat G h s μ.prob (fun a s' => G.reward i h s a + f (h + 1) s')]
    unfold sBell
    refine sum_congr rfl fun a _ => ?_
    rw [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]
  rw [hmean, sum_flat G h s μ.prob (fun a s' => (G.reward i h s a + f (h + 1) s' -
      sBell G i f h s μ) ^ 2),
    sum_flat G h s μ.prob (fun a s' => (G.reward i h s a + f (h + 1) s' - c) ^ 2)] at h1
  exact h1

/-- Mixture: if `μ̄ = ∑_j w_j d_j` then `∑_j w_j sJvar(d_j) ≤ sJvar(μ̄)`. -/
theorem sJvar_mix_ge {ι : Type*} [Fintype ι] (G : MarkovGame m S H A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S) (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (d : ι → FiniteDistribution (JointAction m A)) (μ : FiniteDistribution (JointAction m A))
    (hmix : ∀ a, μ.prob a = ∑ j, w j * (d j).prob a) :
    ∑ j, w j * sJvar G i f h s (d j) ≤ sJvar G i f h s μ := by
  set g : JointAction m A × Fin S → ℝ := fun o => G.reward i h s o.1 + f (h + 1) o.2
  set p : ι → JointAction m A × Fin S → ℝ := fun j o => (d j).prob o.1 * (G.transition h s o.1).prob o.2
  have hp1 : ∀ j, ∑ o, p j o = 1 := by
    intro j
    simp only [p]
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, FiniteDistribution.sum_prob, mul_one]
    exact (d j).sum_prob
  have key := mixture_variance_ge w p g hw hp1
  have hmean : ∀ ν : FiniteDistribution (JointAction m A), ∑ o : JointAction m A × Fin S,
      ν.prob o.1 * (G.transition h s o.1).prob o.2 * g o = sBell G i f h s ν := by
    intro ν
    rw [sum_flat G h s ν.prob (fun a s' => G.reward i h s a + f (h + 1) s')]
    unfold sBell
    refine sum_congr rfl fun a _ => ?_
    rw [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]
  have hpbar : ∀ o : JointAction m A × Fin S, ∑ j, w j * p j o =
      μ.prob o.1 * (G.transition h s o.1).prob o.2 := by
    intro o
    simp only [p, hmix, sum_mul]
    refine sum_congr rfl fun j _ => by ring
  simp_rw [hpbar] at key
  simp only [p] at key
  rw [hmean μ] at key
  simp_rw [hmean] at key
  rw [sum_flat G h s μ.prob (fun a s' => (G.reward i h s a + f (h + 1) s' -
      sBell G i f h s μ) ^ 2)] at key
  refine le_trans (le_of_eq ?_) key
  refine sum_congr rfl fun j _ => ?_
  congr 1
  exact (sum_flat G h s (d j).prob (fun a s' => (G.reward i h s a + f (h + 1) s' -
      sBell G i f h s (d j)) ^ 2)).symm

/-! ### Products, deviations, averages -/

/-- `E_{⊗π}[F] = ∑_b π_i(b) E_{devDist (⊗π) i b}[F]`. -/
theorem sum_prodDist_eq_sum_dev (π : (i : Fin m) → FiniteDistribution (Fin (A i))) (i : Fin m)
    (F : JointAction m A → ℝ) :
    ∑ a, (prodDist π).prob a * F a =
      ∑ b, (π i).prob b * ∑ a, (devDist (prodDist π) i b).prob a * F a := by
  have hP : ∀ a, (prodDist π).prob a = jointProb (fun j _ _ => π j : ProductPolicy m 1 A) 0 0 a :=
    fun a => rfl
  simp_rw [devDist_sum, hP]
  rw [jointProb_sum_split (fun j _ _ => π j : ProductPolicy m 1 A) 0 0 i F]
  have hR : ∀ b, ∑ a', jointProb (fun j _ _ => π j : ProductPolicy m 1 A) 0 0 a' *
      F (Function.update a' i b) = ∑ r : (j : {j : Fin m // j ≠ i}) → Fin (A j),
        (∏ j : {j : Fin m // j ≠ i}, (π j).prob (r j)) *
          F ((Equiv.piSplitAt i (fun j => Fin (A j))).symm (b, r)) := by
    intro b
    rw [jointProb_sum_split (fun j _ _ => π j : ProductPolicy m 1 A) 0 0 i]
    refine sum_congr rfl fun r _ => ?_
    simp_rw [update_piSplitAt_symm]
    rw [← sum_mul, (π i).sum_prob, one_mul]
  simp_rw [hR, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun r _ => sum_congr rfl fun c _ => by ring

theorem devDist_avg {T : ℕ} (hT : 0 < T) (d : Fin T → FiniteDistribution (JointAction m A))
    (i : Fin m) (b : Fin (A i)) (a : JointAction m A) :
    (devDist (avgDist hT d) i b).prob a = ∑ t, (1 / (T : ℝ)) * (devDist (d t) i b).prob a := by
  simp only [devDist, avgDist]
  simp_rw [sum_div, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun a' _ => by ring

theorem avgDist_prob {Ω : Type*} [Fintype Ω] {T : ℕ} (hT : 0 < T) (d : Fin T → FiniteDistribution Ω)
    (o : Ω) : (avgDist hT d).prob o = ∑ t, (1 / (T : ℝ)) * (d t).prob o := by
  simp only [avgDist]; rw [← mul_sum]; ring

theorem deviate_pointMass_eq (π : JointPolicy m S A) (i : Fin m) (β : ℕ → Fin S → Fin (A i))
    (h : ℕ) (s : Fin S) :
    deviate π i (fun h s => EnvironmentStage.pointMass (β h s)) h s = devDist (π h s) i (β h s) := by
  refine FiniteDistribution.ext_prob fun a => ?_
  simp only [deviate, devDist]
  refine sum_congr rfl fun a' _ => ?_
  have := pointMass_sum (β h s) (fun b => (π h s).prob a' *
    (if Function.update a' i b = a then (1 : ℝ) else 0))
  rw [← this]
  refine sum_congr rfl fun b _ => by ring

/-! ### Linear identities for `sBell` and `sSec` -/

theorem sBell_avg {T : ℕ} (hT : 0 < T) (G : MarkovGame m S H A) (i : Fin m) (f : ℕ → Fin S → ℝ)
    (h : ℕ) (s : Fin S) (d : Fin T → FiniteDistribution (JointAction m A)) :
    sBell G i f h s (avgDist hT d) = (∑ t, sBell G i f h s (d t)) / T := by
  unfold sBell
  exact avgDist_sum hT d _

theorem sBell_devDist_avg {T : ℕ} (hT : 0 < T) (G : MarkovGame m S H A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S) (d : Fin T → FiniteDistribution (JointAction m A))
    (b : Fin (A i)) :
    sBell G i f h s (devDist (avgDist hT d) i b) = (∑ t, sBell G i f h s (devDist (d t) i b)) / T := by
  unfold sBell
  simp_rw [devDist_avg hT d i b, sum_mul]
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_div]
  exact sum_congr rfl fun a _ => by ring

theorem sBell_prod (G : MarkovGame m S H A) (i : Fin m) (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S)
    (π : (j : Fin m) → FiniteDistribution (Fin (A j))) :
    sBell G i f h s (prodDist π) = ∑ b, (π i).prob b * sBell G i f h s (devDist (prodDist π) i b) := by
  unfold sBell
  exact sum_prodDist_eq_sum_dev π i _

theorem sSec_prod (G : MarkovGame m S H A) (i : Fin m) (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S)
    (π : (j : Fin m) → FiniteDistribution (Fin (A j))) (c : ℝ) :
    sSec G i f h s (prodDist π) c =
      ∑ b, (π i).prob b * sSec G i f h s (devDist (prodDist π) i b) c := by
  unfold sSec
  exact sum_prodDist_eq_sum_dev π i _

/-- Average of round variances of the deviation `b` `≤` variance of the averaged deviation. -/
theorem sJvar_devDist_avg_ge {T : ℕ} (hT : 0 < T) (G : MarkovGame m S H A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S) (d : Fin T → FiniteDistribution (JointAction m A))
    (b : Fin (A i)) :
    (∑ t, sJvar G i f h s (devDist (d t) i b)) / T ≤ sJvar G i f h s (devDist (avgDist hT d) i b) := by
  have := sJvar_mix_ge G i f h s (fun _ : Fin T => 1 / (T : ℝ)) (fun _ => by positivity)
    (fun t => devDist (d t) i b) (devDist (avgDist hT d) i b) (devDist_avg hT d i b)
  rw [← mul_sum] at this
  rw [div_eq_mul_one_div, mul_comm]
  exact this

/-- Average of round variances `≤` variance of the average. -/
theorem sJvar_avg_ge {T : ℕ} (hT : 0 < T) (G : MarkovGame m S H A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (h : ℕ) (s : Fin S) (d : Fin T → FiniteDistribution (JointAction m A)) :
    (∑ t, sJvar G i f h s (d t)) / T ≤ sJvar G i f h s (avgDist hT d) := by
  have := sJvar_mix_ge G i f h s (fun _ : Fin T => 1 / (T : ℝ)) (fun _ => by positivity)
    d (avgDist hT d) (avgDist_prob hT d)
  rw [← mul_sum] at this
  rw [div_eq_mul_one_div, mul_comm]
  exact this

/-! ### Range of the algorithm's values -/

/-- Rewards in `[0,1]` on steps `1..H`. -/
def Alg.RewOK (al : Alg m S H A) : Prop :=
  ∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ al.rew i h s a ∧ al.rew i h s a ≤ 1

theorem Alg.rew_stage (al : Alg m S H A) (hr : al.RewOK) (c : Fin H) (i : Fin m) (s : Fin S)
    (a : JointAction m A) : 0 ≤ al.rew i (H - c) s a ∧ al.rew i (H - c) s a ≤ 1 :=
  hr i (H - c) s a (by have := c.isLt; omega) (by omega)

theorem wmean_nonneg {n : ℕ} (p : FiniteDistribution (Fin n)) (q : Fin n → ℝ) (hq : ∀ b, 0 ≤ q b) :
    0 ≤ wmean p q := sum_nonneg fun b _ => mul_nonneg (p.prob_nonneg b) (hq b)

theorem Alg.bonus_nonneg (al : Alg m S H A) (hη : 0 < al.η) (V : Fin m → Fin S → ℝ)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (i : Fin m) :
    0 ≤ al.bonus V x c s i := by
  unfold bonus
  have hA : (1 : ℝ) ≤ A i := by exact_mod_cast al.hA i
  have hT : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  refine add_nonneg (div_nonneg (Real.log_nonneg hA) (by positivity)) (mul_nonneg (by positivity)
    (sum_nonneg fun t _ => wvar_nonneg _ _))

/-- `0 ≤ vb x c ≤ c`. -/
theorem Alg.vb_mem (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η)
    (x : Fin al.N → Entry m S H A) : ∀ c i s, 0 ≤ al.vb x c i s ∧ al.vb x c i s ≤ c := by
  intro c
  induction c with
  | zero => intro i s; simp [Alg.vb]
  | succ c ih =>
    intro i s
    simp only [Alg.vb]
    split_ifs with hc
    · simp only [Alg.stageV]
      have hU : 0 ≤ al.optU (al.vb x c) x ⟨c, hc⟩ s i := by
        unfold Alg.optU
        refine add_nonneg (div_nonneg (sum_nonneg fun t _ => wmean_nonneg _ _ fun b => ?_)
          (Nat.cast_nonneg _)) (al.bonus_nonneg hη _ x _ s i)
        unfold Alg.gain
        split_ifs
        · exact add_nonneg (al.rew_stage hr ⟨c, hc⟩ i s _).1 (ih i _).1
        · exact le_rfl
      constructor
      · exact le_min (by positivity) hU
      · push_cast; exact min_le_left _ _
    · simp only [le_refl, true_and]; positivity

theorem Alg.gz_mem (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (i : Fin m) (z : Entry m S H A) :
    0 ≤ al.gz (al.vb x c) c s i z ∧ al.gz (al.vb x c) c s i z ≤ (c : ℝ) + 1 := by
  have h1 := al.rew_stage hr c i s z.1.2.2
  have h2 := al.vb_mem hr hη x c i z.2
  unfold Alg.gz
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end StatisticalRL.Ch7Rest.Marl77
