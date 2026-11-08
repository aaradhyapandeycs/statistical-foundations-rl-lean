import Formalization.Ch7Rest.Marl76Defs
import Formalization.Ch7Rest.Marl78Product
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Existence of a coarse correlated equilibrium of a finite normal-form game

`stageCCE_exists`: for payoffs `u_i : 𝒜 → ℝ` on the joint actions of `m` players with nonempty
finite action sets, there is a distribution `x` on joint actions with no profitable unilateral
deviation to any fixed action:
`∑_a x(a) u_i(a_{-i}, b) ≤ ∑_a x(a) u_i(a)` for every `i` and `b`.

Proof by strict separation (`geometric_hahn_banach_compact_closed`) of the compact convex image
of the simplex under the deviation-gain map from the closed convex cone `{z ≤ 0}`: a separating
functional has nonpositive weights `w_{i,b}`, but at the product distribution with marginals
`q_i ∝ w_{i,·}` its value is exactly `0`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

variable {m : ℕ} {A : Fin m → ℕ}

/-- `x` is a coarse correlated equilibrium of the normal-form game `u`. -/
def IsStageCCE (u : Fin m → JointAction m A → ℝ) (x : FiniteDistribution (JointAction m A)) :
    Prop :=
  ∀ (i : Fin m) (b : Fin (A i)),
    ∑ a, x.prob a * u i (Function.update a i b) ≤ ∑ a, x.prob a * u i a

/-- Deviating to the own marginal of a product distribution changes nothing. -/
theorem product_deviation_identity (q : (i : Fin m) → FiniteDistribution (Fin (A i))) (i : Fin m)
    (g : JointAction m A → ℝ) :
    ∑ a', ∑ b, (toJoint (S := 1) (fun j _ _ => q j) 0 0).prob a' * (q i).prob b *
        g (Function.update a' i b) =
      ∑ a, (toJoint (S := 1) (fun j _ _ => q j) 0 0).prob a * g a := by
  let π : ProductPolicy m 1 A := fun j _ _ => q j
  have h1 := deviate_sum (toJoint π) i (π i) 0 0 g
  have h2 := deviate_toJoint_sum π i (π i) 0 0 g
  rw [Function.update_eq_self] at h2
  rw [← h1, h2]

/-- The deviation-gain map `x ↦ (∑_a x(a) (u_i(a_{-i}, b) − u_i(a)))_{(i,b)}`. -/
noncomputable def gainMap (u : Fin m → JointAction m A → ℝ) :
    (JointAction m A → ℝ) →ₗ[ℝ] ((k : Σ i : Fin m, Fin (A i)) → ℝ) where
  toFun x k := ∑ a, x a * (u k.1 (Function.update a k.1 k.2) - u k.1 a)
  map_add' x y := by
    funext k
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem stageCCE_exists (u : Fin m → JointAction m A → ℝ) (hA : ∀ i, 0 < A i) :
    ∃ x : FiniteDistribution (JointAction m A), IsStageCCE u x := by
  classical
  by_contra hno
  push_neg at hno
  set E := (k : Σ i : Fin m, Fin (A i)) → ℝ
  set L := gainMap u
  set M : Set E := L '' stdSimplex ℝ (JointAction m A)
  set C : Set E := {z | ∀ k, z k ≤ 0}
  have hMconv : Convex ℝ M := (convex_stdSimplex ℝ _).linear_image L
  have hMcomp : IsCompact M :=
    (isCompact_stdSimplex _).image L.continuous_of_finiteDimensional
  have hCconv : Convex ℝ C := by
    intro z hz z' hz' a b ha hb _ k
    change a * z k + b * z' k ≤ 0
    nlinarith [hz k, hz' k]
  have hCclosed : IsClosed C := by
    have : C = ⋂ k, {z : E | z k ≤ 0} := by ext z; simp [C]
    rw [this]
    exact isClosed_iInter fun k => isClosed_le (continuous_apply k) continuous_const
  have hdisj : Disjoint M C := by
    rw [Set.disjoint_left]
    rintro z ⟨p, hp, rfl⟩ hz
    let x : FiniteDistribution (JointAction m A) := ⟨p, hp.1, hp.2⟩
    have hx := hno x
    simp only [IsStageCCE, not_forall, not_le] at hx
    obtain ⟨i, b, hib⟩ := hx
    have := hz ⟨i, b⟩
    simp only [L, gainMap, LinearMap.coe_mk, AddHom.coe_mk, mul_sub, Finset.sum_sub_distrib] at this
    change ∑ a, p a * u i a < ∑ a, p a * u i (Function.update a i b) at hib
    linarith
  obtain ⟨f, u₀, v₀, hfM, huv, hfC⟩ :=
    geometric_hahn_banach_compact_closed hMconv hMcomp hCconv hCclosed hdisj
  -- the weights of `f`
  let e : (Σ i : Fin m, Fin (A i)) → E := fun k j => if k = j then 1 else 0
  let w : (Σ i : Fin m, Fin (A i)) → ℝ := fun k => f (e k)
  have hf : ∀ z : E, f z = ∑ k, z k * w k := by
    intro z
    conv_lhs => rw [pi_eq_sum_univ z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
  have hv0 : v₀ < 0 := by
    have := hfC 0 (fun k => le_rfl)
    rwa [map_zero] at this
  have hw : ∀ k, w k ≤ 0 := by
    intro k
    by_contra hk
    push_neg at hk
    let c : ℝ := -((1 - v₀) / w k)
    have hc : c ≤ 0 := by
      have : 0 < (1 - v₀) / w k := div_pos (by linarith) hk
      simp only [c]; linarith
    have hmem : c • e k ∈ C := by
      intro j
      change c * (if k = j then (1 : ℝ) else 0) ≤ 0
      split_ifs <;> simp [hc]
    have h1 := hfC _ hmem
    rw [map_smul, smul_eq_mul] at h1
    have h2 : c * w k = -(1 - v₀) := by
      simp only [c]; field_simp
    simp only [w] at h2
    linarith
  -- the product distribution with marginals proportional to the weights
  let W : Fin m → ℝ := fun i => ∑ b, w ⟨i, b⟩
  have hW : ∀ i, W i ≤ 0 := fun i => Finset.sum_nonpos fun b _ => hw ⟨i, b⟩
  let q : (i : Fin m) → FiniteDistribution (Fin (A i)) := fun i =>
    if hWi : W i = 0 then EnvironmentStage.pointMass ⟨0, hA i⟩
    else
      { prob := fun b => w ⟨i, b⟩ / W i
        prob_nonneg := fun b => by
          have h1 := hw ⟨i, b⟩
          have h2 : W i < 0 := lt_of_le_of_ne (hW i) hWi
          exact div_nonneg_of_nonpos h1 h2.le
        sum_prob := by
          rw [← Finset.sum_div]
          exact div_self hWi }
  set xs := toJoint (S := 1) (fun j _ _ => q j) 0 0
  have hzero : ∀ i, ∑ b, w ⟨i, b⟩ * ∑ a, xs.prob a * (u i (Function.update a i b) - u i a) = 0 := by
    intro i
    by_cases hWi : W i = 0
    · have hw0 : ∀ b, w ⟨i, b⟩ = 0 := by
        intro b
        have hle : ∀ b' ∈ Finset.univ, w ⟨i, b'⟩ ≤ 0 := fun b' _ => hw ⟨i, b'⟩
        have := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hWi b (Finset.mem_univ b)
        exact this
      simp [hw0]
    · have hq : ∀ b, w ⟨i, b⟩ = W i * (q i).prob b := by
        intro b
        simp only [q, dif_neg hWi]
        field_simp
      have hid := product_deviation_identity q i (u i)
      have : ∑ b, (q i).prob b * ∑ a, xs.prob a * (u i (Function.update a i b) - u i a) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        have e1 : ∑ b, ∑ a, (q i).prob b * (xs.prob a * u i (Function.update a i b)) =
            ∑ a, xs.prob a * u i a := by
          rw [← hid, Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          ring
        have e2 : ∑ b, ∑ a, (q i).prob b * (xs.prob a * u i a) = ∑ a, xs.prob a * u i a := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_mul, (q i).sum_prob, one_mul]
        rw [e1, e2, sub_self]
      simp_rw [hq, mul_assoc]
      rw [← Finset.mul_sum, this, mul_zero]
  have hxsimp : (fun a => xs.prob a) ∈ stdSimplex ℝ (JointAction m A) :=
    ⟨xs.prob_nonneg, xs.sum_prob⟩
  have hlt := hfM (L fun a => xs.prob a) ⟨_, hxsimp, rfl⟩
  rw [hf] at hlt
  have hval : ∑ k, (L fun a => xs.prob a) k * w k = 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hzero i]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [L, gainMap, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  rw [hval] at hlt
  linarith

end StatisticalRL.Ch7Rest.Marl76
