import Formalization.Online.Regret.MVP.MVPProfileDefinitions
import Mathlib.Data.Sym.Card
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Finite cardinality bound for the source's monotone total-profile family. -/
namespace StatisticalRL.OnlineRL.MVPProfile

open scoped BigOperators

/-- The symmetric-power encoding forgets order; monotonicity makes the sorted
list recover the original profile. -/
noncomputable def encodeMonotoneRowProfile {K J : ℕ}
    (f : MonotoneRowProfile K J) : Sym (Fin (J + 1)) K :=
  Sym.ofVector (List.Vector.ofFn f.1)

theorem encodeMonotoneRowProfile_injective {K J : ℕ} :
    Function.Injective (encodeMonotoneRowProfile (K := K) (J := J)) := by
  intro f g hfg
  have hm : ((encodeMonotoneRowProfile f : Sym (Fin (J + 1)) K) : Multiset (Fin (J + 1))) =
      ((encodeMonotoneRowProfile g : Sym (Fin (J + 1)) K) : Multiset (Fin (J + 1))) :=
    congrArg (fun x : Sym (Fin (J + 1)) K => (x : Multiset (Fin (J + 1))) ) hfg
  have hm' : (List.ofFn f.1 : Multiset (Fin (J + 1))) = List.ofFn g.1 := by
    change ((List.Vector.ofFn f.1).toList : Multiset (Fin (J + 1))) =
      (List.Vector.ofFn g.1).toList at hm
    simpa only [List.Vector.toList_ofFn] using hm
  have hp : (List.ofFn f.1).Perm (List.ofFn g.1) := Multiset.coe_eq_coe.mp hm'
  have hs₁ : (List.ofFn f.1).SortedLE := f.2.sortedLE_ofFn
  have hs₂ : (List.ofFn g.1).SortedLE := g.2.sortedLE_ofFn
  have hl : List.ofFn f.1 = List.ofFn g.1 :=
    List.Perm.eq_of_pairwise' hs₁.pairwise hs₂.pairwise hp
  apply Subtype.ext
  exact List.ofFn_inj.mp hl

theorem monotoneRowProfile_card_le_choose (K J : ℕ) :
    Fintype.card (MonotoneRowProfile K J) ≤ (K + J).choose J := by
  classical
  calc
    Fintype.card (MonotoneRowProfile K J) ≤ Fintype.card (Sym (Fin (J + 1)) K) :=
      Fintype.card_le_of_injective _ encodeMonotoneRowProfile_injective
    _ = (K + J).choose J := by
      rw [Sym.card_sym_eq_choose]
      have hcard : Fintype.card (Fin (J + 1)) = J + 1 := by simp
      rw [hcard]
      have hindex : J + 1 + K - 1 = K + J := by omega
      rw [hindex]
      exact Nat.choose_symm_of_eq_add (n := K + J) (a := K) (b := J) (by omega)

noncomputable def monotoneProfilesToRows {K d J : ℕ}
    (p : MonotoneProfiles K d J) : Fin d → MonotoneRowProfile K J :=
  fun r => ⟨fun k => p.val k r, p.property r⟩

theorem monotoneProfilesToRows_injective {K d J : ℕ} :
    Function.Injective (monotoneProfilesToRows (K := K) (d := d) (J := J)) := by
  intro p q hpq
  apply Subtype.ext
  funext k r
  have h := congrFun hpq r
  exact congrFun (congrArg Subtype.val h) k

/-- One factorial comparison for the stars-and-bars estimate. -/
theorem two_pow_pred_le_factorial (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ n.factorial := by
  have h := Nat.factorial_mul_pow_le_factorial (m := 1) (n := n - 1)
  have hsum : 1 + (n - 1) = n := by omega
  simpa [Nat.factorial_one, hsum] using h

theorem profileLevelCap_bounds (K : ℕ) (hK : 2 ≤ K) :
    1 ≤ profileLevelCap K ∧ profileLevelCap K ≤ K ∧
      (profileLevelCap K : ℝ) ≤ logTwoReal K + 1 ∧ 1 ≤ logTwoReal K := by
  have hKpos : 0 < (K : ℝ) := by positivity
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (1 : ℝ) ≤ logTwoReal K := by
    unfold logTwoReal
    apply (le_div_iff₀ htwo).2
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (K : ℝ) by exact_mod_cast hK)
    simpa using hmono
  have hNatMono : Nat.log2 (K - 1) ≤ Nat.log2 K :=
    by simpa only [Nat.log2_eq_log_two] using
      (Nat.log_mono_right (b := 2) (by omega : K - 1 ≤ K))
  have hlogReal : (Nat.log2 K : ℝ) ≤ logTwoReal K := by
    unfold logTwoReal
    rw [Real.log_div_log]
    apply (Real.le_logb_iff_rpow_le (by norm_num) hKpos).2
    rw [Real.rpow_natCast]
    exact_mod_cast (by
      simpa only [Nat.log2_eq_log_two] using
        (Nat.pow_log_le_self 2 (by omega : K ≠ 0)))
  constructor
  · dsimp [profileLevelCap]
    omega
  constructor
  · dsimp [profileLevelCap]
    have hself : Nat.log2 (K - 1) ≤ K - 1 := by
      simpa [Nat.log2_eq_log_two] using (Nat.log_le_self 2 (K - 1))
    omega
  constructor
  · dsimp [profileLevelCap]
    have hreal : (Nat.log2 (K - 1) : ℝ) ≤ (Nat.log2 K : ℝ) := by exact_mod_cast hNatMono
    have hcap : ((Nat.log2 (K - 1) + 1 : ℕ) : ℝ) ≤ (Nat.log2 K : ℝ) + 1 := by
      exact_mod_cast (Nat.add_le_add_right hNatMono 1)
    linarith
  · exact hlog2

/-- Real form of the one-row stars-and-bars estimate, with the source's
integer ceiling level. -/
theorem monotoneRowProfile_card_real_bound (K : ℕ) (hK : 2 ≤ K) :
    (Fintype.card (MonotoneRowProfile K (profileLevelCap K)) : ℝ) ≤
      (4 * (K : ℝ)) ^ logTwoReal K := by
  classical
  let J := profileLevelCap K
  have hJ := profileLevelCap_bounds K hK
  have hJpos : 1 ≤ J := hJ.1
  have hJleK : J ≤ K := hJ.2.1
  have hJreal : (J : ℝ) ≤ logTwoReal K + 1 := hJ.2.2.1
  have hL : 1 ≤ logTwoReal K := hJ.2.2.2
  have hchoose := monotoneRowProfile_card_le_choose K J
  have hchooseR : (Fintype.card (MonotoneRowProfile K J) : ℝ) ≤
      ((K + J).choose J : ℝ) := by exact_mod_cast hchoose
  have hKJ : (K + J : ℕ) ≤ 2 * K := by omega
  have hnum : ((K + J : ℕ) : ℝ) ^ J ≤ ((2 * K : ℕ) : ℝ) ^ J := by
    exact_mod_cast (Nat.pow_le_pow_left hKJ J)
  have hfacNat := two_pow_pred_le_factorial J hJpos
  have hfac : (2 : ℝ) ^ (J - 1) ≤ (J.factorial : ℝ) := by exact_mod_cast hfacNat
  have hpowpos : 0 < (2 : ℝ) ^ (J - 1) := by positivity
  have hfactpos : 0 < (J.factorial : ℝ) := by positivity
  have hchooseSmall : ((K + J).choose J : ℝ) ≤ 2 * (K : ℝ) ^ J := by
    have hchoosePow := Nat.choose_le_pow_div (α := ℝ) J (K + J)
    have hdiv : (((K + J).choose J : ℝ)) ≤
        ((K + J : ℕ) : ℝ) ^ J / (J.factorial : ℝ) := hchoosePow
    have hratio : ((K + J : ℕ) : ℝ) ^ J / (J.factorial : ℝ) ≤
        ((2 * K : ℕ) : ℝ) ^ J / (2 : ℝ) ^ (J - 1) := by
      rw [div_le_div_iff₀ hfactpos hpowpos]
      exact mul_le_mul hnum hfac (by positivity) (by positivity)
    have hcancel : ((2 * K : ℕ) : ℝ) ^ J / (2 : ℝ) ^ (J - 1) =
        2 * (K : ℝ) ^ J := by
      have hKcast : ((2 * K : ℕ) : ℝ) = 2 * (K : ℝ) := by norm_num
      rw [hKcast, mul_pow]
      have hJdecomp : J = (J - 1) + 1 := by omega
      rw [hJdecomp, pow_add]
      have hsub : (J - 1) + 1 - 1 = J - 1 := by omega
      rw [hsub]
      field_simp
    exact hdiv.trans (hratio.trans_eq hcancel)
  have hKpos : (0 : ℝ) < (K : ℝ) := by positivity
  have hKge2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hLlog : logTwoReal K = Real.logb 2 K := by
    unfold logTwoReal
    exact Real.log_div_log
  have htwoPow : (2 : ℝ) ^ logTwoReal K = K := by
    rw [hLlog]
    exact Real.rpow_logb (by norm_num) (by norm_num) hKpos
  have hfourPow : (4 : ℝ) ^ logTwoReal K = (K : ℝ) ^ 2 := by
    calc
      (4 : ℝ) ^ logTwoReal K = ((2 : ℝ) * 2) ^ logTwoReal K := by norm_num
      _ = (2 : ℝ) ^ logTwoReal K * (2 : ℝ) ^ logTwoReal K :=
        Real.mul_rpow (by norm_num) (by norm_num)
      _ = (K : ℝ) ^ 2 := by rw [htwoPow]; ring
  have hfourK : ((4 : ℝ) * K) ^ logTwoReal K =
      (K : ℝ) ^ 2 * (K : ℝ) ^ logTwoReal K := by
    rw [Real.mul_rpow (by norm_num) (by positivity), hfourPow]
  have hJpow : (K : ℝ) ^ J ≤ (K : ℝ) ^ (logTwoReal K + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ (K : ℝ) by linarith) hJreal
  have hsmall : 2 * (K : ℝ) ^ (logTwoReal K + 1) ≤
      (4 * (K : ℝ)) ^ logTwoReal K := by
    rw [Real.rpow_add hKpos]
    rw [hfourK]
    have hscalar : 2 * (K : ℝ) ≤ (K : ℝ) ^ 2 := by
      have hKm : 0 ≤ (K : ℝ) - 2 := by linarith
      nlinarith [mul_nonneg (le_of_lt hKpos) hKm]
    have hpowNonneg : 0 ≤ (K : ℝ) ^ logTwoReal K := by positivity
    rw [Real.rpow_one]
    calc
      2 * ((K : ℝ) ^ logTwoReal K * K) =
          (K : ℝ) ^ logTwoReal K * (2 * (K : ℝ)) := by ring
      _ ≤ (K : ℝ) ^ logTwoReal K * ((K : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hscalar hpowNonneg
      _ = (K : ℝ) ^ 2 * (K : ℝ) ^ logTwoReal K := by ring
  have hJuse : 2 * (K : ℝ) ^ J ≤ 2 * (K : ℝ) ^ (logTwoReal K + 1) :=
    mul_le_mul_of_nonneg_left hJpow (by norm_num)
  calc
    (Fintype.card (MonotoneRowProfile K J) : ℝ) ≤
        ((K + J).choose J : ℝ) := hchooseR
    _ ≤ 2 * (K : ℝ) ^ J := hchooseSmall
    _ ≤ 2 * (K : ℝ) ^ (logTwoReal K + 1) := hJuse
    _ ≤ (4 * (K : ℝ)) ^ logTwoReal K := hsmall

end StatisticalRL.OnlineRL.MVPProfile
