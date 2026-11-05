import Formalization.Online.Regret.MVP.Probability.MVPSplitLogBudget
import Formalization.Online.Regret.MVP.Probability.MVPUnionLogAbsorption
import Formalization.Online.Regret.MVP.Probability.MVPRadiusAbsorption
import Formalization.Online.Regret.MVP.Probability.MVPLogNaturalBounds

/-! stronger radius: quarter failure budget, source iota unchanged. -/
namespace StatisticalRL.OnlineRL

theorem mvp_sourceRadius_quarter_bound (P δ H V : ℝ) (d K n : ℕ)
    (hP : 1 ≤ P) (hδ : 0 < δ) (hδsmall : δ ≤ 1/100)
    (hd : 1 ≤ d) (hK : 2 ≤ K) (hn : 0 < n) (hnK : n ≤ K)
    (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hcard : P ≤ (4*(d:ℝ)*K) ^ ((d:ℝ)*(Real.log K/Real.log 2)+1)) :
    let x := Real.log K/Real.log 2
    let I := 40000*x^3*Real.log (3*d)*Real.log (1/δ)
    let p := mvpUniformPeels d K
    let J := Nat.log2 K
    let L := Real.log (2*p*(P*((K:ℝ)+1)^d*J*2^d)/(δ/4))
    (Real.sqrt (8 * max ((n:ℝ)*V)
      (((n:ℝ)*d*H^2)/(2:ℝ)^p) * L) + (4/3)*H*L) / n ≤
        Real.sqrt ((d:ℝ)*I*V/(16*n*x)) + (d:ℝ)*H*I/(16*n*x) := by
  let x := Real.log K/Real.log 2
  let I := 40000*x^3*Real.log (3*d)*Real.log (1/δ)
  let p := mvpUniformPeels d K
  let J := Nat.log2 K
  let N : ℝ := P*((K:ℝ)+1)^d*J*2^d
  let L := Real.log (2*p*N/(δ/4))
  have hP0 : 0 < P := by linarith
  have hd0 : 0 ≤ (d:ℝ) := by positivity
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hKpos : 0 < K := by omega
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hp : 0 < p := mvpUniformPeels_pos d K
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hJpos : 0 < J := by
    dsimp [J]
    have h : 1 ≤ Nat.log2 K := (Nat.le_log2 (by omega)).2 (by simpa using hK)
    omega
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast hJpos
  have hJle : (J:ℝ) ≤ K := by exact_mod_cast mvp_log2_le_K K
  have hple : (p:ℝ) ≤ d*K := by exact_mod_cast mvpUniformPeels_le d K hd hK
  have hx : 0 < x := by
    dsimp [x]
    exact div_pos (Real.log_pos (by exact_mod_cast hK)) (Real.log_pos (by norm_num))
  have hq : 1 ≤ Real.log (1/δ) := onlineSmallConfidence_log_ge_one δ hδ hδsmall
  have hI : 0 ≤ I := by
    dsimp [I]
    have hz : 0 ≤ Real.log (3*(d:ℝ)) := Real.log_nonneg (by nlinarith)
    positivity
  have hN : 1 ≤ N := by
    dsimp [N]
    have hK1 : (1:ℝ) ≤ (K:ℝ)+1 := by
      have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
      linarith
    have hpow1 : (1:ℝ) ≤ ((K:ℝ)+1)^d := one_le_pow₀ hK1
    have hpow2 : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
    calc
      1 = 1*1*1*1 := by norm_num
      _ ≤ P*((K:ℝ)+1)^d*J*2^d := by gcongr
  have hδq : 0 < δ/4 := by positivity
  have hδqsmall : δ/4 ≤ 1/100 := by linarith only [hδsmall]
  have hL : 1 ≤ L := by
    have hratio : 1/(δ/4) ≤ 2*(p:ℝ)*N/(δ/4) := by
      apply (div_le_div_iff_of_pos_right hδq).2
      nlinarith
    have hlog := Real.log_le_log (one_div_pos.mpr hδq) hratio
    have hmin := onlineSmallConfidence_log_ge_one (δ/4) hδq hδqsmall
    dsimp [L]
    linarith
  have hpeel : (n:ℝ)*(d:ℝ) ≤ (2:ℝ)^p := by
    exact_mod_cast mvpUniformPeels_cover d K n hnK
  have hfloor : ((n:ℝ)*d*H^2)/(2:ℝ)^p ≤ H^2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^p)).2
    nlinarith [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hpeel)]
  have hbudget : 32*L*x ≤ (d:ℝ)*(I/4) := by
    have hs : 128*L*x ≤ (d:ℝ)*I := by
      simpa [L,N,p,J,x,I] using
        mvp_unionLog_quarter_absorbed P J p δ d K hP0
          (by exact_mod_cast hJpos) (by exact_mod_cast hp)
          hδ hδsmall hd hK hJle hple hcard
    nlinarith only [hs]
  have hraw := mvp_radius_absorb d x (I/4) n H L V
    (((n:ℝ)*d*H^2)/(2:ℝ)^p) hd0 hx (by positivity) hn0 hH hL hV hfloor hbudget
  have heq : (d:ℝ)*(I/4)*V/(4*(n:ℝ)*x) = (d:ℝ)*I*V/(16*(n:ℝ)*x) := by ring
  have heqH : (d:ℝ)*H*(I/4)/(4*(n:ℝ)*x) = (d:ℝ)*H*I/(16*(n:ℝ)*x) := by ring
  rw [heq,heqH] at hraw
  exact hraw
end StatisticalRL.OnlineRL
