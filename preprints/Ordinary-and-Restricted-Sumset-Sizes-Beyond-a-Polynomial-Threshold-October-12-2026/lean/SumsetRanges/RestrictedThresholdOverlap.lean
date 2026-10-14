import SumsetRanges.LargeParameters

namespace SumsetRanges

def restrictedDenominator (h : ℕ) : ℕ := 64*(2*h-1)*h

noncomputable def overlapEndpoint (h k : ℕ) : ℕ := 4*k*(sparseThreshold k)^(h-1)

theorem restrictedDenominator_bound (h : ℕ) (hh : 2≤h) :
    restrictedDenominator h ≤ (2*h)^7 := by
  have hp : h^2≤h^7 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold restrictedDenominator
  rw [mul_pow]
  norm_num
  nlinarith [Nat.sub_le (2*h) 1]

theorem threshold_ratio_bound (h k : ℕ) (hh : 2≤h) (hk : (2*h)^80≤k) :
    (8*restrictedDenominator h)^2*sparseThreshold k≤k := by
  have hD := restrictedDenominator_bound h hh
  have hb : 8≤(2*h)^2 := by nlinarith
  have hA : (8*restrictedDenominator h)^2≤(2*h)^24 := by
    calc
      _ ≤ ((2*h)^2*(2*h)^7)^2 := Nat.pow_le_pow_left (Nat.mul_le_mul hb hD) _
      _ = (2*h)^18 := by rw [←pow_add,←pow_mul]
      _ ≤ (2*h)^24 := Nat.pow_le_pow_right (by omega) (by omega)
  have kp : 0<k := lt_of_lt_of_le (by positivity) hk
  have hr : (((2*h:ℕ)^80:ℕ):ℝ)^((3:ℝ)/10)=((2*h:ℕ):ℝ)^24 := by
    push_cast
    rw [←Real.rpow_natCast_mul (by positivity)]
    norm_num
  have hrb := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(((2*h:ℕ)^80:ℕ):ℝ))
    (show (((2*h:ℕ)^80:ℕ):ℝ)≤k by exact_mod_cast hk) (by norm_num : (0:ℝ)≤3/10)
  rw [hr] at hrb
  have hAr : (((8*restrictedDenominator h)^2:ℕ):ℝ)≤(k:ℝ)^((3:ℝ)/10) :=
    (show (((8*restrictedDenominator h)^2:ℕ):ℝ)≤((2*h:ℕ):ℝ)^24 by exact_mod_cast hA).trans hrb
  have hKr : (sparseThreshold k:ℝ)≤(k:ℝ)^((7:ℝ)/10) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have he : (k:ℝ)^((3:ℝ)/10)*(k:ℝ)^((7:ℝ)/10)=(k:ℝ) := by
    rw [←Real.rpow_add (by exact_mod_cast kp)]
    norm_num
  have hp := mul_le_mul hAr hKr (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  rw [he] at hp
  exact_mod_cast hp

/-- A stronger elementary ratio estimate supplies all powers in the small-range overlap. -/
theorem overlap_power_bound (h k D K : ℕ) (hh : 2≤h) (hk : 2≤k) (hD : 1≤D)
    (hr : (8*D)^2*K≤k) : D^h*(4*k*K^(h-1))≤(k-1)^h := by
  have hp := Nat.pow_le_pow_left hr (h-1)
  have he : h≤2*(h-1) := by omega
  have hpow : (8*D)^h≤((8*D)^2)^(h-1) := by
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by omega) he
  have hfour : 4≤4^h := by
    simpa using Nat.pow_le_pow_right (by decide : 0<4) (show 1≤h by omega)
  have ha : 4*(2*D)^h≤(8*D)^h := by
    calc
      _ ≤ 4^h*(2*D)^h := Nat.mul_le_mul_right _ hfour
      _ = (8*D)^h := by rw [←mul_pow]; congr 1; ring
  have ha' : 4*(2*D)^h*K^(h-1)≤k^(h-1) := by
    calc
      _ ≤ ((8*D)^2)^(h-1)*K^(h-1) := Nat.mul_le_mul_right _ (ha.trans hpow)
      _ = ((8*D)^2*K)^(h-1) := (mul_pow _ _ _).symm
      _ ≤ _ := hp
  have ha'' := Nat.mul_le_mul_right k ha'
  have hpred : k≤2*(k-1) := by omega
  have hkpow := Nat.pow_le_pow_left hpred h
  have kh : k^(h-1)*k=k^h := by rw [←pow_succ]; congr 1; omega
  rw [kh] at ha''
  have hfinal : 2^h*(D^h*(4*k*K^(h-1)))≤2^h*(k-1)^h := by
    calc
      _ = (4*(2*D)^h*K^(h-1))*k := by rw [mul_pow]; ring
      _ ≤ k^h := ha''
      _ ≤ (2*(k-1))^h := hkpow
      _ = _ := mul_pow _ _ _
  exact Nat.le_of_mul_le_mul_left hfinal (by positivity)

theorem restricted_threshold_elementary (h k : ℕ) (hh : 2≤h) (hk : (2*h)^80≤k) :
    restrictedDenominator h+1≤k ∧ h^2+2≤k ∧ h+2≤k := by
  have hp : (2*h)^8≤k := (Nat.pow_le_pow_right (by omega) (by omega : 8≤80)).trans hk
  have hD := restrictedDenominator_bound h hh
  have hbase : 2≤2*h := by omega
  have hpow : 1≤(2*h)^7 := Nat.one_le_pow _ _ (by omega)
  have hp2 : (2*h)^2≤(2*h)^7 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_succ] at hp
  have he : (2*h)^2=4*h^2 := by ring
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem overlapEndpoint_properties (h k : ℕ) (hh : 2≤h) (hk : (2*h)^80≤k) :
    k-2≤overlapEndpoint h k ∧
    (restrictedDenominator h)^h*overlapEndpoint h k≤(2*h-1)*(k-1)^h ∧
    3*h*k*(sparseThreshold k)^(h-1)≤h*overlapEndpoint h k+h-(h-1)^2+1 ∧
    h+overlapEndpoint h k≤k^h := by
  have hel := restricted_threshold_elementary h k hh hk
  have hD : 1≤restrictedDenominator h := by
    unfold restrictedDenominator
    have hl : 1≤2*h-1 := by omega
    nlinarith
  have hK : 1≤sparseThreshold k := by
    have hlarge := sparseThreshold_large hh hk
    have hc : 1≤(32*h^3)^10 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hKpow : 1≤(sparseThreshold k)^(h-1) := Nat.one_le_pow _ _ hK
  have hpow := overlap_power_bound h k (restrictedDenominator h) (sparseThreshold k)
    hh (by omega) hD (threshold_ratio_bound h k hh hk)
  change (restrictedDenominator h)^h*overlapEndpoint h k≤(k-1)^h at hpow
  have hDp : 1≤(restrictedDenominator h)^h := Nat.one_le_pow _ _ hD
  have hM : overlapEndpoint h k≤(k-1)^h := by nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · unfold overlapEndpoint
    have hb : k≤k*(sparseThreshold k)^(h-1) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith [Nat.sub_le k 2]
  · exact hpow.trans (Nat.le_mul_of_pos_left _ (by omega))
  · have hsq : (h-1)^2≤h^2 := Nat.pow_le_pow_left (Nat.sub_le _ _) _
    have hbig : k≤k*(sparseThreshold k)^(h-1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold overlapEndpoint
    have hdiff : (h-1)^2≤h*k*(sparseThreshold k)^(h-1) := by nlinarith [hel.2.1]
    have he1 : 3*h*k*(sparseThreshold k)^(h-1)=3*(h*k*(sparseThreshold k)^(h-1)) := by ring
    have he2 : h*(4*k*(sparseThreshold k)^(h-1))=4*(h*k*(sparseThreshold k)^(h-1)) := by ring
    rw [he1,he2]
    omega
  · have hkh : h≤k-1 := by omega
    have hp : h≤(k-1)^(h-1) := by
      calc
        h ≤ k-1 := hkh
        _ ≤ (k-1)^(h-1) := by
          simpa using Nat.pow_le_pow_right (by omega : 0<k-1) (show 1≤h-1 by omega)
    have hkp : k*(k-1)^(h-1)≤k^h := by
      calc
        _ ≤ k*k^(h-1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
        _ = k^h := by rw [←pow_succ']; congr 1; omega
    have he : (k-1)^h+(k-1)^(h-1)=k*(k-1)^(h-1) := by
      conv_lhs => lhs; rw [show h=h-1+1 by omega,pow_succ]
      have hk' : k-1+1=k := by omega
      nlinarith
    omega

end SumsetRanges
