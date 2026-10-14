import SumsetRanges.OrdinaryStepCoefficients
import SumsetRanges.OrdinaryDenseBounds
import SumsetRanges.DenseConvolutionBounds

open Finset
namespace SumsetRanges

theorem ordinary_dense_convolution_bound (h c b D ell : ℕ) (γ δ : ℕ → ℤ)
    (hh : 1≤h) (hc : 2*h^3≤c) (hD : D≤h)
    (hg0 : γ 0=1) (hg1 : γ 1=b)
    (hgn : ∀ e≤D,0≤γ e) (hgb : ∀ e∈Icc 2 D,γ e≤h^2*b)
    (hdn : ∀ d≤D,0≤δ d)
    (hdl : ∀ d≤D,(ell : ℤ)*(ordinaryBeta c d : ℤ)≤2*δ d)
    (hdu : ∀ d≤D,δ d≤(ell : ℤ)*(ordinaryBeta c d : ℤ)) :
    (ell : ℤ)*((ordinaryBeta c D : ℤ)+if D=0 then 0 else (b : ℤ)*(ordinaryBeta c (D-1) : ℤ)) ≤
      2*∑ e∈range (D+1),γ e*δ (D-e) ∧
    (∑ e∈range (D+1),γ e*δ (D-e)) ≤
      2*(ell : ℤ)*((ordinaryBeta c D : ℤ)+if D=0 then 0 else (b : ℤ)*(ordinaryBeta c (D-1) : ℤ)) := by
  by_cases hz : D=0
  · subst D
    simpa [hg0] using And.intro (hdl 0 (by omega))
      ((hdu 0 (by omega)).trans (by simp [ordinaryBeta]; omega))
  have hDp : 1≤D := by omega
  rw [sum_range_split_two _ D hDp]
  simp only [Nat.sub_zero,hg0,hg1,one_mul,ite_eq_right hz]
  have htail0 : 0≤∑ e∈Icc 2 D,γ e*δ (D-e) := by
    apply Finset.sum_nonneg
    intro e he
    exact mul_nonneg (hgn e (mem_Icc.mp he).2) (hdn (D-e) (Nat.sub_le _ _))
  have htail : (∑ e∈Icc 2 D,γ e*δ (D-e))≤
      ((h : ℤ)^2*b*ell)*∑ e∈Icc 2 D,(ordinaryBeta c (D-e) : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have h1 := mul_le_mul (hgb e he) (hdu (D-e) (Nat.sub_le _ _))
      (hdn (D-e) (Nat.sub_le _ _)) (by positivity : (0 : ℤ)≤h^2*b)
    nlinarith [h1]
  have h4 : 2*h≤c := by nlinarith
  have ht := ordinaryBeta_tail_scaled h c D hh h4 hDp hD
  have ht' : (c : ℤ)*(∑ e∈Icc 2 D,(ordinaryBeta c (D-e) : ℤ))≤
      2*h*(ordinaryBeta c (D-1) : ℤ) := by exact_mod_cast ht
  have hc' : 2*(h : ℤ)^3≤c := by exact_mod_cast hc
  have hh' : (1 : ℤ)≤h := by exact_mod_cast hh
  have hsum0 : 0≤∑ e∈Icc 2 D,(ordinaryBeta c (D-e) : ℤ) := by positivity
  have hb : (h : ℤ)^2*(∑ e∈Icc 2 D,(ordinaryBeta c (D-e) : ℤ))≤(ordinaryBeta c (D-1) : ℤ) := by
    nlinarith
  have htfinal : (∑ e∈Icc 2 D,γ e*δ (D-e))≤(ell : ℤ)*b*(ordinaryBeta c (D-1) : ℤ) := by
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℤ)≤(ell : ℤ)*b)
    nlinarith
  have h0l := hdl D (le_refl D)
  have h1l := mul_le_mul_of_nonneg_left (hdl (D-1) (Nat.sub_le _ _)) (Int.natCast_nonneg b)
  have h0u := hdu D (le_refl D)
  have h1u := mul_le_mul_of_nonneg_left (hdu (D-1) (Nat.sub_le _ _)) (Int.natCast_nonneg b)
  constructor <;> nlinarith

def ordinaryWeight (c b D : ℕ) : ℤ :=
  (ordinaryBeta c D : ℤ)+if D=0 then 0 else (b : ℤ)*(ordinaryBeta c (D-1) : ℤ)

theorem series_coeff_mul_reversed (P Q : PowerSeries ℤ) (D : ℕ) :
    PowerSeries.coeff D (P*Q)=∑e∈range (D+1),PowerSeries.coeff e Q*PowerSeries.coeff (D-e) P := by
  rw [mul_comm,PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun e d => PowerSeries.coeff e Q*PowerSeries.coeff d P) D

theorem dense_ordinary_one (b x : ℕ) (hb : 2≤b) (hx : b-1≤x) :
    (ordinarySums (denseSet (b-1) x) 1).card=b := by
  have he : b-1=(b-2)+1 := by omega
  rw [he,card_dense_ordinary (b-2) x 1 (by omega)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.zero_add,Nat.one_mul ]
  omega

theorem ordinary_series_convolution_bound (h c b x D ell : ℕ) (P : PowerSeries ℤ)
    (hh : 2≤h) (hc : 2*h^3≤c) (hb : 2≤b) (hx : b-1≤x)
    (hxb : x≤h*(b-2)+1) (hD : D≤h) (hPn : SeriesNonneg P)
    (hPl : ∀d≤D,(ell : ℤ)*ordinaryBeta c d≤2*PowerSeries.coeff d P)
    (hPu : ∀d≤D,PowerSeries.coeff d P≤(ell : ℤ)*ordinaryBeta c d) :
    (ell : ℤ)*ordinaryWeight c b D≤2*PowerSeries.coeff D (P*ordinarySeries (denseSet (b-1) x)) ∧
    PowerSeries.coeff D (P*ordinarySeries (denseSet (b-1) x))≤2*(ell : ℤ)*ordinaryWeight c b D := by
  rw [series_coeff_mul_reversed]
  unfold ordinaryWeight
  apply ordinary_dense_convolution_bound h c b D ell
    (fun e => PowerSeries.coeff e (ordinarySeries (denseSet (b-1) x)))
    (fun d => PowerSeries.coeff d P) (by omega) hc hD
  · simp [coeff_ordinarySeries,ordinarySums]
  · rw [coeff_ordinarySeries,dense_ordinary_one b x hb hx]
  · intro e _; rw [coeff_ordinarySeries]; positivity
  · intro e he
    rw [coeff_ordinarySeries]
    have hb' : b-2+1=b-1 := by omega
    have hb'' : b-2+2=b := by omega
    have hn := dense_ordinary_bound h (b-2) x e hh (by omega) hxb ((mem_Icc.mp he).2.trans hD)
    rw [hb',hb''] at hn
    exact_mod_cast hn
  · intro d _; exact hPn d
  · exact hPl
  · exact hPu

end SumsetRanges
