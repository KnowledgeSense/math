import SumsetRanges.SparseStepCoefficients
import SumsetRanges.DenseRestricted

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

theorem sum_range_split_two (f : ℕ → ℤ) (D : ℕ) (hD : 1≤D) :
    ∑ e∈range (D+1),f e = f 0+f 1+∑ e∈Icc 2 D,f e := by
  have he : range (D+1)={0,1}∪Icc 2 D := by ext e; simp; omega
  have hd : Disjoint ({0,1} : Finset ℕ) (Icc 2 D) := by
    simp only [Finset.disjoint_left,mem_insert,mem_singleton,mem_Icc]
    omega
  rw [he,sum_union hd]
  simp

theorem dense_convolution_bound (h c b D ell : ℕ) (γ δ : ℕ → ℤ)
    (hh : 1≤h) (hc : 8*h^2≤c) (hD : D≤h)
    (hg0 : γ 0=1) (hg1 : γ 1=b)
    (hgn : ∀ e≤D,0≤γ e) (hgb : ∀ e∈Icc 2 D,γ e≤2*h*b)
    (hdn : ∀ d≤D,0≤δ d)
    (hdl : ∀ d≤D,(ell : ℤ)*(c.choose d : ℤ)≤2*δ d)
    (hdu : ∀ d≤D,δ d≤(ell : ℤ)*(c.choose d : ℤ)) :
    (ell : ℤ)*((c.choose D : ℤ)+if D=0 then 0 else (b : ℤ)*(c.choose (D-1) : ℤ)) ≤
      2*∑ e∈range (D+1),γ e*δ (D-e) ∧
    (∑ e∈range (D+1),γ e*δ (D-e)) ≤
      2*(ell : ℤ)*((c.choose D : ℤ)+if D=0 then 0 else (b : ℤ)*(c.choose (D-1) : ℤ)) := by
  by_cases hz : D=0
  · subst D
    simpa [hg0] using And.intro (hdl 0 (by omega))
      ((hdu 0 (by omega)).trans (by simp; omega))
  have hDp : 1≤D := by omega
  rw [sum_range_split_two _ D hDp]
  simp only [Nat.sub_zero,hg0,hg1,one_mul,ite_eq_right hz]
  have htail0 : 0≤∑ e∈Icc 2 D,γ e*δ (D-e) := by
    apply Finset.sum_nonneg
    intro e he
    exact mul_nonneg (hgn e (mem_Icc.mp he).2) (hdn (D-e) (Nat.sub_le _ _))
  have htail : (∑ e∈Icc 2 D,γ e*δ (D-e))≤
      (2*(h : ℤ)*b*ell)*∑ e∈Icc 2 D,(c.choose (D-e) : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have h1 := mul_le_mul (hgb e he) (hdu (D-e) (Nat.sub_le _ _))
      (hdn (D-e) (Nat.sub_le _ _)) (by positivity : (0 : ℤ)≤2*h*b)
    nlinarith [h1]
  have h4 : 4*h≤c := by nlinarith
  have ht := choose_tail_le_scaled_previous h c D h4 hDp hD
  have ht' : (c : ℤ)*(∑ e∈Icc 2 D,(c.choose (D-e) : ℤ))≤
      4*h*(c.choose (D-1) : ℤ) := by exact_mod_cast ht
  have hc' : 8*(h : ℤ)^2≤c := by exact_mod_cast hc
  have hh' : (1 : ℤ)≤h := by exact_mod_cast hh
  have hsum0 : 0≤∑ e∈Icc 2 D,(c.choose (D-e) : ℤ) := by positivity
  have hb : 2*(h : ℤ)*(∑ e∈Icc 2 D,(c.choose (D-e) : ℤ))≤(c.choose (D-1) : ℤ) := by
    nlinarith
  have htfinal : (∑ e∈Icc 2 D,γ e*δ (D-e))≤(ell : ℤ)*b*(c.choose (D-1) : ℤ) := by
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℤ)≤(ell : ℤ)*b)
    nlinarith
  have h0l := hdl D (le_refl D)
  have h1l := mul_le_mul_of_nonneg_left (hdl (D-1) (Nat.sub_le _ _)) (Int.natCast_nonneg b)
  have h0u := hdu D (le_refl D)
  have h1u := mul_le_mul_of_nonneg_left (hdu (D-1) (Nat.sub_le _ _)) (Int.natCast_nonneg b)
  constructor <;> nlinarith

theorem coeff_mul_range_reversed (P Q : Polynomial ℤ) (D : ℕ) :
    (P*Q).coeff D=∑ e∈range (D+1),Q.coeff e*P.coeff (D-e) := by
  rw [mul_comm,coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun e d => Q.coeff e*P.coeff d) D

def restrictedWeight (c b D : ℕ) : ℤ :=
  (c.choose D : ℤ)+if D=0 then 0 else (b : ℤ)*(c.choose (D-1) : ℤ)

theorem dense_polynomial_convolution_bound (h c b x D ell : ℕ) (P : Polynomial ℤ)
    (hh : 1≤h) (hc : 8*h^2≤c) (hb : 2≤b) (hx : b-1≤x) (hD : D≤h)
    (hPn : CoeffNonneg P)
    (hPl : ∀ d≤D,(ell : ℤ)*(c.choose d : ℤ)≤2*P.coeff d)
    (hPu : ∀ d≤D,P.coeff d≤(ell : ℤ)*(c.choose d : ℤ)) :
    (ell : ℤ)*restrictedWeight c b D≤
      2*(P*restrictedPolynomial (denseSet (b-1) x)).coeff D ∧
    (P*restrictedPolynomial (denseSet (b-1) x)).coeff D≤
      2*(ell : ℤ)*restrictedWeight c b D := by
  rw [coeff_mul_range_reversed]
  apply dense_convolution_bound h c b D ell _ _ hh hc hD
  · exact restrictedPolynomial_constant _
  · rw [coeff_restrictedPolynomial,dense_restricted_one _ _ hx]
    congr 1
    omega
  · intro e _
    exact coeffNonneg_restrictedPolynomial _ e
  · intro e he
    rw [coeff_restrictedPolynomial]
    have hh' := dense_restricted_bound h (b-1) x e (by omega) hx
      (by have := (mem_Icc.mp he).1; omega) ((mem_Icc.mp he).2.trans hD)
    have hb' : b-1+1=b := by omega
    rw [hb'] at hh'
    exact_mod_cast hh'
  · intro d _
    exact hPn d
  · exact hPl
  · exact hPu

end SumsetRanges
