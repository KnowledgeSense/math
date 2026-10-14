import BoseBurton.SupportPayment

noncomputable section
namespace BoseBurton
open Finset

theorem sum_pair_nonpos {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι→ℝ)
    (a b : ι) (ha : a∈S) (hb : b∈S) (hab : a≠b)
    (hpair : f a+f b≤0) (hrest : ∀ i∈S, i≠a→i≠b→f i≤0) : ∑ i∈S,f i≤0 := by
  have hbe : b∈S.erase a := mem_erase.mpr ⟨Ne.symm hab,hb⟩
  have hsum : ∑ i∈(S.erase a).erase b,f i≤0 := by
    apply sum_nonpos
    intro i hi
    obtain ⟨hib,hia,hi⟩ := mem_erase.mp hi |>.imp_right (mem_erase.mp)
    exact hrest i hi hia hib
  have h1 := sum_erase_add S f ha
  have h2 := sum_erase_add (S.erase a) f hbe
  linarith

theorem pairedProduct_curvature_nonpos (z : ℝ) (hz0 : 0≤z) (hzhalf : z≤1/2)
    (r j k : ℕ) (hk : 2≤k) (hkr : 2*k≤r) (hjk : j≠k) :
    pairedProduct z r j (k-1)+pairedProduct z r j (k+1)-2*pairedProduct z r j k≤0 := by
  by_cases hj : j<k
  · have h := pairedProduct_concave z hz0 hzhalf r j k (by omega) (by omega)
    linarith
  · rw [pairedProduct_eq_zero_left z r j (k-1) (by omega) (by omega),
      pairedProduct_eq_zero_left z r j (k+1) (by omega) (by omega),
      pairedProduct_eq_zero_left z r j k (by omega) (by omega)]
    norm_num

theorem positiveExpansion_internal_concave (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s k : ℕ) (hsr : s<r) (hk : 2≤k) (hkr : 2*k≤r) :
    (∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j (k-1))+
    (∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j (k+1))≤
    2*(∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j k) := by
  have hz1 : z<1 := by linarith
  let f : ℕ→ℝ := fun j => positiveWeight z r s j*
    (pairedProduct z r j (k-1)+pairedProduct z r j (k+1)-2*pairedProduct z r j k)
  have hrest (j : ℕ) (hj : j≠k) : f j≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (positiveWeight_nonneg z hz0 hz1 r s j hsr)
      (pairedProduct_curvature_nonpos z hz0.le hzhalf r j k hk hkr hj)
  have hsum : ∑ j∈range (s+1),f j≤0 := by
    by_cases hks : k≤s
    · by_cases hr : 2*k+2≤r
      · apply sum_pair_nonpos _ f (k-1) k (by simp; omega) (by simp; omega) (by omega)
        · have hp := enteringWeightedProduct_payment z hz0 hzhalf r s k hsr hk hks hr
          dsimp [f]
          rw [pairedProduct_eq_zero_left z r (k-1) (k-1) (by omega) (by omega),
            pairedProduct_eq_zero_left z r k (k-1) (by omega) (by omega),
            pairedProduct_eq_zero_left z r k k (by omega) (by omega)]
          nlinarith
        · intro j _ _ hj
          exact hrest j hj
      · apply sum_nonpos
        intro j _
        by_cases hj : j=k
        · subst j
          dsimp [f]
          rw [pairedProduct_eq_zero_left z r k (k-1) (by omega) (by omega),
            pairedProduct_eq_zero_right z r k (k+1) (by omega) (by omega),
            pairedProduct_eq_zero_left z r k k (by omega) (by omega)]
          simp
        · exact hrest j hj
    · apply sum_nonpos
      intro j hj
      exact hrest j (by simp only [mem_range] at hj; omega)
  dsimp [f] at hsum
  simp only [mul_sub,mul_add,sum_sub_distrib,sum_add_distrib] at hsum
  have he : (∑ j∈range (s+1),positiveWeight z r s j*(2*pairedProduct z r j k))=
      2*∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j k := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [he] at hsum
  linarith

end BoseBurton
