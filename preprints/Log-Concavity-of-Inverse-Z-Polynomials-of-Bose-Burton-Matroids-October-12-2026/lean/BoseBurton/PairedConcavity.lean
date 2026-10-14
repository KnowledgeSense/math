import BoseBurton.FallingConcavity

noncomputable section
namespace BoseBurton

theorem reflected_product_concave (a₀ a a₁ b₀ b b₁ : ℝ)
    (ha : 0≤a) (hb : 0≤b) (ha₀ : a₀≤a) (ha₁ : a≤a₁)
    (hb₀ : b₀≤b) (hb₁ : b≤b₁) (hca : a₀+a₁≤2*a) (hcb : b₀+b₁≤2*b) :
    a₀*b₁+a₁*b₀≤2*(a*b) := by
  have h1 := mul_nonneg hb (show 0≤2*a-a₀-a₁ by linarith)
  have h2 := mul_nonneg ha (show 0≤2*b-b₀-b₁ by linarith)
  have h3 := mul_nonneg (sub_nonneg.mpr ha₁) (sub_nonneg.mpr hb₀)
  have h4 := mul_nonneg (sub_nonneg.mpr ha₀) (sub_nonneg.mpr hb₁)
  nlinarith

theorem pairedProduct_concave (z : ℝ) (hz0 : 0≤z) (hzhalf : z≤1/2)
    (r j k : ℕ) (hleft : j+1≤k) (hright : j+1≤r-k) :
    pairedProduct z r j (k-1)+pairedProduct z r j (k+1)≤2*pairedProduct z r j k := by
  have hz1 : z<1 := by linarith
  unfold pairedProduct
  rw [show r-(k-1)=r-k+1 by omega,show r-(k+1)=r-k-1 by omega]
  exact reflected_product_concave _ _ _ _ _ _
    (fallingProduct_nonneg z hz0 hz1 j k) (fallingProduct_nonneg z hz0 hz1 j (r-k))
    (fallingProduct_mono z hz0 hz1 j (Nat.sub_le _ _))
    (fallingProduct_mono z hz0 hz1 j (Nat.le_succ _))
    (fallingProduct_mono z hz0 hz1 j (Nat.sub_le _ _))
    (fallingProduct_mono z hz0 hz1 j (Nat.le_succ _))
    (fallingProduct_concave z hz0 hzhalf j k hleft)
    (fallingProduct_concave z hz0 hzhalf j (r-k) hright)

theorem pairedProduct_eq_zero_left (z : ℝ) (r j k : ℕ) (hk : 1≤k) (hkj : k≤j) :
    pairedProduct z r j k=0 := by rw [pairedProduct,fallingProduct_eq_zero z j k hk hkj,zero_mul]

theorem pairedProduct_eq_zero_right (z : ℝ) (r j k : ℕ) (hk : k<r) (hkj : r-k≤j) :
    pairedProduct z r j k=0 := by rw [pairedProduct,fallingProduct_eq_zero z j (r-k) (by omega) hkj,mul_zero]

theorem pairedProduct_pos (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r j k : ℕ) (hleft : j<k) (hright : j<r-k) : 0<pairedProduct z r j k :=
  mul_pos (fallingProduct_pos z hz0 hz1 j k hleft) (fallingProduct_pos z hz0 hz1 j (r-k) hright)

end BoseBurton
