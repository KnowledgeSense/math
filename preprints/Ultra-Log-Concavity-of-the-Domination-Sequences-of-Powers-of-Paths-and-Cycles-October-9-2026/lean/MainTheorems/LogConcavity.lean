import MainTheorems.PureOSequences.Sequences

namespace ResearchMain.LogConcavity

open ResearchMain.PureOSequences

theorem spread_product_le {f : ℤ → ℤ} (hf : RatioDecreasing f)
    (a b : ℤ) (hab : b ≤ a) (j : ℕ) :
    f (a + j) * f (b - j) ≤ f a * f b := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := hf (a + j) (b - j) (by omega)
    have heqa : a + (j + 1 : ℕ) = a + j + 1 := by omega
    have heqb : b - (j + 1 : ℕ) = b - j - 1 := by omega
    rw [heqa, heqb]
    exact h.trans ih

theorem balanced_product_le {f : ℤ → ℤ} (hf : RatioDecreasing f)
    (l x y r : ℤ) (hlx : l ≤ x) (hly : l ≤ y)
    (hsum : l + r = x + y) :
    f l * f r ≤ f x * f y := by
  by_cases hxy : x ≤ y
  · have h := spread_product_le hf y x hxy (x - l).toNat
    have hj : ((x - l).toNat : ℤ) = x - l := by omega
    rw [hj, show y + (x - l) = r by omega, show x - (x - l) = l by omega] at h
    simpa only [mul_comm] using h
  · have h := spread_product_le hf x y (by omega) (y - l).toNat
    have hj : ((y - l).toNat : ℤ) = y - l := by omega
    rw [hj, show x + (y - l) = r by omega, show y - (y - l) = l by omega] at h
    simpa only [mul_comm] using h

theorem shifted_minor {f : ℤ → ℤ} (hf : RatioDecreasing f)
    (u v j : ℤ) (huv : u ≤ v) (hj : 0 ≤ j) :
    f (u - j) * f v ≤ f u * f (v - j) :=
  balanced_product_le hf (u - j) u (v - j) v
    (by omega) (by omega) (by ring)

def finiteConvolution (J : Finset ℤ) (f b : ℤ → ℤ) (n : ℤ) : ℤ :=
  ∑ j ∈ J, b j * f (n - j)

theorem convolution_minor {f b : ℤ → ℤ} (hf : RatioDecreasing f)
    (J : Finset ℤ) (hJ : ∀ j ∈ J, 0 ≤ j) (hb : ∀ j ∈ J, 0 ≤ b j)
    (u v : ℤ) (huv : u ≤ v) :
    finiteConvolution J f b u * f v ≤ f u * finiteConvolution J f b v := by
  simp only [finiteConvolution, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_left (shifted_minor hf u v j huv (hJ j hj)) (hb j hj)
  nlinarith only [h]

theorem conditioning_cumulative_ordered {α : Type*} [LinearOrder α]
    {c f g : α → ℤ} (S : Finset α)
    (hc : ∀ s ∈ S, 0 ≤ c s)
    (hminor : ∀ s t, s ≤ t → f s * g t ≤ g s * f t) (a : α) :
    (∑ s ∈ S.filter (· ≤ a), c s * f s) * (∑ s ∈ S, c s * g s) ≤
      (∑ s ∈ S.filter (· ≤ a), c s * g s) * (∑ s ∈ S, c s * f s) := by
  classical
  let A := S.filter (· ≤ a)
  let B := S.filter (a < ·)
  have hpartition : A ∪ B = S := by
    ext s
    constructor
    · intro hs
      rcases Finset.mem_union.mp hs with hs | hs
      · exact (Finset.mem_filter.mp hs).1
      · exact (Finset.mem_filter.mp hs).1
    · intro hs
      by_cases hsa : s ≤ a
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hs, hsa⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hs, lt_of_not_ge hsa⟩))
  have hdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro s hs ht
    have := (Finset.mem_filter.mp hs).2
    have := (Finset.mem_filter.mp ht).2
    exact not_lt_of_ge (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2
  have hineq :
      (∑ s ∈ A, c s * f s) * (∑ t ∈ B, c t * g t) ≤
      (∑ s ∈ A, c s * g s) * (∑ t ∈ B, c t * f t) := by
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s hs
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨hsS, hsa⟩ := Finset.mem_filter.mp hs
    obtain ⟨htS, hat⟩ := Finset.mem_filter.mp ht
    have h := mul_le_mul_of_nonneg_left (hminor s t (le_trans hsa (le_of_lt hat)))
      (mul_nonneg (hc s hsS) (hc t htS))
    nlinarith only [h]
  have hfpart : (∑ s ∈ S, c s * f s) =
      (∑ s ∈ A, c s * f s) + ∑ t ∈ B, c t * f t := by
    rw [← hpartition, Finset.sum_union hdisjoint]
  have hgpart : (∑ s ∈ S, c s * g s) =
      (∑ s ∈ A, c s * g s) + ∑ t ∈ B, c t * g t := by
    rw [← hpartition, Finset.sum_union hdisjoint]
  change (∑ s ∈ A, c s * f s) * _ ≤ (∑ s ∈ A, c s * g s) * _
  rw [hfpart, hgpart]
  nlinarith only [hineq]

theorem conditioning_cumulative {c f g : ℤ → ℤ} (S : Finset ℤ)
    (hc : ∀ s ∈ S, 0 ≤ c s)
    (hminor : ∀ u v, u ≤ v → g u * f v ≤ f u * g v) (N a : ℤ) :
    (∑ s ∈ S.filter (· ≤ a), c s * f (N - s)) *
      (∑ s ∈ S, c s * g (N - s)) ≤
    (∑ s ∈ S.filter (· ≤ a), c s * g (N - s)) *
      (∑ s ∈ S, c s * f (N - s)) := by
  apply conditioning_cumulative_ordered S hc
  intro s t hst
  simpa only [mul_comm] using hminor (N - t) (N - s) (by omega)

end ResearchMain.LogConcavity
