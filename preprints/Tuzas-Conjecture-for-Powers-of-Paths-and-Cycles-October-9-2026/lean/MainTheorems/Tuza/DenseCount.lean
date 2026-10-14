import MainTheorems.Tuza.CountBounds
import MainTheorems.Tuza.DenseQuadratic

namespace ResearchMain.Tuza

def denseCoverCount (r s t u e : ℕ) : ℕ :=
  r.choose 2 + s.choose 2 + t.choose 2 + u.choose 2 + r * t + e

def denseFanCount (r s t u w z : ℕ) : ℕ :=
  fanCount (r + w) t + fanCount z r + fanCount r s + fanCount t u

noncomputable def denseCompleteCount (r s t u w z e : ℕ) : ℝ :=
  (completeCount (r + t + w + z) : ℝ) - (w : ℝ) * z + e +
    (s - w).choose 2 + (u - z).choose 2

theorem dense_fan_margin (r s t u w z e : ℕ) (hr : 0 < r) (ht : 0 < t)
    (hsr : s ≤ r) (hrs : r ≤ s + 1) (hut : u ≤ t) (htu : t ≤ u + 1) :
    denseMarginD r t w z e - 2 * ((r : ℝ) + t) + 2 ≤
      2 * (denseFanCount r s t u w z : ℝ) - (denseCoverCount r s t u e : ℝ) := by
  have hJ₁ := fan_count_real_lower (r + w) t ht
  have hJ₂ := fan_count_real_lower z r hr
  have hB := balanced_fan_difference r s t u hr ht hsr hrs hut htu
  have hm₁ := min_le_right ((r : ℝ) + w) (t : ℝ)
  have hm₂ := min_le_right (z : ℝ) (r : ℝ)
  simp only [Nat.cast_add] at hJ₁
  simp only [denseMarginD, denseFanCount, denseCoverCount, Nat.cast_add, Nat.cast_mul]
  nlinarith

theorem dense_complete_error (r s t u w z e : ℝ) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hw : 0 ≤ w) (hz : 0 ≤ z) (hs : s = r ∨ s = r - 1) (hu : u = t ∨ u = t - 1) :
    denseMarginF r t w z e - 5 / 3 * (r + t) + 1 ≤
      ((r + t + w + z) * (r + t + w + z - 2) - 3) / 3 - 2 * w * z + 2 * e +
      (s - w) * (s - w - 1) + (u - z) * (u - z - 1) -
      (r * (r - 1) + s * (s - 1) + t * (t - 1) + u * (u - 1)) / 2 - r * t - e := by
  unfold denseMarginF
  rcases hs with hs | hs <;> rcases hu with hu | hu <;> rw [hs, hu] <;>
    ring_nf <;> linarith only [hr, ht, hw, hz]

theorem dense_complete_margin (r s t u w z e : ℕ) (hr : 0 < r) (ht : 0 < t)
    (hsr : s ≤ r) (hrs : r ≤ s + 1) (hut : u ≤ t) (htu : t ≤ u + 1)
    (hws : w ≤ s) (hzu : z ≤ u) :
    denseMarginF r t w z e - 5 / 3 * ((r : ℝ) + t) + 1 ≤
      2 * denseCompleteCount r s t u w z e - (denseCoverCount r s t u e : ℝ) := by
  have hC := complete_count_real_bound (r + t + w + z)
  have er := choose_two_real r
  have es := choose_two_real s
  have et := choose_two_real t
  have eu := choose_two_real u
  have ew := choose_two_real (s - w)
  have ez := choose_two_real (u - z)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hw' : (0 : ℝ) ≤ w := by positivity
  have hz' : (0 : ℝ) ≤ z := by positivity
  have hcases : s = r ∨ s + 1 = r := by omega
  have kcases : u = t ∨ u + 1 = t := by omega
  have hcases' : (s : ℝ) = r ∨ (s : ℝ) = (r : ℝ) - 1 := by
    have h : (s : ℝ) = r ∨ (s : ℝ) + 1 = r := by exact_mod_cast hcases
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have kcases' : (u : ℝ) = t ∨ (u : ℝ) = (t : ℝ) - 1 := by
    have h : (u : ℝ) = t ∨ (u : ℝ) + 1 = t := by exact_mod_cast kcases
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  simp only [Nat.cast_add] at hC
  simp only [Nat.cast_sub hws] at ew
  simp only [Nat.cast_sub hzu] at ez
  have he := dense_complete_error r s t u w z e hr' ht' hw' hz' hcases' kcases'
  simp only [denseCompleteCount, denseCoverCount,
    Nat.cast_add, Nat.cast_mul]
  linear_combination he + hC / 3 + er / 2 + es / 2 + et / 2 + eu / 2 - ew - ez

theorem dense_clique_margin (r s t u e : ℕ) (hr : 0 < r) (ht : 0 < t)
    (hsr : s ≤ r) (hrs : r ≤ s + 1) (hut : u ≤ t) (htu : t ≤ u + 1) :
    denseMarginL r t e - 2 / 3 * ((r : ℝ) + t) - 2 ≤
      2 * ((completeCount (r + s) : ℝ) + completeCount (t + u)) -
        (denseCoverCount r s t u e : ℝ) := by
  have hC₁ := complete_count_real_bound (r + s)
  have hC₂ := complete_count_real_bound (t + u)
  have er := choose_two_real r
  have es := choose_two_real s
  have et := choose_two_real t
  have eu := choose_two_real u
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hcases : s = r ∨ s + 1 = r := by omega
  have kcases : u = t ∨ u + 1 = t := by omega
  have hcases' : (s : ℝ) = r ∨ (s : ℝ) + 1 = r := by exact_mod_cast hcases
  have kcases' : (u : ℝ) = t ∨ (u : ℝ) + 1 = t := by exact_mod_cast kcases
  simp only [Nat.cast_add] at hC₁ hC₂
  simp only [denseMarginL, denseCoverCount, Nat.cast_add, Nat.cast_mul]
  rcases hcases' with hs | hs <;> rcases kcases' with hu | hu <;> nlinarith

theorem dense_count_large (r s t u w z e N : ℕ) (hr : 0 < r) (ht : 0 < t) (hrt : r ≤ t)
    (hsr : s ≤ r) (hrs : r ≤ s + 1) (hut : u ≤ t) (htu : t ≤ u + 1)
    (hws : w ≤ s) (hzu : z ≤ u) (hsize : 88 ≤ r + t)
    (hfan : denseFanCount r s t u w z ≤ N)
    (hcomplete : denseCompleteCount r s t u w z e ≤ N)
    (hclique : completeCount (r + s) + completeCount (t + u) ≤ N) :
    denseCoverCount r s t u e ≤ 2 * N := by
  let M : ℝ := 2 * (N : ℝ) - (denseCoverCount r s t u e : ℝ)
  have hd := dense_fan_margin r s t u w z e hr ht hsr hrs hut htu
  have hf := dense_complete_margin r s t u w z e hr ht hsr hrs hut htu hws hzu
  have hl := dense_clique_margin r s t u e hr ht hsr hrs hut htu
  have hfan' : (denseFanCount r s t u w z : ℝ) ≤ N := by exact_mod_cast hfan
  have hclique' : (completeCount (r + s) : ℝ) + completeCount (t + u) ≤ N := by exact_mod_cast hclique
  have hp := dense_integer_margins_positive r t w z e M M M
    (by positivity) (by exact_mod_cast hrt) (by positivity) (by positivity)
    (by exact_mod_cast hsize) (by dsimp only [M]; linarith)
    (by dsimp only [M]; linarith) (by dsimp only [M]; linarith)
  have h : (denseCoverCount r s t u e : ℝ) ≤ 2 * (N : ℝ) := by
    dsimp only [M] at hp
    linarith
  exact_mod_cast h

end ResearchMain.Tuza
