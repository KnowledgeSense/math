import MainTheorems.Tuza.DenseMenu

namespace ResearchMain.Tuza

theorem shape_two_three_cases {w z : ℕ} (s : FerrersProfile w z) (hw : w = 2) (hz : z = 3)
    (hs : shapeSum s = 4) :
    (∀ i, s.degree i = if i.val = 0 then 3 else 1) ∨ (∀ i, s.degree i = 2) := by
  subst w
  subst z
  have h0 := s.bound 0
  have h1 := s.bound 1
  have ha := s.antitone (show (0 : Fin 2) ≤ 1 by decide)
  simp only [shapeSum, Fin.sum_univ_two] at hs
  have hc : (s.degree 0 = 3 ∧ s.degree 1 = 1) ∨ (s.degree 0 = 2 ∧ s.degree 1 = 2) := by omega
  rcases hc with hc | hc
  · left
    intro i
    fin_cases i <;> simp [hc.1, hc.2]
  · right
    intro i
    fin_cases i <;> simp [hc.1, hc.2]

theorem shape_two_two_cases {w z : ℕ} (s : FerrersProfile w z) (hw : w = 2) (hz : z = 2)
    (hs : shapeSum s = 3) : ∀ i, s.degree i = if i.val = 0 then 2 else 1 := by
  subst w
  subst z
  have h0 := s.bound 0
  have h1 := s.bound 1
  have ha := s.antitone (show (0 : Fin 2) ≤ 1 by decide)
  simp only [shapeSum, Fin.sum_univ_two] at hs
  have hc : s.degree 0 = 2 ∧ s.degree 1 = 1 := by omega
  intro i
  fin_cases i <;> simp [hc.1, hc.2]

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem dense_fullRows_le (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b))
    (he : d.lowerCrossCount (halfUp a) (halfUp b) =
      (d.height (halfUp b) - halfUp a) * (d.medianDegree ha - halfUp b)) (i : Fin a) :
    (if i.val < d.height (halfUp b) then d.medianDegree ha else 0) ≤ d.degree i := by
  by_cases hx : i.val < d.height (halfUp b)
  · rw [ite_eq_left hx]
    by_cases hr : i.val < halfUp a
    · exact d.degree_ge_median ha i hr
    · let j : Fin (d.height (halfUp b) - halfUp a) := ⟨i.val - halfUp a, by omega⟩
      have hsum := (d.lowerShape_sum ha hd).trans he
      have hj := shapeSum_full (d.lowerShape ha hd) hsum j
      have hm : middleEmbedding a (halfUp a) (d.height (halfUp b)) hd (d.height_le _) j = i := by
        apply Fin.ext
        simp only [middleEmbedding_val, j]
        omega
      change d.degree (middleEmbedding a (halfUp a) (d.height (halfUp b)) hd (d.height_le _) j) -
        halfUp b = d.medianDegree ha - halfUp b at hj
      rw [hm] at hj
      have hdi := (d.lt_height_iff _ i).mp hx
      have hy := d.median_dense_degree ha hd
      omega
  · rw [ite_eq_right hx]
    exact Nat.zero_le _

theorem dense_pattern_graph_le (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b))
    (c : FerrersProfile a b)
    (hprefix : ∀ i, i.val < halfUp a → c.degree i ≤ d.medianDegree ha)
    (hsuffix : ∀ i, d.height (halfUp b) ≤ i.val → c.degree i = 0)
    (hmiddle : ∀ j, c.degree (middleEmbedding a (halfUp a) (d.height (halfUp b)) hd (d.height_le _) j) ≤
      halfUp b + (d.lowerShape ha hd).degree j) : c.graph ≤ d.graph := by
  apply graph_mono
  intro i
  by_cases hr : i.val < halfUp a
  · exact (hprefix i hr).trans (d.degree_ge_median ha i hr)
  · by_cases hx : i.val < d.height (halfUp b)
    · let j : Fin (d.height (halfUp b) - halfUp a) := ⟨i.val - halfUp a, by omega⟩
      have hm : middleEmbedding a (halfUp a) (d.height (halfUp b)) hd (d.height_le _) j = i := by
        apply Fin.ext
        simp only [middleEmbedding_val, j]
        omega
      have hj := hmiddle j
      change c.degree (middleEmbedding a (halfUp a) (d.height (halfUp b)) hd (d.height_le _) j) ≤
        halfUp b + (d.degree (middleEmbedding a (halfUp a) (d.height (halfUp b)) hd (d.height_le _) j) - halfUp b) at hj
      rw [hm, Nat.add_sub_of_le ((d.lt_height_iff _ i).mp hx)] at hj
      exact hj
    · rw [hsuffix i (by omega)]
      exact Nat.zero_le _

theorem dense_zero_certificate (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b))
    (x y : ℕ) (hx : d.height (halfUp b) = x) (hy : d.medianDegree ha = y)
    (he : d.lowerCrossCount (halfUp a) (halfUp b) = 0)
    (c : FerrersProfile a b) (hrows : ∀ i, c.degree i = denseRows a b x y i)
    (p : ℕ) (hp : p ≤ packingNumber c.graph) (hsize : denseCoverBase a b ≤ 2 * p) : Inequality d.graph := by
  have hg : c.graph ≤ d.graph := graph_mono (fun i => by
    rw [hrows i, ← hx, ← hy]
    exact d.denseRows_le ha i)
  have hc := d.dense_cover_base_bound hd
  rw [he, Nat.add_zero] at hc
  exact hc.trans (hsize.trans (Nat.mul_le_mul_left 2 (hp.trans (packingNumber_mono hg))))

theorem dense_pattern_graph_le_of_shape (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b))
    (c : FerrersProfile a b) (v : ℕ → ℕ)
    (hshape : ∀ j, (d.lowerShape ha hd).degree j = v j.val)
    (hprefix : ∀ i, i.val < halfUp a → c.degree i ≤ d.medianDegree ha)
    (hsuffix : ∀ i, d.height (halfUp b) ≤ i.val → c.degree i = 0)
    (hmiddle : ∀ i, halfUp a ≤ i.val → i.val < d.height (halfUp b) →
      c.degree i ≤ halfUp b + v (i.val - halfUp a)) : c.graph ≤ d.graph := by
  apply d.dense_pattern_graph_le ha hd c hprefix hsuffix
  intro j
  rw [hshape j]
  have hj := j.isLt
  have hm := hmiddle (middleEmbedding a (halfUp a) (d.height (halfUp b)) hd (d.height_le _) j)
    (by simp only [middleEmbedding_val]; omega)
    (by simp only [middleEmbedding_val]; omega)
  simpa only [middleEmbedding_val, Nat.add_sub_cancel_left] using hm

theorem dense_full_certificate (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b))
    (x y : ℕ) (hx : d.height (halfUp b) = x) (hy : d.medianDegree ha = y)
    (he : d.lowerCrossCount (halfUp a) (halfUp b) = (x - halfUp a) * (y - halfUp b))
    (c : FerrersProfile a b) (hrows : ∀ i, c.degree i = if i.val < x then y else 0)
    (p : ℕ) (hp : p ≤ packingNumber c.graph)
    (hsize : denseCoverBase a b + (x - halfUp a) * (y - halfUp b) ≤ 2 * p) : Inequality d.graph := by
  have hg : c.graph ≤ d.graph := graph_mono (fun i => by
    rw [hrows i, ← hx, ← hy]
    exact d.dense_fullRows_le ha hd (by simpa only [hx, hy] using he) i)
  have hc := d.dense_cover_base_bound hd
  rw [he] at hc
  exact hc.trans (hsize.trans (Nat.mul_le_mul_left 2 (hp.trans (packingNumber_mono hg))))

end FerrersProfile

structure DenseCertificate (a b : ℕ) where
  x : ℕ
  y : ℕ
  e : ℕ
  correct : ∀ (d : FerrersProfile a b) (ha : 0 < a), halfUp a ≤ d.height (halfUp b) →
    d.height (halfUp b) = x → d.medianDegree ha = y →
    d.lowerCrossCount (halfUp a) (halfUp b) = e → Inequality d.graph

def denseCertificateTest {a b : ℕ} (certificates : List (DenseCertificate a b)) (x y e : ℕ) : Bool :=
  certificates.any fun c => decide (c.x = x ∧ c.y = y ∧ c.e = e)

theorem denseCertificateTest_sound {a b : ℕ} (d : FerrersProfile a b) (ha : 0 < a)
    (hd : halfUp a ≤ d.height (halfUp b)) (certificates : List (DenseCertificate a b))
    (h : denseCertificateTest certificates (d.height (halfUp b)) (d.medianDegree ha)
      (d.lowerCrossCount (halfUp a) (halfUp b)) = true) : Inequality d.graph := by
  simp only [denseCertificateTest, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨c, _, hx, hy, he⟩ := h
  exact c.correct d ha hd hx.symm hy.symm he.symm

end ResearchMain.Tuza
