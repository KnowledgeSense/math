import MainTheorems.Tuza.DenseRows
import MainTheorems.Tuza.IntervalSums

namespace ResearchMain.Tuza

def shapeSum {w z : ℕ} (s : FerrersProfile w z) : ℕ := ∑ i : Fin w, s.degree i

theorem shapeSum_le {w z : ℕ} (s : FerrersProfile w z) : shapeSum s ≤ w * z := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin w))) => s.bound i)
  simpa only [shapeSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

theorem shapeSum_zero {w z : ℕ} (s : FerrersProfile w z) (h : shapeSum s = 0) :
    ∀ i, s.degree i = 0 := by
  exact fun i => (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ _)

theorem shapeSum_full {w z : ℕ} (s : FerrersProfile w z) (h : shapeSum s = w * z) :
    ∀ i, s.degree i = z := by
  have he : ∑ i : Fin w, s.degree i = ∑ _i : Fin w, z := by simpa only [shapeSum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  exact fun i => (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ (Finset.univ : Finset (Fin w))) =>
    s.bound j)).mp he i (Finset.mem_univ _)

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem lowerCrossCount_eq_sum (r t : ℕ) :
    d.lowerCrossCount r t = ∑ i : Fin a, if r ≤ i.val then d.degree i - t else 0 := by
  have he : d.lowerCrossCount r t =
      ∑ i : Fin a, (Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ r ≤ i.val ∧ t ≤ j.val)).card := by
    simp only [lowerCrossCount, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r ≤ i.val
  · have hf : Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ r ≤ i.val ∧ t ≤ j.val) =
        Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ t ≤ j.val) := by
      ext j
      simp [hi]
    rw [hf, ite_eq_left hi]
    exact d.cross_suffix_card i t
  · have hf : Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ r ≤ i.val ∧ t ≤ j.val) = ∅ := by
      ext j
      simp [hi]
    rw [hf, Finset.card_empty, ite_eq_right hi]

def lowerShape (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    FerrersProfile (d.height (halfUp b) - halfUp a) (d.medianDegree ha - halfUp b) where
  degree i := d.degree (middleEmbedding a (halfUp a) (d.height (halfUp b)) hd (d.height_le _) i) - halfUp b
  bound i := by
    apply Nat.sub_le_sub_right
    apply d.degree_le_median ha
    simp only [middleEmbedding_val]
    omega
  antitone := by
    intro i j hij
    apply Nat.sub_le_sub_right
    apply d.antitone
    change halfUp a + i.val ≤ halfUp a + j.val
    exact Nat.add_le_add_left hij _

theorem lowerShape_sum (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    shapeSum (d.lowerShape ha hd) = d.lowerCrossCount (halfUp a) (halfUp b) := by
  rw [lowerCrossCount_eq_sum]
  have he : (∑ i : Fin a, if halfUp a ≤ i.val then d.degree i - halfUp b else 0) =
      ∑ i : Fin a with halfUp a ≤ i.val ∧ i.val < d.height (halfUp b), (d.degree i - halfUp b) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hr : halfUp a ≤ i.val
    · by_cases hx : i.val < d.height (halfUp b)
      · simp [hr, hx]
      · have hdeg : d.degree i < halfUp b := by
          have hh := d.lt_height_iff (halfUp b) i
          omega
        simp [hr, hx, Nat.sub_eq_zero_of_le hdeg.le]
    · simp [hr]
  rw [he, sum_middle a (halfUp a) (d.height (halfUp b)) hd (d.height_le _)]
  rfl

theorem lowerCrossCount_bound (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    d.lowerCrossCount (halfUp a) (halfUp b) ≤
      (d.height (halfUp b) - halfUp a) * (d.medianDegree ha - halfUp b) := by
  rw [← d.lowerShape_sum ha hd]
  exact shapeSum_le _

end FerrersProfile

end ResearchMain.Tuza
