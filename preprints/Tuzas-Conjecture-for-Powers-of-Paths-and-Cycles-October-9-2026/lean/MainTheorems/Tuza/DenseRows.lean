import MainTheorems.Tuza.DenseReduction
import MainTheorems.Tuza.ProfileBounds
import MainTheorems.Tuza.FastCounts

namespace ResearchMain.Tuza

def denseRows (a b x y : ℕ) : Fin a → ℕ :=
  fun i => if i.val < halfUp a then y else if i.val < x then halfUp b else 0

def denseProfile (a b x y : ℕ) (hy : halfUp b ≤ y) (hyb : y ≤ b) : FerrersProfile a b where
  degree := denseRows a b x y
  bound i := by
    have hb := halfUp_le b
    simp only [denseRows]
    split_ifs <;> omega
  antitone := by
    intro i j hij
    change i.val ≤ j.val at hij
    simp only [denseRows]
    split_ifs <;> omega

def denseHeight (a b x y k : ℕ) : ℕ :=
  if k = 0 then a else if k ≤ halfUp b then x else if k ≤ y then halfUp a else 0

def denseTransposeHeight (a b x y k : ℕ) : ℕ :=
  if k = 0 then b else if k ≤ halfUp a then y else if k ≤ x then halfUp b else 0

theorem denseHeight_eq (a b x y k : ℕ) (hx : halfUp a ≤ x) (hxa : x ≤ a) (hy : halfUp b ≤ y) :
    rowHeight (denseRows a b x y) k = denseHeight a b x y k := by
  by_cases hk : k = 0
  · subst k
    simp [rowHeight, denseHeight]
  · by_cases hkt : k ≤ halfUp b
    · have he : Finset.univ.filter (fun i : Fin a => k ≤ denseRows a b x y i) =
          Finset.univ.filter (fun i : Fin a => i.val < x) := by
        ext i
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        dsimp only [denseRows]
        split_ifs <;> omega
      simp only [rowHeight, he, denseHeight, ite_eq_right hk, ite_eq_left hkt]
      exact prefix_filter_card a x hxa
    · by_cases hky : k ≤ y
      · have he : Finset.univ.filter (fun i : Fin a => k ≤ denseRows a b x y i) =
            Finset.univ.filter (fun i : Fin a => i.val < halfUp a) := by
          ext i
          rw [Finset.mem_filter, Finset.mem_filter]
          simp only [Finset.mem_univ, true_and]
          dsimp only [denseRows]
          split_ifs <;> omega
        simp only [rowHeight, he, denseHeight, ite_eq_right hk, ite_eq_right hkt, ite_eq_left hky]
        exact prefix_filter_card a _ (halfUp_le a)
      · have he : Finset.univ.filter (fun i : Fin a => k ≤ denseRows a b x y i) = ∅ := by
          ext i
          rw [Finset.mem_filter]
          simp only [Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          dsimp only [denseRows]
          split_ifs <;> omega
        simp only [rowHeight, he, denseHeight, ite_eq_right hk, ite_eq_right hkt, ite_eq_right hky,
          Finset.card_empty]

theorem denseTransposeHeight_eq (a b x y k : ℕ) (hy : halfUp b ≤ y) (hyb : y ≤ b) (hk : k ≤ a) :
    (denseProfile a b x y hy hyb).transpose.height k = denseTransposeHeight a b x y k := by
  by_cases hk0 : k = 0
  · subst k
    simp [FerrersProfile.height, denseTransposeHeight]
  · rw [(denseProfile a b x y hy hyb).transpose_height k (by omega) hk]
    change denseRows a b x y ⟨k - 1, _⟩ = denseTransposeHeight a b x y k
    simp only [denseRows, denseTransposeHeight, ite_eq_right hk0]
    split_ifs <;> omega

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem denseRows_le (ha : 0 < a) (i : Fin a) :
    denseRows a b (d.height (halfUp b)) (d.medianDegree ha) i ≤ d.degree i := by
  simp only [denseRows]
  split_ifs with hir hix
  · exact d.degree_ge_median ha i hir
  · exact (d.lt_height_iff _ i).mp hix
  · exact Nat.zero_le _

theorem denseProfile_le (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    (denseProfile a b (d.height (halfUp b)) (d.medianDegree ha)
      (d.median_dense_degree ha hd) (d.medianDegree_le ha)).graph ≤ d.graph :=
  graph_mono (d.denseRows_le ha)

end FerrersProfile

end ResearchMain.Tuza
