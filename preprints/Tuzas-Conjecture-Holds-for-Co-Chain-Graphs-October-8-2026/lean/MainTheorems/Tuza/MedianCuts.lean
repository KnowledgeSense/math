import MainTheorems.Tuza.SparseCover

namespace ResearchMain.Tuza

def halfUp (n : ℕ) : ℕ := (n + 1) / 2

theorem halfUp_le (n : ℕ) : halfUp n ≤ n := by unfold halfUp; omega

theorem halfUp_pos {n : ℕ} (hn : 0 < n) : 0 < halfUp n := by unfold halfUp; omega

theorem halfUp_remainder (n : ℕ) : halfUp n - (n - halfUp n) ≤ 1 := by unfold halfUp; omega

theorem halfUp_add (n : ℕ) : halfUp n + (n - halfUp n) = n :=
  Nat.add_sub_of_le (halfUp_le n)

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

def medianIndex (ha : 0 < a) : Fin a := ⟨halfUp a - 1, by have := halfUp_le a; have := halfUp_pos ha; omega⟩

def medianDegree (ha : 0 < a) : ℕ := d.degree (medianIndex ha)

theorem medianDegree_le (ha : 0 < a) : d.medianDegree ha ≤ b := d.bound _

theorem degree_ge_median (ha : 0 < a) (i : Fin a) (hi : i.val < halfUp a) :
    d.medianDegree ha ≤ d.degree i := by
  apply d.antitone
  change i.val ≤ halfUp a - 1
  omega

theorem degree_le_median (ha : 0 < a) (i : Fin a) (hi : halfUp a ≤ i.val) :
    d.degree i ≤ d.medianDegree ha := by
  apply d.antitone
  change halfUp a - 1 ≤ i.val
  omega

theorem median_sparse_iff (ha : 0 < a) :
    d.height (halfUp b) < halfUp a ↔ d.medianDegree ha < halfUp b := by
  have h := d.lt_height_iff (halfUp b) (medianIndex ha)
  change halfUp a - 1 < d.height (halfUp b) ↔ halfUp b ≤ d.medianDegree ha at h
  have := halfUp_pos ha
  omega

theorem median_sparse_cover (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a) :
    coverNumber d.graph ≤
      (halfUp a).choose 2 + (a - halfUp a).choose 2 +
      (halfUp b).choose 2 + (b - halfUp b).choose 2 +
      d.height (halfUp b) * halfUp b +
      (halfUp a - d.height (halfUp b)) * d.medianDegree ha := by
  have hyt : d.medianDegree ha ≤ halfUp b := le_of_lt ((d.median_sparse_iff ha).mp hs)
  have hc := d.sparseCover_covers
    (fun i hi => (d.lt_height_iff (halfUp b) i).mp hi)
    (fun i hi => d.degree_ge_median ha i hi)
    (fun i hi => d.degree_le_median ha i hi)
    (fun i hi => (d.lt_height_iff (halfUp b) i).mpr hi)
  have hn := number_le_cover hc
  rw [sparseCoverGraph_card a b (halfUp a) (halfUp b) (d.height (halfUp b)) (d.medianDegree ha)
    (le_of_lt hs) (halfUp_le a) hyt (halfUp_le b)] at hn
  exact hn

theorem transpose_height (k : ℕ) (hk : 0 < k) (hka : k ≤ a) :
    d.transpose.height k = d.degree ⟨k - 1, by omega⟩ := by
  let i : Fin a := ⟨k - 1, by omega⟩
  have he : Finset.univ.filter (fun j : Fin b => k ≤ d.transpose.degree j) =
      Finset.univ.filter (fun j : Fin b => j.val < d.degree i) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    change k ≤ d.height (j.val + 1) ↔ j.val < d.degree i
    have h := d.lt_height_iff (j.val + 1) i
    change k - 1 < d.height (j.val + 1) ↔ j.val + 1 ≤ d.degree i at h
    omega
  change (Finset.univ.filter (fun j : Fin b => k ≤ d.transpose.degree j)).card = d.degree i
  rw [he, prefix_filter_card b (d.degree i) (d.bound i)]

theorem transpose_median_height (ha : 0 < a) :
    d.transpose.height (halfUp a) = d.medianDegree ha :=
  d.transpose_height _ (halfUp_pos ha) (halfUp_le a)

theorem transpose_medianDegree (hb : 0 < b) :
    d.transpose.medianDegree hb = d.height (halfUp b) := by
  change d.height (halfUp b - 1 + 1) = _
  congr 1
  have := halfUp_pos hb
  omega

end FerrersProfile

end ResearchMain.Tuza
