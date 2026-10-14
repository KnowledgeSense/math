import MainTheorems.Tuza.Certificates.SparseCatalogue
import MainTheorems.Tuza.SparsePivots
import MainTheorems.Tuza.SmallClosure

namespace ResearchMain.Tuza

def sparseTest (a b x y : ℕ) : Bool :=
  decide (a + b ≤ 12) || sparseBaseTest a b x y ||
    sparsePivotTest a b x y ||
    sparseCertificateTest (Certificates.sparseCertificates a b) x y

def sparseSizeTest (a : ℕ) : Bool :=
  (List.range 111).all fun b =>
    if 0 < a ∧ a ≤ b ∧ a + b ≤ 110 ∧
        3 * ((halfUp a) ^ 2 + (halfUp b) ^ 2) < 84 * (halfUp a + halfUp b) then
      (List.range (halfUp a)).all fun x => (List.range (halfUp b)).all fun y => sparseTest a b x y
    else true

theorem FerrersProfile.sparseTest_sound {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hab : a ≤ b) (hs : d.height (halfUp b) < halfUp a)
    (h : sparseTest a b (d.height (halfUp b)) (d.medianDegree ha) = true) : Inequality d.graph := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  simp only [sparseTest, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · exact d.small_inequality ha hab h
  · exact d.sparse_base_sound ha hb hs h
  · exact d.sparsePivotTest_sound ha hs h
  · exact sparseCertificateTest_sound d ha hs _ h

theorem FerrersProfile.sparseSizeTest_sound {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hab : a ≤ b) (hn : a + b ≤ 110)
    (hs : d.height (halfUp b) < halfUp a)
    (hq : 3 * ((halfUp a) ^ 2 + (halfUp b) ^ 2) < 84 * (halfUp a + halfUp b))
    (h : sparseSizeTest a = true) : Inequality d.graph := by
  have hb : b ∈ List.range 111 := List.mem_range.mpr (by omega)
  have hy := (d.median_sparse_iff ha).mp hs
  have hm := (List.all_eq_true.mp h) b hb
  rw [ite_eq_left ⟨ha, hab, hn, hq⟩] at hm
  have hx := List.all_eq_true.mp hm (d.height (halfUp b)) (List.mem_range.mpr hs)
  have hxy := List.all_eq_true.mp hx (d.medianDegree ha) (List.mem_range.mpr hy)
  exact d.sparseTest_sound ha hab hs hxy

end ResearchMain.Tuza
