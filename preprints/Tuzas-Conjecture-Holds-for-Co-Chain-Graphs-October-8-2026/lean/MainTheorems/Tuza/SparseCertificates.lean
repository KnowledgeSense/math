import MainTheorems.Tuza.SparseMenu

namespace ResearchMain.Tuza

structure SparseCertificate (a b : ℕ) where
  x : ℕ
  y : ℕ
  profile : FerrersProfile a b
  rows : ∀ i, profile.degree i = sparseRows a b x y i
  size : ℕ
  packed : size ≤ packingNumber profile.graph

def sparseCertificateTest {a b : ℕ} (certificates : List (SparseCertificate a b)) (x y : ℕ) : Bool :=
  certificates.any fun c => decide (c.x = x ∧ c.y = y ∧ sparseCoverValue a b x y ≤ 2 * c.size)

theorem sparseCertificateTest_sound {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a)
    (certificates : List (SparseCertificate a b))
    (h : sparseCertificateTest certificates (d.height (halfUp b)) (d.medianDegree ha) = true) :
    Inequality d.graph := by
  simp only [sparseCertificateTest, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨c, _, hx, hy, hsize⟩ := h
  have hg : c.profile.graph ≤ d.graph := by
    apply FerrersProfile.graph_mono
    intro i
    rw [c.rows i, hx, hy]
    exact d.sparseRows_le ha i
  have hp := c.packed.trans (packingNumber_mono hg)
  exact (d.sparse_cover_value_bound ha hs).trans (hsize.trans (Nat.mul_le_mul_left 2 hp))

end ResearchMain.Tuza
