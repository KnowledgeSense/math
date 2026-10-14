import MainTheorems.EulerianPencil.Reduction

namespace ResearchMain.EulerianPencil

open Polynomial

theorem reflect_linear (r : ℝ) : (X - C r : ℝ[X]).reflect 1 = 1 - C r * X := by
  simp [reflect_sub]

theorem reflect_root_product (r : Multiset ℝ) :
    ((r.map (fun a => (X - C a : ℝ[X]))).prod).reflect r.card =
      (r.map (fun a => (1 - C a * X : ℝ[X]))).prod := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a r ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons]
    rw [show r.card + 1 = 1 + r.card by omega, reflect_mul _ _
      (by simp : (X - C a : ℝ[X]).natDegree ≤ 1)
      (natDegree_multiset_prod_X_sub_C_eq_card r).le, reflect_linear, ih]

theorem reflect_splits {f : ℝ[X]} (hs : f.Splits) : (f.reflect f.natDegree).Splits := by
  have he : f.reflect f.natDegree = C f.leadingCoeff *
      (f.roots.map (fun a => (1 - C a * X : ℝ[X]))).prod := by
    conv_lhs => arg 2; rw [hs.eq_prod_roots]
    rw [reflect_C_mul, hs.natDegree_eq_card_roots, reflect_root_product]
  rw [he]
  apply Splits.C_mul
  apply Splits.multisetProd
  intro p hp
  obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hp
  have hn : (1 - C a * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
  exact Splits.of_natDegree_le_one hn

theorem reduction_splits {m : ℕ} {f : ℝ[X]} (hs : f.Splits) (hd : f.natDegree = m) :
    (reduction m f).Splits := by
  rw [reduction, ← hd]
  exact (reflect_splits hs).comp_X_sub_C 2

theorem oddH_splits (m : ℕ) : (oddH m).Splits :=
  reduction_splits (oddF_splits m) (oddF_natDegree m)

theorem evenH_splits (m : ℕ) : (evenH m).Splits :=
  reduction_splits (evenF_splits m) (evenF_natDegree m)

end ResearchMain.EulerianPencil
