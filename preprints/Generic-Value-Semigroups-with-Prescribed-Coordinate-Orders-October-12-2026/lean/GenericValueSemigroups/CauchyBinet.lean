import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Ring

namespace GenericValueSemigroups
open Matrix Equiv Finset

/-- Multilinear expansion of the determinant of a rectangular product. -/
theorem det_rectangular_product {q N : ℕ} (A : Matrix (Fin q) (Fin N) ℝ)
    (B : Matrix (Fin N) (Fin q) ℝ) :
    (A*B).det = ∑ f : Fin q → Fin N,
      (A.submatrix id f).det * ∏ i, B (f i) i := by
  classical
  calc
    (A*B).det = ∑ f : Fin q → Fin N, ∑ σ : Equiv.Perm (Fin q),
        (Equiv.Perm.sign σ : ℝ) * ∏ i, A (σ i) (f i) * B (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f hf
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
        Finset.sum_mul, Finset.prod_mul_distrib, mul_assoc]

/-- Cauchy--Binet summed over all index functions; each ordered minor appears `q!` times. -/
theorem factorial_mul_det_rectangular_product {q N : ℕ}
    (A : Matrix (Fin q) (Fin N) ℝ) (B : Matrix (Fin N) (Fin q) ℝ) :
    (Nat.factorial q : ℝ) * (A*B).det =
      ∑ f : Fin q → Fin N, (A.submatrix id f).det * (B.submatrix f id).det := by
  classical
  symm
  simp only [Matrix.det_apply' (B.submatrix _ _), Matrix.submatrix_apply, id_eq,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  have hσ (σ : Equiv.Perm (Fin q)) :
      (∑ f : Fin q → Fin N, (A.submatrix id f).det *
        ((Equiv.Perm.sign σ : ℝ) * ∏ i, B (f (σ i)) i)) = (A*B).det := by
    rw [det_rectangular_product]
    apply Finset.sum_bij (fun f _ => f ∘ σ)
    · intro f hf; exact Finset.mem_univ _
    · intro f hf g hg hfg
      funext i
      have h := congrFun hfg (σ.symm i)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h
    · intro g hg
      refine ⟨g ∘ σ.symm, Finset.mem_univ _, ?_⟩
      funext i
      simp
    · intro f hf
      have hd := Matrix.det_permute' σ (A.submatrix id f)
      change (A.submatrix id (f ∘ σ)).det =
        (Equiv.Perm.sign σ : ℝ) * (A.submatrix id f).det at hd
      rw [hd]
      simp only [Function.comp_apply]
      ring
  simp_rw [hσ]
  simp [Fintype.card_perm, mul_comm]

theorem exists_sorting_permutation {q N : ℕ} (f : Fin q → Fin N)
    (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin q), StrictMono (f ∘ σ) := by
  classical
  let S : Finset (Fin N) := Finset.univ.image f
  have hc : S.card = q := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  let e : Fin q ≃ S := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨by intro i j hij; exact hf (congrArg Subtype.val hij), by
      intro j
      obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp j.property
      exact ⟨i, Subtype.ext hij⟩⟩
  let o := S.orderIsoOfFin hc
  let σ : Equiv.Perm (Fin q) := o.toEquiv.trans e.symm
  have he (i : Fin q) : f (σ i) = (o i : Fin N) := by
    change (e (e.symm (o i))).val = (o i).val
    rw [e.apply_symm_apply]
  refine ⟨σ, ?_⟩
  intro i j hij
  change f (σ i) < f (σ j)
  rw [he, he]
  exact o.strictMono hij

/-- Simultaneous permutation of the inner indices preserves a product of minors. -/
theorem minor_product_permute {q N : ℕ} (A : Matrix (Fin q) (Fin N) ℝ)
    (B : Matrix (Fin N) (Fin q) ℝ) (f : Fin q → Fin N) (σ : Equiv.Perm (Fin q)) :
    (A.submatrix id (f ∘ σ)).det * (B.submatrix (f ∘ σ) id).det =
      (A.submatrix id f).det * (B.submatrix f id).det := by
  rw [← Matrix.det_mul, ← Matrix.det_mul]
  congr 1
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Function.comp_apply]
  exact Equiv.sum_comp σ (fun k => A i (f k) * B (f k) j)

/-- Products of arbitrary equally indexed minors are nonnegative for totally nonnegative matrices. -/
theorem minor_product_nonneg {N q : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg)
    {rows cols : Fin q → Fin N} (hr : StrictMono rows) (hc : StrictMono cols)
    (f : Fin q → Fin N) :
    0 ≤ (A.submatrix rows f).det * (B.submatrix f cols).det := by
  classical
  by_cases hf : Function.Injective f
  · obtain ⟨σ, hσ⟩ := exists_sorting_permutation f hf
    have he := minor_product_permute (A.submatrix rows id) (B.submatrix id cols) f σ
    simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at he
    rw [← he]
    exact mul_nonneg (hA hr hσ) (hB hσ hc)
  · obtain ⟨i,j,hij,hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      simpa only [Function.Injective, not_forall, exists_prop] using hf
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])]
    simp

/-- Closure of total nonnegativity under matrix multiplication. -/
theorem totallyNonneg_mul {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg) : (A*B).IsTotallyNonneg := by
  intro q rows cols hr hc
  have he := factorial_mul_det_rectangular_product (A.submatrix rows id) (B.submatrix id cols)
  have hmat : (A.submatrix rows id)*(B.submatrix id cols) = (A*B).submatrix rows cols := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hmat] at he
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at he
  have hsum : 0 ≤ ∑ f : Fin q → Fin N,
      (A.submatrix rows f).det * (B.submatrix f cols).det :=
    Finset.sum_nonneg (fun f _ => minor_product_nonneg hA hB hr hc f)
  rw [← he] at hsum
  have hfac : (0 : ℝ) < (Nat.factorial q : ℝ) := by exact_mod_cast Nat.factorial_pos q
  exact (mul_nonneg_iff_of_pos_left hfac).mp hsum

/-- A positive intermediate minor makes a minor of a product positive. -/
theorem det_product_submatrix_pos {N q : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg)
    (rows cols mid : Fin q → Fin N) (hr : StrictMono rows) (hc : StrictMono cols)
    (ha : 0 < (A.submatrix rows mid).det) (hb : 0 < (B.submatrix mid cols).det) :
    0 < ((A*B).submatrix rows cols).det := by
  have he := factorial_mul_det_rectangular_product (A.submatrix rows id) (B.submatrix id cols)
  have hmat : (A.submatrix rows id)*(B.submatrix id cols) = (A*B).submatrix rows cols := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hmat] at he
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at he
  have hp : 0 < ∑ f : Fin q → Fin N,
      (A.submatrix rows f).det * (B.submatrix f cols).det :=
    Finset.sum_pos' (fun f _ => minor_product_nonneg hA hB hr hc f)
      ⟨mid, Finset.mem_univ _, mul_pos ha hb⟩
  rw [← he] at hp
  have hfac : (0 : ℝ) < (Nat.factorial q : ℝ) := by exact_mod_cast Nat.factorial_pos q
  exact (mul_pos_iff_of_pos_left hfac).mp hp

theorem rectangular_minor_product_nonneg {N q : ℕ}
    (A : Matrix (Fin q) (Fin N) ℝ) (B : Matrix (Fin N) (Fin q) ℝ)
    (hA : ∀ f : Fin q → Fin N, StrictMono f → 0 ≤ (A.submatrix id f).det)
    (hB : ∀ f : Fin q → Fin N, StrictMono f → 0 ≤ (B.submatrix f id).det)
    (f : Fin q → Fin N) :
    0 ≤ (A.submatrix id f).det * (B.submatrix f id).det := by
  classical
  by_cases hf : Function.Injective f
  · obtain ⟨σ, hσ⟩ := exists_sorting_permutation f hf
    rw [← minor_product_permute A B f σ]
    exact mul_nonneg (hA _ hσ) (hB _ hσ)
  · obtain ⟨i,j,hij,hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      simpa only [Function.Injective, not_forall, exists_prop] using hf
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])]
    simp

theorem det_rectangular_mul_nonneg {N q : ℕ}
    (A : Matrix (Fin q) (Fin N) ℝ) (B : Matrix (Fin N) (Fin q) ℝ)
    (hA : ∀ f : Fin q → Fin N, StrictMono f → 0 ≤ (A.submatrix id f).det)
    (hB : ∀ f : Fin q → Fin N, StrictMono f → 0 ≤ (B.submatrix f id).det) :
    0 ≤ (A*B).det := by
  have h := Finset.sum_nonneg (fun f (_ : f ∈ Finset.univ) =>
    rectangular_minor_product_nonneg A B hA hB f)
  rw [← factorial_mul_det_rectangular_product] at h
  have hp : (0 : ℝ) < (Nat.factorial q : ℝ) := by exact_mod_cast Nat.factorial_pos q
  exact (mul_nonneg_iff_of_pos_left hp).mp h

theorem det_rectangular_mul_pos {N q : ℕ}
    (A : Matrix (Fin q) (Fin N) ℝ) (B : Matrix (Fin N) (Fin q) ℝ)
    (hA : ∀ f : Fin q → Fin N, StrictMono f → 0 ≤ (A.submatrix id f).det)
    (hB : ∀ f : Fin q → Fin N, StrictMono f → 0 ≤ (B.submatrix f id).det)
    (mid : Fin q → Fin N) (ha : 0 < (A.submatrix id mid).det)
    (hb : 0 < (B.submatrix mid id).det) : 0 < (A*B).det := by
  have h := Finset.sum_pos' (fun f (_ : f ∈ Finset.univ) =>
    rectangular_minor_product_nonneg A B hA hB f)
    ⟨mid, Finset.mem_univ _, mul_pos ha hb⟩
  rw [← factorial_mul_det_rectangular_product] at h
  have hp : (0 : ℝ) < (Nat.factorial q : ℝ) := by exact_mod_cast Nat.factorial_pos q
  exact (mul_pos_iff_of_pos_left hp).mp h

end GenericValueSemigroups
