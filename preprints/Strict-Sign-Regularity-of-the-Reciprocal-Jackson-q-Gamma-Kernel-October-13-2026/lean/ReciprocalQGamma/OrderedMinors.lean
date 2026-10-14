import ReciprocalQGamma.CauchyBinet
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
import Mathlib.Data.Finset.Sort

noncomputable section
open scoped BigOperators
namespace ReciprocalQGamma

theorem injective_sort {r m : ℕ} (f : Fin r → Fin m) (hf : Function.Injective f) :
    ∃ g : Fin r → Fin m, StrictMono g ∧ ∃ p : Equiv.Perm (Fin r), ∀ i, f i = g (p i) := by
  let s : Finset (Fin m) := Finset.univ.image f
  have hc : s.card = r := by simp [s, Finset.card_image_of_injective _ hf]
  let g : Fin r → Fin m := s.orderEmbOfFin hc
  let f' : Fin r → s := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hi : Function.Bijective f' := by
    constructor
    · intro i j h; exact hf (congrArg Subtype.val h)
    · intro ⟨j, hj⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
      exact ⟨i, Subtype.ext hi⟩
  let p : Equiv.Perm (Fin r) := (Equiv.ofBijective f' hi).trans (s.orderIsoOfFin hc).symm.toEquiv
  refine ⟨g, (s.orderEmbOfFin hc).strictMono, p, ?_⟩
  intro i
  change (f' i).val = ((s.orderIsoOfFin hc) ((s.orderIsoOfFin hc).symm (f' i))).val
  rw [OrderIso.apply_symm_apply]

theorem minor_product_nonneg {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin r) ℝ)
    (ha : ∀ g : Fin r → Fin m, StrictMono g → 0 ≤ (A.submatrix id g).det)
    (hb : ∀ g : Fin r → Fin m, StrictMono g → 0 ≤ (B.submatrix g id).det)
    (f : Fin r → Fin m) : 0 ≤ (A.submatrix id f).det * (B.submatrix f id).det := by
  by_cases hf : Function.Injective f
  · obtain ⟨g, hg, p, hp⟩ := injective_sort f hf
    have hfa : (A.submatrix id f).det = ((Equiv.Perm.sign p : ℤ) : ℝ) * (A.submatrix id g).det := by
      convert Matrix.det_permute' p (A.submatrix id g) using 1
      congr 1; ext i j; simp [Matrix.submatrix_apply, hp]
    have hfb : (B.submatrix f id).det = ((Equiv.Perm.sign p : ℤ) : ℝ) * (B.submatrix g id).det := by
      convert Matrix.det_permute p (B.submatrix g id) using 1
      congr 1; ext i j; simp [Matrix.submatrix_apply, hp]
    rw [hfa, hfb]
    have hs : (((Equiv.Perm.sign p : ℤ) : ℝ)) * ((Equiv.Perm.sign p : ℤ) : ℝ) = 1 := by
      have h := congrArg (fun u : ℤˣ => ((u : ℤ) : ℝ)) (Int.units_mul_self (Equiv.Perm.sign p))
      simpa only [Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one] using h
    have he : (((Equiv.Perm.sign p : ℤ) : ℝ) * (A.submatrix id g).det) *
        (((Equiv.Perm.sign p : ℤ) : ℝ) * (B.submatrix g id).det) =
        (A.submatrix id g).det * (B.submatrix g id).det := by
      calc
        _ = ((((Equiv.Perm.sign p : ℤ) : ℝ)) * ((Equiv.Perm.sign p : ℤ) : ℝ)) *
          ((A.submatrix id g).det * (B.submatrix g id).det) := by ring
        _ = _ := by rw [hs, one_mul]
    rw [he]
    exact mul_nonneg (ha g hg) (hb g hg)
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      simpa [Function.Injective] using hf
    rw [Matrix.det_zero_of_column_eq hne (fun _ => by simp [Matrix.submatrix_apply, hij]), zero_mul]

theorem totallyNonneg_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (ha : A.IsTotallyNonneg) (hb : B.IsTotallyNonneg) : (A * B).IsTotallyNonneg := by
  intro r rows cols hr hc
  have he : (A * B).submatrix rows cols = A.submatrix rows id * B.submatrix id cols := by
    ext i j; simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [he]
  have hfact : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  apply nonneg_of_mul_nonneg_right _ hfact
  rw [cauchyBinet_unordered]
  apply Finset.sum_nonneg
  intro f _
  apply minor_product_nonneg _ _ _ _ f
  · intro g hg
    simpa [Matrix.submatrix_submatrix] using (ha hr hg : 0 ≤ (A.submatrix rows g).det)
  · intro g hg
    simpa [Matrix.submatrix_submatrix] using (hb hg hc : 0 ≤ (B.submatrix g cols).det)

end ReciprocalQGamma
