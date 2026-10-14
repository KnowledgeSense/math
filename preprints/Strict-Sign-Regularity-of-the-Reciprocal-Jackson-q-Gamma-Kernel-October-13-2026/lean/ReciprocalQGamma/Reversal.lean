import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

open scoped BigOperators
namespace ReciprocalQGamma

lemma sign_finRev_real (n : ℕ) :
    (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℝ) =
      (-1 : ℝ)^(n*(n-1)/2) := by
  let v : Fin n → ℝ := fun i => i.val
  have hv : Function.Injective v := by
    intro i j h
    apply Fin.ext
    change (i.val : ℝ) = j.val at h
    exact_mod_cast h
  have hd := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hs : ∑ i : Fin n, (Finset.Ioi i).card = n*(n-1)/2 := by
    simp_rw [Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range]
    simpa using (Finset.sum_range_reflect (fun i => i) n).trans (Finset.sum_range_id n)
  have he (i j : Fin n) : v j.rev - v i.rev = (-1 : ℝ)*(v j-v i) := by
    dsimp [v]
    push_cast [Nat.cast_sub (Nat.succ_le_of_lt j.isLt), Nat.cast_sub (Nat.succ_le_of_lt i.isLt)]
    ring
  have hm : ((Matrix.vandermonde v).submatrix Fin.revPerm id) =
      Matrix.vandermonde (fun i => v i.rev) := by rfl
  have hp := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) (Matrix.vandermonde v)
  rw [hm, Matrix.det_vandermonde] at hp
  simp_rw [he, Finset.prod_mul_distrib, Finset.prod_const] at hp
  rw [Finset.prod_pow_eq_pow_sum, hs,
    ← Matrix.det_vandermonde] at hp
  exact mul_right_cancel₀ hd hp.symm

lemma det_reverse_columns {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.det (fun i j => M i j.rev) = (-1 : ℝ)^(n*(n-1)/2) * Matrix.det M := by
  change (M.submatrix id Fin.revPerm).det = _
  rw [Matrix.det_permute', sign_finRev_real]

end ReciprocalQGamma
