import ReciprocalQGamma.InfiniteKernel
import ReciprocalQGamma.Reversal

noncomputable section
open scoped BigOperators
namespace ReciprocalQGamma

lemma reciprocal_qGamma_factorization (q x y : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hx : 0 < x) (hy : 0 < y) :
    1 / qGamma q (x+y) =
      ((1-q)^(x-1) / qInfiniteProduct q q) * (1-q)^y *
        qInfiniteProduct q (q^x*q^y) := by
  have hb : 0 < 1-q := sub_pos.mpr hq1
  have hp := (qInfiniteProduct_pos q q hq0.le hq1 hq0.le hq1).ne'
  have hz0 : 0 ≤ q^(x+y) := (Real.rpow_pos_of_pos hq0 _).le
  have hz1 : q^(x+y) < 1 := Real.rpow_lt_one hq0.le hq1 (add_pos hx hy)
  have hr := (qInfiniteProduct_pos q (q^(x+y)) hq0.le hq1 hz0 hz1).ne'
  have hxpow := (Real.rpow_pos_of_pos hb x).ne'
  have hypow := (Real.rpow_pos_of_pos hb y).ne'
  rw [Real.rpow_add hq0] at hr
  unfold qGamma
  rw [Real.rpow_add hq0, Real.rpow_sub hb, Real.rpow_sub hb,
    Real.rpow_one, Real.rpow_add hb]
  field_simp

/-- Strict sign regularity of the reciprocal q-gamma kernel at arbitrary positive nodes. -/
theorem reciprocal_qGamma_strict_sign_regular (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    {r : ℕ} (x y : Fin r → ℝ) (hx : StrictMono x) (hy : StrictMono y)
    (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i) :
    0 < (-1 : ℝ)^(r*(r-1)/2) *
      Matrix.det (fun i j => 1 / qGamma q (x i+y j)) := by
  let s : Fin r → ℝ := fun i => 1-q^(x i)
  let t : Fin r → ℝ := fun j => q^(y j.rev)
  have hs : StrictMono s := by
    intro i j hij
    have h := Real.rpow_lt_rpow_of_exponent_gt hq0 hq1 (hx hij)
    dsimp [s]
    linarith
  have ht : StrictMono t := by
    intro i j hij
    exact Real.rpow_lt_rpow_of_exponent_gt hq0 hq1 (hy (Fin.rev_lt_rev.mpr hij))
  have hs0 (i : Fin r) : 0 < s i := sub_pos.mpr (Real.rpow_lt_one hq0.le hq1 (hx0 i))
  have hs1 (i : Fin r) : s i < 1 := by
    have h := Real.rpow_pos_of_pos hq0 (x i)
    dsimp [s]; linarith
  have ht0 (j : Fin r) : 0 < t j := Real.rpow_pos_of_pos hq0 _
  have ht1 (j : Fin r) : t j < 1 := Real.rpow_lt_one hq0.le hq1 (hy0 j.rev)
  have hk := qInfiniteProduct_kernel_pos q hq0 hq1 s t hs ht hs0 hs1 ht0 ht1
  let K : Matrix (Fin r) (Fin r) ℝ := fun i j => qInfiniteProduct q (q^(x i)*q^(y j.rev))
  have hk' : 0 < K.det := by simpa [K, s, t] using hk
  let a : Fin r → ℝ := fun i => (1-q)^(x i-1) / qInfiniteProduct q q
  let b : Fin r → ℝ := fun j => (1-q)^(y j.rev)
  have ha : ∀ i, 0 < a i := fun i => div_pos
    (Real.rpow_pos_of_pos (sub_pos.mpr hq1) _)
    (qInfiniteProduct_pos q q hq0.le hq1 hq0.le hq1)
  have hb : ∀ j, 0 < b j := fun j => Real.rpow_pos_of_pos (sub_pos.mpr hq1) _
  have he : (fun i j => 1 / qGamma q (x i+y j.rev)) =
      Matrix.of (fun i j => a i*(b j*K i j)) := by
    funext i j
    simpa [a,b,K,mul_assoc] using reciprocal_qGamma_factorization q (x i) (y j.rev)
      hq0 hq1 (hx0 i) (hy0 j.rev)
  have hdet : 0 < Matrix.det (fun i j => 1 / qGamma q (x i+y j.rev)) := by
    rw [he]
    change 0 < (Matrix.of (fun i j => a i*(Matrix.of (fun i j => b j*K i j)) i j)).det
    rw [Matrix.det_mul_column a (Matrix.of (fun i j => b j*K i j))]
    rw [Matrix.det_mul_row b K]
    exact mul_pos (Finset.prod_pos (fun i _ => ha i))
      (mul_pos (Finset.prod_pos (fun j _ => hb j)) hk')
  rw [det_reverse_columns (fun i j => 1 / qGamma q (x i+y j))] at hdet
  exact hdet

end ReciprocalQGamma
