import OscillatoryRecurrence.PolynomialMoments

noncomputable section
open scoped BigOperators
open Polynomial Finset
namespace OscillatoryRecurrence

lemma determinant_scaling {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n → ℕ) (t s : ℂ)
    (h : ∀ i j, t^(a i+b j+1)*A i j = s*(-1)^(a i+b j)*B i j) :
    t^((∑ i, a i)+(∑ j, b j)+n)*A.det =
      s^n*(-1)^((∑ i, a i)+(∑ j, b j))*B.det := by
  let C : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => t^(b j)*A i j)
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => (-1)^(b j)*B i j)
  have he : Matrix.of (fun i j => t^(a i+1)*C i j) =
      Matrix.of (fun i j => (s*(-1)^(a i))*D i j) := by
    ext i j
    have hh := h i j
    simp only [C,D,Matrix.of_apply]
    convert hh using 1 <;> ring
  have hh := congrArg Matrix.det he
  rw [Matrix.det_mul_column, Matrix.det_mul_column] at hh
  have hc : C.det = (∏ j, t^(b j))*A.det := Matrix.det_mul_row _ A
  have hd : D.det = (∏ j, (-1)^(b j))*B.det := Matrix.det_mul_row _ B
  rw [hc,hd] at hh
  simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
    prod_pow_eq_pow_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] at hh
  convert hh using 1 <;> ring

lemma exponentialMoment_determinant (t s : ℂ) (ht : t ≠ 0)
    (hplus : Complex.exp t = s) (hminus : Complex.exp (-t) = s)
    {n : ℕ} (a b : Fin n → ℕ) :
    t^((∑ i, a i)+(∑ j, b j)+n)*
      Matrix.det (fun i j => exponentialMoment t (a i+b j+1)) =
    s^n*(-1)^((∑ i, a i)+(∑ j, b j))*
      (Matrix.det (fun i j => endpointMoment (a i+b j))).eval₂ (Rat.castHom ℂ) (-t^2) := by
  have hh := determinant_scaling
    (fun i j => exponentialMoment t (a i+b j+1))
    (fun i j => (endpointMoment (a i+b j)).eval₂ (Rat.castHom ℂ) (-t^2)) a b t s
    (fun i j => exponentialMoment_polynomial t s ht hplus hminus (a i+b j))
  have he := (Polynomial.eval₂RingHom (Rat.castHom ℂ) (-t^2)).map_det
    (fun i j => endpointMoment (a i+b j))
  convert hh using 1
  exact congrArg (fun d : ℂ => s^n*(-1)^((∑ i, a i)+(∑ j, b j))*d) he

lemma double_index_sum (n : ℕ) : (∑ i : Fin n, i.val)*2+n = n^2 := by
  have he : (∑ i : Fin n, i.val) = ∑ i ∈ range n, i :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n
  rw [he, sum_range_id_mul_two]
  cases n with
  | zero => simp
  | succ n => simp; ring

lemma exponential_hankel_normalization (t s : ℂ) (ht : t ≠ 0)
    (hplus : Complex.exp t = s) (hminus : Complex.exp (-t) = s) (n : ℕ) :
    t^(n^2)*Matrix.det (fun i j : Fin n => exponentialMoment t (i.val+j.val+1)) =
      s^n*(polynomialHankel n).eval₂ (Rat.castHom ℂ) (-t^2) := by
  have h := exponentialMoment_determinant t s ht hplus hminus
    (fun i : Fin n => i.val) (fun j : Fin n => j.val)
  have hn := double_index_sum n
  have hsign : (-1 : ℂ)^((∑ i : Fin n, i.val)+(∑ i : Fin n, i.val)) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [hsign, mul_one, show (∑ i : Fin n, i.val)+(∑ i : Fin n, i.val)+n=n^2 by omega] at h
  exact h

lemma borderColumn_sum (n : ℕ) (hn : 0 < n) :
    (∑ b : Fin n, borderColumn n b) = (∑ b : Fin n, b.val)+1 := by
  cases n with
  | zero => omega
  | succ n =>
    have hc (b : Fin n) : borderColumn (n+1) b.castSucc = b.val := by
      simp only [borderColumn, Fin.val_castSucc]
      rw [ite_eq_right (by have := b.isLt; omega)]
    have hl : borderColumn (n+1) (Fin.last n) = n+1 := by simp [borderColumn]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hc,hl,Fin.val_castSucc,Fin.val_last]
    omega

lemma exponential_border_normalization (t s : ℂ) (ht : t ≠ 0)
    (hplus : Complex.exp t = s) (hminus : Complex.exp (-t) = s)
    (n : ℕ) (hn : 0 < n) :
    t^(n^2+1)*Matrix.det (fun i j : Fin n =>
      exponentialMoment t (i.val+borderColumn n j+1)) =
      -(s^n)*(polynomialBorder n).eval₂ (Rat.castHom ℂ) (-t^2) := by
  have h := exponentialMoment_determinant t s ht hplus hminus
    (fun i : Fin n => i.val) (borderColumn n)
  rw [borderColumn_sum n hn] at h
  have hm := double_index_sum n
  have hs : (-1 : ℂ)^((∑ i : Fin n, i.val)+((∑ i : Fin n, i.val)+1)) = -1 := by
    rw [← add_assoc, ← two_mul, pow_add, pow_mul]
    norm_num
  rw [hs, show (∑ i : Fin n, i.val)+((∑ i : Fin n, i.val)+1)+n=n^2+1 by omega] at h
  simpa [polynomialBorder, Nat.ne_of_gt hn] using h

end OscillatoryRecurrence
