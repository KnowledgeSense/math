import OscillatoryRecurrence.EndpointExpansion
import OscillatoryRecurrence.Nonvanishing
import Mathlib.Algebra.Polynomial.Reverse

noncomputable section
open Polynomial Finset
open scoped BigOperators
namespace OscillatoryRecurrence

 theorem endpointExpansion_X_pow_degree (r : ℕ) :
    (endpointExpansion ((X:ℚ[X])^r)).natDegree≤r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [endpointExpansion_X_pow_succ]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      rw [natDegree_X,natDegree_C]
      omega
    · apply natDegree_mul_le.trans
      have h := natDegree_C_mul_le ((r:ℚ)+1) (X:ℚ[X])
      simp only [natDegree_X] at h
      omega

 theorem endpoint_det_degree {n : ℕ} (a b : Fin n → ℕ) :
    (Matrix.det (Matrix.of (fun i j => endpointExpansion ((X:ℚ[X])^(a i+b j+1))))).natDegree≤
      (∑ i,a i)+(∑ j,b j)+n := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ i : Fin n, (a (σ i)+b i+1) :=
      sum_le_sum (fun i _ => endpointExpansion_X_pow_degree _)
    _ = _ := by
      simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      rw [Equiv.sum_comp σ a]
      simp only [Nat.cast_id]

 def endpointHankel (n : ℕ) : ℚ[X] :=
  Matrix.det (Matrix.of (fun i j : Fin n => endpointExpansion (X^(i.val+j.val+1))))

 theorem endpointHankel_degree (n : ℕ) : (endpointHankel n).natDegree≤n^2 := by
  have h := endpoint_det_degree (fun i : Fin n => i.val) (fun j : Fin n => j.val)
  have he := double_index_sum n
  dsimp only [endpointHankel]
  convert h using 1
  omega

 theorem endpoint_det_eval (t s : ℂ) (ht : t≠0)
    (hplus : Complex.exp t=s) (hminus : Complex.exp (-t)=s)
    {n : ℕ} (a b : Fin n → ℕ) :
    s^n*(Matrix.det (Matrix.of (fun i j => endpointExpansion ((X:ℚ[X])^(a i+b j+1))))).eval₂
      (Rat.castHom ℂ) t⁻¹ =
      Matrix.det (Matrix.of (fun i j => exponentialMoment t (a i+b j+1))) := by
  have he := (Polynomial.eval₂RingHom (Rat.castHom ℂ) t⁻¹).map_det
    (fun i j => endpointExpansion ((X:ℚ[X])^(a i+b j+1)))
  change (Matrix.det (Matrix.of (fun i j => endpointExpansion ((X:ℚ[X])^(a i+b j+1))))).eval₂
    (Rat.castHom ℂ) t⁻¹ = Matrix.det (Matrix.of (fun i j =>
      (endpointExpansion ((X:ℚ[X])^(a i+b j+1))).eval₂ (Rat.castHom ℂ) t⁻¹)) at he
  rw [he]
  have hs := Matrix.det_smul (Matrix.of (fun i j : Fin n =>
    (endpointExpansion ((X:ℚ[X])^(a i+b j+1))).eval₂ (Rat.castHom ℂ) t⁻¹)) s
  simp only [Fintype.card_fin] at hs
  rw [← hs]
  congr 1
  ext i j
  exact endpointExpansion_exponentialMoment t s ht hplus hminus _

 theorem imaginary_pi_transcendental : Transcendental ℚ (Complex.I*(Real.pi:ℂ)) := by
  intro h
  have hsq := h.pow 2
  have he : -(Complex.I*(Real.pi:ℂ))^2=(Real.pi:ℂ)^2 := by
    rw [mul_pow,Complex.I_sq]
    ring
  have hh := hsq.neg
  rw [he] at hh
  exact squared_frequency_transcendental 1 (by norm_num) (by simpa using hh)

 theorem endpointHankel_reflect (n : ℕ) :
    (endpointHankel n).reflect (n^2)=(polynomialHankel n).comp (-(X:ℚ[X])^2) := by
  let t : ℂ := Complex.I*(Real.pi:ℂ)
  have ht : t≠0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  let : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have hp : Complex.exp t=(-1:ℂ) := by simpa [t] using integral_frequency_exp 1
  have hm : Complex.exp (-t)=(-1:ℂ) := by simpa [t] using integral_frequency_exp_neg 1
  have he := endpoint_det_eval t (-1) ht hp hm
    (fun i : Fin n => i.val) (fun j : Fin n => j.val)
  have hn := exponential_hankel_normalization t (-1) ht hp hm n
  change (-1:ℂ)^n*(endpointHankel n).eval₂ (Rat.castHom ℂ) t⁻¹=
    Matrix.det (fun i j : Fin n => exponentialMoment t (i.val+j.val+1)) at he
  rw [← he] at hn
  have hr := eval₂_reflect_mul_pow (Rat.castHom ℂ) t⁻¹ (n^2) (endpointHankel n)
    (endpointHankel_degree n)
  simp only [invOf_eq_inv,inv_inv,inv_pow] at hr
  have hr' : ((endpointHankel n).reflect (n^2)).eval₂ (Rat.castHom ℂ) t=
      t^(n^2)*(endpointHankel n).eval₂ (Rat.castHom ℂ) t⁻¹ := by
    field_simp [ht] at hr
    simpa only [mul_comm,one_div] using hr
  apply (transcendental_iff_injective.mp imaginary_pi_transcendental)
  change ((endpointHankel n).reflect (n^2)).eval₂ (Rat.castHom ℂ) t=
    ((polynomialHankel n).comp (-(X:ℚ[X])^2)).eval₂ (Rat.castHom ℂ) t
  rw [eval₂_comp,eval₂_neg,eval₂_pow,eval₂_X,hr']
  apply mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1:ℂ)≠0))
  linear_combination hn

 def endpointBorder (n : ℕ) : ℚ[X] :=
  if n=0 then 0 else Matrix.det (Matrix.of (fun i j : Fin n =>
    endpointExpansion (X^(i.val+borderColumn n j+1))))

 theorem endpointBorder_degree (n : ℕ) : (endpointBorder n).natDegree≤n^2+1 := by
  by_cases hn : n=0
  · simp [endpointBorder,hn]
  · have h := endpoint_det_degree (fun i : Fin n => i.val) (borderColumn n)
    rw [borderColumn_sum n (Nat.pos_of_ne_zero hn)] at h
    have he := double_index_sum n
    dsimp only [endpointBorder]
    rw [ite_eq_right hn]
    convert h using 1
    omega

 theorem endpointBorder_reflect (n : ℕ) :
    (endpointBorder n).reflect (n^2+1)=-(polynomialBorder n).comp (-(X:ℚ[X])^2) := by
  by_cases hn0 : n=0
  · subst n
    simp [endpointBorder,polynomialBorder,reflect_zero]
  let t : ℂ := Complex.I*(Real.pi:ℂ)
  have ht : t≠0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  let : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have hp : Complex.exp t=(-1:ℂ) := by simpa [t] using integral_frequency_exp 1
  have hm : Complex.exp (-t)=(-1:ℂ) := by simpa [t] using integral_frequency_exp_neg 1
  have he := endpoint_det_eval t (-1) ht hp hm
    (fun i : Fin n => i.val) (borderColumn n)
  have he' : (-1:ℂ)^n*(endpointBorder n).eval₂ (Rat.castHom ℂ) t⁻¹=
      Matrix.det (fun i j : Fin n => exponentialMoment t (i.val+borderColumn n j+1)) := by
    unfold endpointBorder
    rw [ite_eq_right hn0]
    exact he
  have hn := exponential_border_normalization t (-1) ht hp hm n (Nat.pos_of_ne_zero hn0)
  rw [← he'] at hn
  have hr := eval₂_reflect_mul_pow (Rat.castHom ℂ) t⁻¹ (n^2+1) (endpointBorder n)
    (endpointBorder_degree n)
  simp only [invOf_eq_inv,inv_inv,inv_pow] at hr
  have hr' : ((endpointBorder n).reflect (n^2+1)).eval₂ (Rat.castHom ℂ) t=
      t^(n^2+1)*(endpointBorder n).eval₂ (Rat.castHom ℂ) t⁻¹ := by
    field_simp [ht] at hr
    simpa only [mul_comm,one_div] using hr
  apply (transcendental_iff_injective.mp imaginary_pi_transcendental)
  change ((endpointBorder n).reflect (n^2+1)).eval₂ (Rat.castHom ℂ) t=
    (-(polynomialBorder n).comp (-(X:ℚ[X])^2)).eval₂ (Rat.castHom ℂ) t
  rw [eval₂_neg,eval₂_comp,eval₂_neg,eval₂_pow,eval₂_X,hr']
  apply mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1:ℂ)≠0))
  linear_combination hn

end OscillatoryRecurrence
