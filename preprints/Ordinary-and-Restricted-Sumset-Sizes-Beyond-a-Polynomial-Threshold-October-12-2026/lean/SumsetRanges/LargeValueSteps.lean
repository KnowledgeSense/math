import SumsetRanges.DenseConvolutionBounds
import SumsetRanges.LargeConstruction

open Finset Polynomial
namespace SumsetRanges
open scoped Classical

theorem coefficient_step_product (P Q R Y : Polynomial ℤ) (h μ : ℕ) (hm : μ≤h)
    (he : P-Q=X^μ*R) :
    (P*Y).coeff h-(Q*Y).coeff h=(R*Y).coeff (h-μ) := by
  rw [← coeff_sub,← sub_mul,he,mul_assoc,coeff_X_pow_mul']
  simp only [ite_eq_left hm]

theorem largeValue_linear_step (h c b x μ : ℕ) (r u : ℕ → ℕ)
    (hh : 1≤h) (hc : 8*h^2≤c) (hb : 2≤b) (hx : b-1≤x)
    (hμ : μ∈Icc 2 h) (hn : 8*h*(nonfreeSize h r u+2*μ)≤c) :
    restrictedWeight c b (h-μ)≤
      2*(largeValue h c b r u x-largeValue h c b (Function.update r μ (r μ+1)) u x) ∧
    largeValue h c b r u x-largeValue h c b (Function.update r μ (r μ+1)) u x≤
      2*restrictedWeight c b (h-μ) := by
  have hN : nonfreeSize h r u+2*μ≤c := by
    have ht := Nat.le_mul_of_pos_left (nonfreeSize h r u+2*μ) (by omega : 0<8*h)
    omega
  have he := coefficient_step_product _ _ _ (restrictedPolynomial (denseSet (b-1) x)) h μ
    (mem_Icc.mp hμ).2 (sparse_linear_step_factored h c μ r u hμ hN)
  change largeValue h c b r u x-largeValue h c b (Function.update r μ (r μ+1)) u x=_ at he
  rw [he]
  have hch : 2*h≤c := by nlinarith
  have hbds := fun d (hd : d≤h-μ) => linear_step_coefficient_bounds h c μ r u hh hch hμ hn d
    (hd.trans (Nat.sub_le _ _))
  simpa only [Nat.cast_one,one_mul,mul_one] using
    dense_polynomial_convolution_bound h c b x (h-μ) 1 (linearStepRemainder h c μ r u)
      hh hc hb hx (Nat.sub_le _ _) (linearStepRemainder_nonneg h c μ r u)
      (fun d hd => by simpa using (hbds d hd).1)
      (fun d hd => by simpa using (hbds d hd).2)

theorem largeValue_shared_step (h c b x μ : ℕ) (r u : ℕ → ℕ)
    (hh : 1≤h) (hc : 8*h^2≤c) (hb : 2≤b) (hx : b-1≤x)
    (hμ : μ∈Icc 2 h) (hu : 1≤u μ) (hn : 8*h*(nonfreeSize h r u+μ)≤c) :
    (u μ : ℤ)*restrictedWeight c b (h-μ)≤
      2*(largeValue h c b r u x-largeValue h c b r (Function.update u μ (u μ+1)) x) ∧
    largeValue h c b r u x-largeValue h c b r (Function.update u μ (u μ+1)) x≤
      2*(u μ : ℤ)*restrictedWeight c b (h-μ) := by
  have hN : nonfreeSize h r u+μ≤c := by
    have ht := Nat.le_mul_of_pos_left (nonfreeSize h r u+μ) (by omega : 0<8*h)
    omega
  have he := coefficient_step_product _ _ _ (restrictedPolynomial (denseSet (b-1) x)) h μ
    (mem_Icc.mp hμ).2 (sparse_shared_step_factored h c μ r u hμ hN)
  change largeValue h c b r u x-largeValue h c b r (Function.update u μ (u μ+1)) x=_ at he
  rw [he]
  have hch : 2*h≤c := by nlinarith
  have hbds := fun d (hd : d≤h-μ) => shared_step_coefficient_bounds h c μ r u hh hch hμ hu hn d
    (hd.trans (Nat.sub_le _ _))
  exact dense_polynomial_convolution_bound h c b x (h-μ) (u μ) (sharedStepRemainder h c μ r u)
      hh hc hb hx (Nat.sub_le _ _) (sharedStepRemainder_nonneg h c μ r u (mem_Icc.mp hμ).1)
      (fun d hd => (hbds d hd).1) (fun d hd => (hbds d hd).2)

end SumsetRanges
