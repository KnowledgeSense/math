import SumsetRanges.OrdinaryConvolutionBounds
import SumsetRanges.OrdinaryLargeConstruction

namespace SumsetRanges

theorem series_coefficient_step_product (P Q R Y : PowerSeries ℤ) (h m : ℕ) (hm : m≤h)
    (he : P-Q=PowerSeries.X^m*R) :
    PowerSeries.coeff h (P*Y)-PowerSeries.coeff h (Q*Y)=PowerSeries.coeff (h-m) (R*Y) := by
  rw [←map_sub,←sub_mul,he,mul_assoc,PowerSeries.coeff_X_pow_mul']
  simp only [ite_eq_left hm]

theorem ordinaryValue_linear_step (h c b x m : ℕ) (r u : ℕ → ℕ)
    (hh : 2≤h) (hc : 2*h^3≤c) (hb : 2≤b) (hx : b-1≤x) (hxb : x≤h*(b-2)+1)
    (hm : m∈Finset.Icc 2 (h-1)) (hn : 4*h*(ordinaryNonfreeSize h r u+2)≤c) :
    ordinaryWeight c b (h-(m+1))≤2*(ordinaryValue h c b r u x-
      ordinaryValue h c b (Function.update r m (r m+1)) u x) ∧
    ordinaryValue h c b r u x-ordinaryValue h c b (Function.update r m (r m+1)) u x≤
      2*ordinaryWeight c b (h-(m+1)) := by
  have hN : ordinaryNonfreeSize h r u+2≤c := by
    have ht := Nat.le_mul_of_pos_left (ordinaryNonfreeSize h r u+2) (by omega : 0<4*h)
    omega
  have hmh : m+1≤h := by have := Finset.mem_Icc.mp hm; omega
  have he := series_coefficient_step_product _ _ _ (ordinarySeries (denseSet (b-1) x)) h (m+1)
    hmh (ordinary_sparse_linear_step h c m r u hm hN)
  change ordinaryValue h c b r u x-ordinaryValue h c b (Function.update r m (r m+1)) u x=_ at he
  rw [he]
  have hch : 2*h≤c := by nlinarith
  have hbds := fun d (hd : d≤h-(m+1)) => ordinary_linear_coefficients h c d r u
    (by omega) hch hN hn (hd.trans (Nat.sub_le _ _))
  simpa only [Nat.cast_one,one_mul,mul_one] using ordinary_series_convolution_bound h c b x (h-(m+1)) 1
    (ordinarySparseSeries h c r u) hh hc hb hx hxb (Nat.sub_le _ _)
    (ordinarySparseSeries_nonneg h c r u)
    (fun d hd => by simpa using (hbds d hd).1) (fun d hd => by simpa using (hbds d hd).2)

theorem ordinaryValue_shared_step (h c b x m : ℕ) (r u : ℕ → ℕ)
    (hh : 2≤h) (hc : 2*h^3≤c) (hb : 2≤b) (hx : b-1≤x) (hxb : x≤h*(b-2)+1)
    (hm : m∈Finset.Icc 2 (h-1)) (hu : 1≤u m) (hn : 4*h*(ordinaryNonfreeSize h r u+2)≤c) :
    (u m : ℤ)*ordinaryWeight c b (h-(m+1))≤2*(ordinaryValue h c b r u x-
      ordinaryValue h c b r (Function.update u m (u m+1)) x) ∧
    ordinaryValue h c b r u x-ordinaryValue h c b r (Function.update u m (u m+1)) x≤
      2*(u m : ℤ)*ordinaryWeight c b (h-(m+1)) := by
  have hN : ordinaryNonfreeSize h r u+2≤c := by
    have ht := Nat.le_mul_of_pos_left (ordinaryNonfreeSize h r u+2) (by omega : 0<4*h)
    omega
  have hmh : m+1≤h := by have := Finset.mem_Icc.mp hm; omega
  have he := series_coefficient_step_product _ _ _ (ordinarySeries (denseSet (b-1) x)) h (m+1)
    hmh (ordinary_sparse_shared_step h c m r u hm hN)
  change ordinaryValue h c b r u x-ordinaryValue h c b r (Function.update u m (u m+1)) x=_ at he
  rw [he]
  have hch : 2*h≤c := by nlinarith
  have hbds := fun d (hd : d≤h-(m+1)) => ordinary_shared_coefficients h c m d r u
    (by omega) hch hm hu hN hn (hd.trans (Nat.sub_le _ _))
  exact ordinary_series_convolution_bound h c b x (h-(m+1)) (u m)
    (ordinarySharedRemainder h c m r u) hh hc hb hx hxb (Nat.sub_le _ _)
    (ordinarySharedRemainder_nonneg h c m r u)
    (fun d hd => (hbds d hd).1) (fun d hd => (hbds d hd).2)

end SumsetRanges
