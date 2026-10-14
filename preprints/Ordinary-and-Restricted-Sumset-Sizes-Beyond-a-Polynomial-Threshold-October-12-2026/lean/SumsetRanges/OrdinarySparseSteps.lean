import SumsetRanges.OrdinarySparseBounds

open Finset
namespace SumsetRanges

theorem ordinarySparseSeries_factor (h c m : ℕ) (r u : ℕ → ℕ) (hm : m∈Icc 2 (h-1)) :
    ordinarySparseSeries h c r u=geometricSeries^(c-ordinaryNonfreeSize h r u)*
      ordinarySeries (carryG (m+1) (r m))*ordinarySeries (carryH m (u m))*ordinaryOther h m r u := by
  unfold ordinarySparseSeries ordinaryOther
  rw [←Finset.mul_prod_erase _ _ hm]
  ring

theorem ordinaryOther_update_r (h m a : ℕ) (r u : ℕ → ℕ) :
    ordinaryOther h m (Function.update r m a) u=ordinaryOther h m r u := by
  unfold ordinaryOther
  apply Finset.prod_congr rfl
  intro j hj
  have hne : j≠m := (Finset.mem_erase.mp hj).1
  rw [Function.update_of_ne hne]

theorem ordinaryOther_update_u (h m a : ℕ) (r u : ℕ → ℕ) :
    ordinaryOther h m r (Function.update u m a)=ordinaryOther h m r u := by
  unfold ordinaryOther
  apply Finset.prod_congr rfl
  intro j hj
  have hne : j≠m := (Finset.mem_erase.mp hj).1
  rw [Function.update_of_ne hne]

theorem ordinary_sparse_linear_step (h c m : ℕ) (r u : ℕ → ℕ)
    (hm : m∈Icc 2 (h-1)) (hc : ordinaryNonfreeSize h r u+2≤c) :
    ordinarySparseSeries h c r u-ordinarySparseSeries h c (Function.update r m (r m+1)) u=
      PowerSeries.X^(m+1)*ordinarySparseSeries h c r u := by
  rw [ordinarySparseSeries_factor h c m r u hm,
    ordinarySparseSeries_factor h c m (Function.update r m (r m+1)) u hm,
    ordinaryNonfreeSize_step_r h m r u hm,Function.update_self,ordinaryOther_update_r]
  have hf : c-ordinaryNonfreeSize h r u=(c-(ordinaryNonfreeSize h r u+2))+2 := by omega
  have hg := ordinary_carryG_step (m+1) (r m) (by have := mem_Icc.mp hm; omega)
  have he : ordinarySeries (carryG (m+1) (r m+1))=
      geometricSeries^2*ordinarySeries (carryG (m+1) (r m))-
        PowerSeries.X^(m+1)*geometricSeries^2*ordinarySeries (carryG (m+1) (r m)) := by
    rw [←hg]; ring
  rw [he,hf,pow_add]
  ring

noncomputable def ordinarySharedRemainder (h c m : ℕ) (r u : ℕ → ℕ) : PowerSeries ℤ :=
  geometricSeries^(c-(ordinaryNonfreeSize h r u+2))*geometricSeries^(u m+3)*
    ordinarySeries (carryG (m+1) (r m))*ordinaryOther h m r u*
      ∑j∈range (u m),(geometricPolynomial m : PowerSeries ℤ)^j

theorem ordinary_sparse_shared_step (h c m : ℕ) (r u : ℕ → ℕ)
    (hm : m∈Icc 2 (h-1)) (hc : ordinaryNonfreeSize h r u+2≤c) :
    ordinarySparseSeries h c r u-ordinarySparseSeries h c r (Function.update u m (u m+1))=
      PowerSeries.X^(m+1)*ordinarySharedRemainder h c m r u := by
  rw [ordinarySparseSeries_factor h c m r u hm,
    ordinarySparseSeries_factor h c m r (Function.update u m (u m+1)) hm,
    ordinaryNonfreeSize_step_u h m r u hm,Function.update_self,ordinaryOther_update_u]
  have hf : c-ordinaryNonfreeSize h r u=(c-(ordinaryNonfreeSize h r u+2))+2 := by omega
  have hg := ordinary_carryH_step m (u m) (mem_Icc.mp hm).1
  have he : ordinarySeries (carryH m (u m+1))=
      geometricSeries^2*ordinarySeries (carryH m (u m))-
        PowerSeries.X^(m+1)*geometricSeries^(u m+3)*
          ∑j∈range (u m),(geometricPolynomial m : PowerSeries ℤ)^j := by
    rw [←hg]; ring
  rw [he,hf,pow_add]
  unfold ordinarySharedRemainder
  ring

end SumsetRanges
