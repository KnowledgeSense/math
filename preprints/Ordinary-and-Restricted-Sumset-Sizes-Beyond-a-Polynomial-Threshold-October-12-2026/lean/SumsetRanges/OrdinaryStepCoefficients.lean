import SumsetRanges.OrdinarySharedRemainder

namespace SumsetRanges

theorem ordinary_series_coefficient_sandwich (h c n ell d : ℕ) (P : PowerSeries ℤ)
    (hh : 1≤h) (hc : 2*h≤c) (hn : 1≤n) (hnc : n≤c)
    (hgap : 4*h*(c-n)≤c) (hd : d≤h)
    (hlo : SeriesLE ((ell : PowerSeries ℤ)*geometricSeries^n) P)
    (hhi : SeriesLE P ((ell : PowerSeries ℤ)*geometricSeries^c)) :
    (ell : ℤ)*ordinaryBeta c d≤2*PowerSeries.coeff d P ∧
      PowerSeries.coeff d P≤(ell : ℤ)*ordinaryBeta c d := by
  have hncoef := hlo d
  have hccoef := hhi d
  have he : (ell : PowerSeries ℤ)=PowerSeries.C (ell : ℤ) := by simp
  rw [he,PowerSeries.coeff_C_mul,coeff_geometricSeries_pow n d hn] at hncoef
  rw [he,PowerSeries.coeff_C_mul,coeff_geometricSeries_pow c d (by omega)] at hccoef
  have hb := ordinaryBeta_half h c n d hh hc hn hnc hgap hd
  have hb' : (ordinaryBeta c d : ℤ)≤2*(ordinaryBeta n d : ℤ) := by exact_mod_cast hb
  have hm := mul_le_mul_of_nonneg_left hb' (Int.natCast_nonneg ell)
  constructor
  · nlinarith
  · exact hccoef

theorem ordinary_free_after_step (h c ν : ℕ) (hh : 1≤h) (hc : 2*h≤c)
    (hν : ν+2≤c) (hgap : 4*h*(ν+2)≤c) :
    1≤c-(ν+2) ∧ c-(ν+2)≤c ∧ 4*h*(c-(c-(ν+2)))≤c := by
  have he : c-(c-(ν+2))=ν+2 := by omega
  refine ⟨?_,Nat.sub_le _ _,by rw [he]; exact hgap⟩
  by_contra hn
  have hce : c=ν+2 := by omega
  rw [←hce] at hgap
  nlinarith

theorem ordinary_linear_coefficients (h c d : ℕ) (r u : ℕ → ℕ)
    (hh : 1≤h) (hc : 2*h≤c) (hν : ordinaryNonfreeSize h r u+2≤c)
    (hgap : 4*h*(ordinaryNonfreeSize h r u+2)≤c) (hd : d≤h) :
    (ordinaryBeta c d : ℤ)≤2*PowerSeries.coeff d (ordinarySparseSeries h c r u) ∧
      PowerSeries.coeff d (ordinarySparseSeries h c r u)≤ordinaryBeta c d := by
  have hf := ordinary_free_after_step h c (ordinaryNonfreeSize h r u) hh hc hν hgap
  have hlo := (geometricSeries_pow_mono (c-(ordinaryNonfreeSize h r u+2)) (c-ordinaryNonfreeSize h r u) (by omega)).trans
    (ordinarySparseSeries_lower h c r u)
  have he := ordinary_series_coefficient_sandwich h c (c-(ordinaryNonfreeSize h r u+2)) 1 d
    (ordinarySparseSeries h c r u) hh hc hf.1 hf.2.1 hf.2.2 hd
    (by simpa using hlo) (by simpa using ordinarySparseSeries_upper h c r u (by omega))
  simpa using he

theorem ordinary_shared_coefficients (h c m d : ℕ) (r u : ℕ → ℕ)
    (hh : 1≤h) (hc : 2*h≤c) (hm : m∈Finset.Icc 2 (h-1)) (hu : 1≤u m)
    (hν : ordinaryNonfreeSize h r u+2≤c) (hgap : 4*h*(ordinaryNonfreeSize h r u+2)≤c) (hd : d≤h) :
    (u m : ℤ)*ordinaryBeta c d≤2*PowerSeries.coeff d (ordinarySharedRemainder h c m r u) ∧
      PowerSeries.coeff d (ordinarySharedRemainder h c m r u)≤(u m : ℤ)*ordinaryBeta c d := by
  have hf := ordinary_free_after_step h c (ordinaryNonfreeSize h r u) hh hc hν hgap
  exact ordinary_series_coefficient_sandwich h c (c-(ordinaryNonfreeSize h r u+2)) (u m) d
    (ordinarySharedRemainder h c m r u) hh hc hf.1 hf.2.1 hf.2.2 hd
    (ordinarySharedRemainder_lower h c m r u (Finset.mem_Icc.mp hm).1)
    (ordinarySharedRemainder_upper h c m r u hm hu hν)

end SumsetRanges
