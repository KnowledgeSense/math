import AperyMoments.ReciprocalTransformSeriesOuter

noncomputable section
namespace AperyMoments
open Complex Finset
open scoped Topology

theorem reciprocalDoubleTerm_antidiagonal (α R : ℝ) (n : ℕ) :
    (∑ p∈Finset.antidiagonal n,reciprocalDoubleTerm α R p.2 p.1)=
      (reciprocalPolynomial n α:ℂ)/(R:ℂ)^(n+1) := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun k m => reciprocalDoubleTerm α R m k)]
  have he : (∑ k∈range (n+1), (-(α:ℂ))^k*((2*n-k).choose k:ℂ)*
      (spectralMomentCoefficient (n-k) α:ℂ))=(reciprocalPolynomial n α:ℂ) := by
    exact_mod_cast reciprocal_spectral_coefficients n α
  rw [← he,Finset.sum_div]
  apply sum_congr rfl
  intro k hk
  have hk' : k≤n := Nat.le_of_lt_succ (mem_range.mp hk)
  simp only [reciprocalDoubleTerm]
  rw [show 2*(n-k)+k=2*n-k by omega,show n-k+k+1=n+1 by omega]
  ring

theorem reciprocal_transform_hasSum {α R : ℝ} (hα : 0<α) (hα1 : α≤1)
    (hR : 256<R) :
    HasSum (fun n=>(reciprocalPolynomial n α:ℂ)/(R:ℂ)^(n+1))
      (outerResolvent α (R:ℂ)) := by
  have hs := reciprocalDoubleTerm_summable hα.le hα1 hR
  have ht := hs.hasSum.prod_fiberwise (reciprocalDoubleTerm_hasSum hα.le hα1 hR)
  have he := ht.unique (reciprocalEvenTerm_hasSum hα hα1 hR)
  have hd : HasSum (fun p:ℕ×ℕ=>reciprocalDoubleTerm α R p.1 p.2)
      (outerResolvent α (R:ℂ)) := he ▸ hs.hasSum
  have hswap : HasSum (fun p:ℕ×ℕ=>reciprocalDoubleTerm α R p.2 p.1)
      (outerResolvent α (R:ℂ)) := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hd
  have hsig := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr hswap
  have hf (n : ℕ) : HasSum
      (fun p:Finset.antidiagonal n=>reciprocalDoubleTerm α R p.val.2 p.val.1)
      ((reciprocalPolynomial n α:ℂ)/(R:ℂ)^(n+1)) := by
    have heq : (∑ p:Finset.antidiagonal n,reciprocalDoubleTerm α R p.val.2 p.val.1)=
        (reciprocalPolynomial n α:ℂ)/(R:ℂ)^(n+1) := by
      rw [Finset.sum_coe_sort (Finset.antidiagonal n) (fun p:ℕ×ℕ=>reciprocalDoubleTerm α R p.2 p.1)]
      exact reciprocalDoubleTerm_antidiagonal α R n
    rw [← heq]
    exact hasSum_fintype _

  exact hsig.sigma hf

end AperyMoments
