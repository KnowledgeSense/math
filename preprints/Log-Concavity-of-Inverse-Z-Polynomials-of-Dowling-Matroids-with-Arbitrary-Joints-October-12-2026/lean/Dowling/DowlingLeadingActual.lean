import Dowling.DowlingLeadingCoefficient
import Dowling.FullCandidateIdentification

noncomputable section
namespace Dowling
open PowerSeries
variable (G : Type*) [Group G] [Fintype G]

/-- The source odd-rank coefficient formula for the genuine full Dowling matroid,
including nonabelian gain groups and the trivial gain group. -/
theorem fullP_odd_top (k : ℕ) :
    ((fullP G (2*k+3)).coeff (k+1) : ℝ)=
      (Fintype.card G : ℝ)^(2*k+2)*((2*k+1).doubleFactorial : ℝ)*(2*k+3 : ℝ)^k := by
  have h := dowlingPCandidate_odd_top (Fintype.card G)
    (by exact_mod_cast Fintype.card_ne_zero (α := G)) k
  rw [← fullPSeries_eq_candidate] at h
  change ((2*k+3).factorial : ℝ)*
    (coeff (2*k+3) (invariantEGF (fullP G))).coeff (k+1)=_ at h
  rw [invariantEGF_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_map] at h
  have hf : ((2*k+3).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*k+3)
  change ((2*k+3).factorial : ℝ)*(((2*k+3).factorial : ℝ)⁻¹*
    ((fullP G (2*k+3)).coeff (k+1) : ℝ))=_ at h
  simpa only [← mul_assoc,mul_inv_cancel₀ hf,one_mul] using h

/-- The conventional `h` indexing of the full-Dowling odd-rank input. -/
theorem fullP_odd_top_source (h : ℕ) (hh : 2≤h) :
    ((fullP G (2*h-1)).coeff (h-1) : ℝ)=
      (Fintype.card G : ℝ)^(2*h-2)*((2*h-3).doubleFactorial : ℝ)*(2*h-1 : ℕ)^(h-2) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hh
  subst h
  rw [show 2*(2+k)-1=2*k+3 by omega,show 2+k-1=k+1 by omega,
    show 2*(2+k)-2=2*k+2 by omega,show 2*(2+k)-3=2*k+1 by omega,
    show 2+k-2=k by omega]
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using fullP_odd_top G k

end Dowling
