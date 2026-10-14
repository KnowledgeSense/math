import Dowling.SmallRankInvariants

noncomputable section
namespace Dowling
open Finset Polynomial
variable {G : Type*} [Group G] [Fintype G]

theorem dowlingScalarCoefficient_zero (a : ℝ) (n : ℕ) :
    dowlingScalarCoefficient a n 0=dowlingBinomialWeight a n := by
  simp [dowlingScalarCoefficient,dowlingBinomialWeight_zero]

theorem fullY_constant_real (n : ℕ) :
    ((fullY G n).coeff 0 : ℝ)=(n.factorial : ℝ)*(Fintype.card G : ℝ)^n*
      dowlingBinomialWeight (Fintype.card G : ℝ)⁻¹ n := by
  rw [fullY_coeff_real,dowlingScalarCoefficient_zero]

theorem fullY_constant_succ (n : ℕ) :
    (fullY G (n+1)).coeff 0=((Fintype.card G : ℤ)*n+1)*(fullY G n).coeff 0 := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [fullY_constant_real,fullY_constant_real,Nat.factorial_succ,pow_succ]
  push_cast
  let m : ℝ := Fintype.card G
  have hm : m≠0 := by dsimp [m]; exact_mod_cast Fintype.card_ne_zero (α := G)
  have hb := dowlingBinomialWeight_succ m⁻¹ n
  change (n+1)*(n.factorial : ℝ)*(m^n*m)*dowlingBinomialWeight m⁻¹ (n+1)=
    (m*n+1)*((n.factorial : ℝ)*m^n*dowlingBinomialWeight m⁻¹ n)
  calc
    _ = (n.factorial : ℝ)*m^n*m*((n+1)*dowlingBinomialWeight m⁻¹ (n+1)) := by ring
    _ = (n.factorial : ℝ)*m^n*m*((m⁻¹+n)*dowlingBinomialWeight m⁻¹ n) := by rw [hb]
    _ = _ := by field_simp; ring

theorem fullY_constant_product (n : ℕ) :
    (fullY G n).coeff 0=∏ j∈range n,((Fintype.card G : ℤ)*j+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [fullY_constant_succ,ih,Finset.prod_range_succ,mul_comm]

end Dowling
