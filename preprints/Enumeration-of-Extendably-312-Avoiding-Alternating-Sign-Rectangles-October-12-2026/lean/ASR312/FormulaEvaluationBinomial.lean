import ASR312.Formula
import ASR312.SeriesDefinitions
import Mathlib.RingTheory.PowerSeries.Binomial

noncomputable section
open PowerSeries Finset
open scoped BigOperators
namespace ASR312

/-- Formal integer powers of `1 + X`, including negative exponents. -/
def B (r : ℤ) : PowerSeries ℚ := binomialSeries ℚ r

@[simp] theorem coeff_B (r : ℤ) (n : ℕ) :
    coeff n (B r)=((Ring.choose r n : ℤ) : ℚ) := by
  simp only [B,binomialSeries_coeff,zsmul_eq_mul,mul_one]

@[simp] theorem constantCoeff_B (r : ℤ) : constantCoeff (B r)=1 := by
  simp [B]

theorem B_add (r s : ℤ) : B (r+s)=B r*B s := binomialSeries_add r s

theorem B_nat (r : ℕ) : B (r:ℤ)=(1+X)^r := binomialSeries_nat r

theorem coeff_shift_B (r : ℤ) (n j : ℕ) :
    coeff n (X^j*B r)=(generalizedBinomial r ((n:ℤ)-j):ℚ) := by
  rw [coeff_X_pow_mul']
  by_cases hj : j ≤ n
  · rw [ite_eq_left hj,coeff_B]
    unfold generalizedBinomial
    rw [ite_eq_right (by omega),show ((n:ℤ)-j).toNat=n-j by omega]
  · rw [ite_eq_right hj]
    unfold generalizedBinomial
    rw [ite_eq_left (by omega)]
    norm_num

def weightedBinomialSeries (k : ℕ) : PowerSeries ℚ :=
  C (1/2)*((1+C 2*X)^k-1)

theorem one_add_two_X_pow_rescale (k : ℕ) :
    (1+C 2*X : PowerSeries ℚ)^k = rescale 2 ((1+X)^k) := by
  simp

theorem coeff_one_add_two_X_pow (k i : ℕ) :
    coeff i ((1+C 2*X : PowerSeries ℚ)^k)=(2:ℚ)^i*(k.choose i:ℚ) := by
  rw [one_add_two_X_pow_rescale,coeff_rescale,← B_nat,coeff_B]
  simp [Ring.choose_natCast]

theorem weightedBinomialSeries_coeff (k i : ℕ) :
    coeff i (weightedBinomialSeries k) =
      if i=0 then 0 else (2:ℚ)^(i-1)*(k.choose i:ℚ) := by
  rw [weightedBinomialSeries,coeff_C_mul,map_sub,coeff_one_add_two_X_pow,coeff_one]
  by_cases hi : i=0
  · subst i
    simp
  · rw [ite_eq_right hi,ite_eq_right hi,sub_zero]
    have hp : (2:ℚ)^i=2*2^(i-1) := by
      conv_lhs => rw [show i=i-1+1 by omega,pow_succ]
      ring
    rw [hp]
    ring

theorem coeff_product_range (f g : PowerSeries ℚ) (n : ℕ) :
    coeff n (f*g)=∑ i ∈ range (n+1), coeff i f*coeff (n-i) g := by
  rw [coeff_mul]
  exact Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f*coeff j g) n

theorem coeff_B_correction (r : ℤ) (n : ℕ) :
    coeff n (B r*(1-C 2*X^2))=
      (generalizedBinomial r n:ℚ)-2*(generalizedBinomial r ((n:ℤ)-2):ℚ) := by
  have he : B r*(1-C 2*X^2)=B r-C 2*(X^2*B r) := by ring
  have hb : coeff n (B r)=(generalizedBinomial r n:ℚ) := by
    simpa using coeff_shift_B r n 0
  rw [he,map_sub,coeff_C_mul,hb,coeff_shift_B]
  norm_num

theorem weighted_binomial_product_coeff (r : ℤ) (k d : ℕ) :
    coeff d (weightedBinomialSeries k*(B r*(1-C 2*X^2)))=
      ∑ i ∈ Icc 1 d, (2:ℚ)^(i-1)*(k.choose i:ℚ)*
        ((generalizedBinomial r ((d:ℤ)-i):ℚ)-
          2*(generalizedBinomial r ((d:ℤ)-i-2):ℚ)) := by
  rw [coeff_product_range]
  have hs : Icc 1 d ⊆ range (d+1) := by
    intro i hi
    have := mem_Icc.mp hi
    exact mem_range.mpr (by omega)
  calc
    _ = ∑ i ∈ Icc 1 d, coeff i (weightedBinomialSeries k)*
        coeff (d-i) (B r*(1-C 2*X^2)) := by
      symm
      apply sum_subset hs
      intro i hi hnot
      have hi0 : i=0 := by
        have := mem_range.mp hi
        simp only [mem_Icc,not_and] at hnot
        omega
      subst i
      simp [weightedBinomialSeries_coeff]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      obtain ⟨hi1,hid⟩ := mem_Icc.mp hi
      rw [weightedBinomialSeries_coeff,ite_eq_right (by omega),coeff_B_correction,
        Nat.cast_sub hid]

end ASR312
