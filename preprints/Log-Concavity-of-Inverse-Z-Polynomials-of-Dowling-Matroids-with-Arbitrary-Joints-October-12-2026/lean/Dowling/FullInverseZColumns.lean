import Dowling.ActualBlockSeries
import Dowling.FullInverseZFlatConvolution

noncomputable section
namespace Dowling
open scoped Classical BigOperators
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

def partitionColumn (G : Type*) [Group G] [Fintype G] (n k : ℕ) : Polynomial ℝ :=
  ∑ p : GainPartition G n with p.roots.card=k, (partitionZ p).map (Int.castRingHom ℝ)

theorem partitionColumn_factorial (n k : ℕ) :
    (k.factorial : Polynomial ℝ)*partitionColumn G n k =
      (n.factorial : Polynomial ℝ)*coeff n
        (fullZSeries G*dowlingBlockCoordinate (Fintype.card G)^k) := by
  rw [partitionColumn,partitionZ_color_enumeration]
  have h := labeledColorSum_eq_factorial_coeff (flatColorWeight (k := k) G) n
  rw [labeledColorProduct_flat] at h
  unfold labeledColorSum labeledColorCount at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.prod_congr rfl
  intro c _
  congr 2
  ext i
  simp

theorem partitionColumn_coeff (n k : ℕ) :
    coeff n (fullZSeries G*dowlingBlockCoordinate (Fintype.card G)^k) =
      Polynomial.C ((k.factorial : ℝ)/(n.factorial : ℝ))*partitionColumn G n k := by
  have hn : (n.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hunit : Polynomial.C ((n.factorial : ℝ)⁻¹)*(n.factorial : Polynomial ℝ)=1 := by
    rw [← map_natCast Polynomial.C,← Polynomial.C_mul,inv_mul_cancel₀ hn,Polynomial.C_1]
  calc
    _ = Polynomial.C ((n.factorial : ℝ)⁻¹)*
        ((n.factorial : Polynomial ℝ)*coeff n
          (fullZSeries G*dowlingBlockCoordinate (Fintype.card G)^k)) := by
            rw [← mul_assoc,hunit,one_mul]
    _ = Polynomial.C ((n.factorial : ℝ)⁻¹)*
        ((k.factorial : Polynomial ℝ)*partitionColumn G n k) := by rw [partitionColumn_factorial]
    _ = _ := by
      rw [← map_natCast Polynomial.C,← mul_assoc,← Polynomial.C_mul]
      congr 2
      rw [div_eq_mul_inv,mul_comm]

theorem partitionColumn_convolution (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), partitionColumn G n k *
      (Polynomial.C ((-1:ℝ)^k)*(fullY G k).map (Int.castRingHom ℝ))) =
      if n=0 then 1 else 0 := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (full_inverseZ_flat_convolution (G := G) n)
  simp only [Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_neg,Polynomial.map_one,map_pow,map_neg,map_one] at h
  have he : (∑ p : GainPartition G n, (partitionZ p).map (Int.castRingHom ℝ)*
      (Polynomial.C ((-1:ℝ)^p.roots.card)*(fullY G p.roots.card).map (Int.castRingHom ℝ))) =
      ∑ k ∈ Finset.range (n+1), partitionColumn G n k *
        (Polynomial.C ((-1:ℝ)^k)*(fullY G k).map (Int.castRingHom ℝ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_range.mpr (Nat.lt_succ_of_le p.roots_card_le))]
    apply Finset.sum_congr rfl
    intro k _
    rw [partitionColumn,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  simp only [map_pow,map_neg,map_one] at he
  rw [he] at h
  by_cases hn : n=0 <;> simpa only [hn,ite_true,ite_false,Polynomial.map_one,Polynomial.map_zero,map_pow,map_neg,map_one] using h

end Dowling
