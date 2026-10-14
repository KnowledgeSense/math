import SumsetRanges.OrdinaryDenseSets
import SumsetRanges.SeriesAgreement

open Finset
namespace SumsetRanges

theorem dense_ordinary_step (L x q : ℕ) (hx : L≤x) :
    (ordinarySums (denseSet (L+1) x) q).card≤(ordinarySums (denseSet (L+1) (x+1)) q).card ∧
    (ordinarySums (denseSet (L+1) (x+1)) q).card≤(ordinarySums (denseSet (L+1) x) q).card+q := by
  rw [card_dense_ordinary L x q hx,card_dense_ordinary L (x+1) q (by omega)]
  have h0 : (∑i∈range q,min x ((i+1)*L+1))≤∑i∈range q,min (x+1) ((i+1)*L+1) :=
    Finset.sum_le_sum (fun i _ => by omega)
  have h1 : (∑i∈range q,min (x+1) ((i+1)*L+1))≤∑i∈range q,(min x ((i+1)*L+1)+1) :=
    Finset.sum_le_sum (fun i _ => by omega)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one] at h1
  omega

theorem dense_ordinary_bound (h L x q : ℕ) (hh : 2≤h) (hx : L≤x)
    (hxh : x≤h*L+1) (hq : q≤h) :
    (ordinarySums (denseSet (L+1) x) q).card≤h^2*(L+2) := by
  rw [card_dense_ordinary L x q hx]
  have hs : (∑i∈range q,min x ((i+1)*L+1))≤q*x := by
    calc
      _ ≤ ∑_i∈range q,x := Finset.sum_le_sum (fun i _ => min_le_left _ _)
      _ = _ := by simp
  have hp := Nat.mul_le_mul hq hxh
  nlinarith

theorem dense_ordinary_endpoint (h L q : ℕ) (hq : q≤h) :
    (ordinarySums (denseSet (L+1) (h*L+1)) q).card=
      ∑i∈range (q+1),(ordinarySums (Icc 0 L) i).card := by
  have hx : L≤h*L+1 ∨ q=0 := by
    by_cases hz : h=0
    · right; omega
    · left
      have hp : 1≤h := by omega
      nlinarith
  rcases hx with hx | rfl
  · rw [card_dense_ordinary L (h*L+1) q hx]
    have he (i : ℕ) (hi : i∈range q) : min (h*L+1) ((i+1)*L+1)=(i+1)*L+1 := by
      apply min_eq_right
      have hip : i+1≤h := by have := mem_range.mp hi; omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_right L hip) 1
    simp_rw [ordinarySums_nat_Icc,Nat.card_Icc,Nat.sub_zero]
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_mul,Nat.zero_add]
    rw [Finset.sum_congr rfl he,Nat.add_comm]
  · simp [ordinarySums]

end SumsetRanges
