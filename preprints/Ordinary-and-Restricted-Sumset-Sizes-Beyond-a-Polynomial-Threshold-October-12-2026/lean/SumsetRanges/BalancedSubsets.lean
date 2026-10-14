import SumsetRanges.RestrictedPolynomial

open Finset
namespace SumsetRanges

/-- A q-subset whose sum increases by exactly one as t increases. -/
def balancedPoint (q t : ℕ) (i : Fin q) : ℕ :=
  i.val+t/q+if q-t%q ≤ i.val then 1 else 0

theorem balancedPoint_strictMono (q t : ℕ) : StrictMono (balancedPoint q t) := by
  intro i j hij
  have hval : i.val<j.val := hij
  unfold balancedPoint
  split_ifs <;> omega

theorem balancedPoint_lt (n q t : ℕ) (hq : 0<q) (hqn : q≤n)
    (ht : t≤q*(n-q)) (i : Fin q) : balancedPoint q t i<n := by
  have hrem := Nat.mod_lt t hq
  have hdiv : t/q≤n-q := by
    have hh := Nat.div_le_div_right ht (c := q)
    simpa [Nat.mul_div_cancel_left _ hq] using hh
  have he := Nat.div_add_mod t q
  unfold balancedPoint
  by_cases hi : q-t%q≤i.val
  · rw [ite_eq_left hi]
    have hrpos : 0<t%q := by have := i.isLt; omega
    have hdlt : t/q<n-q := by nlinarith
    have := i.isLt
    omega
  · rw [ite_eq_right hi]
    have := i.isLt
    omega

theorem sum_balancedPoint (q t : ℕ) (hq : 0<q) :
    (∑ i : Fin q, balancedPoint q t i) = q.choose 2+t := by
  unfold balancedPoint
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  have hfirst : (∑ i : Fin q,i.val)=q.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) q,Finset.sum_range_id,Nat.choose_two_right]
  rw [hfirst]
  have hlast : (∑ i : Fin q, if q-t%q≤i.val then 1 else 0)=t%q := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if q-t%q≤i then 1 else 0) q]
    rw [← Finset.sum_filter]
    have hf : (range q).filter (fun i => q-t%q≤i) = Ico (q-t%q) q := by
      ext i
      simp only [mem_filter,mem_range,mem_Ico]
      omega
    rw [hf]
    simp only [Finset.sum_const,smul_eq_mul,mul_one,Nat.card_Ico]
    have := Nat.mod_lt t hq
    omega
  rw [hlast]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have he := Nat.div_add_mod t q
  omega

theorem balancedPoint_mono_parameter (q : ℕ) (t s : ℕ) (hts : t≤s) (i : Fin q) :
    balancedPoint q t i ≤ balancedPoint q s i := by
  have hd : t/q≤s/q := Nat.div_le_div_right hts
  have ht := Nat.div_add_mod t q
  have hs := Nat.div_add_mod s q
  unfold balancedPoint
  by_cases he : t/q=s/q
  · have hr : t%q≤s%q := by rw [he] at ht; omega
    split_ifs <;> omega
  · have hdlt : t/q<s/q := by omega
    split_ifs <;> omega

end SumsetRanges
