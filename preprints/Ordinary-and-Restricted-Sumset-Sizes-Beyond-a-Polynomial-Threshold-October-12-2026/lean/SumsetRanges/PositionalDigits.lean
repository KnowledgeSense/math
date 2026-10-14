import SumsetRanges.OrdinaryBasics
import SumsetRanges.RadixMap

open Finset
namespace SumsetRanges

/-- Every integer below a radix power has a bounded digit vector of the specified length. -/
theorem bounded_digits (g r t : ℕ) (hg : 1≤g) (ht : t<g^r) :
    ∃v : Fin r → ℕ, (∀i,v i<g) ∧ ∑i,v i*g^i.val=t := by
  induction r generalizing t with
  | zero =>
      have ht0 : t=0 := by simpa using ht
      subst t
      exact ⟨Fin.elim0,fun i => Fin.elim0 i,by simp⟩
  | succ r ih =>
      have hdiv : t/g<g^r := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [pow_succ,mul_comm] using ht)
      obtain ⟨v,hv,he⟩ := ih (t/g) hdiv
      refine ⟨Fin.cons (t%g) v,?_,?_⟩
      · intro i
        exact Fin.cases (Nat.mod_lt t (by omega)) hv i
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.val_zero,pow_zero,mul_one,Fin.cons_succ,Fin.val_succ,pow_succ]
        have hs : (∑i : Fin r,v i*(g^i.val*g))=(∑i : Fin r,v i*g^i.val)*g := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _; ring
        rw [hs,he]
        simpa [mul_comm] using Nat.mod_add_div t g

theorem maximal_digit_sum (g r : ℕ) (hg : 1≤g) :
    (∑i : Fin r,(g-1)*g^i.val)+1=g^r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [pow_succ]
      have hg' : g-1+1=g := by omega
      calc
        _ = (∑i : Fin r,(g-1)*g^i.val)+1+(g-1)*g^r := by omega
        _ = g^r+(g-1)*g^r := by rw [ih]
        _ = (g-1+1)*g^r := by ring
        _ = g^r*g := by rw [hg']; ring

def digitSet (g i : ℕ) : Finset ℕ := (Finset.range g).image (fun j => j*g^i)

@[simp] theorem mem_digitSet (g i x : ℕ) : x∈digitSet g i ↔ ∃j<g,j*g^i=x := by
  simp [digitSet]

theorem card_digitSet (g i : ℕ) (hg : 1≤g) : (digitSet g i).card=g := by
  rw [digitSet,Finset.card_image_of_injective]
  · simp
  · intro a b he
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0<g^i) he

theorem digitSet_lt_power (g r i : ℕ) (hg : 1≤g) (hi : i<r)
    {x : ℕ} (hx : x∈digitSet g i) : x<g^r := by
  obtain ⟨j,hj,rfl⟩ := (mem_digitSet g i x).mp hx
  calc
    j*g^i < g*g^i := Nat.mul_lt_mul_of_pos_right hj (by positivity)
    _ = g^(i+1) := by rw [pow_succ,mul_comm]
    _ ≤ g^r := Nat.pow_le_pow_right hg (by omega)

end SumsetRanges
