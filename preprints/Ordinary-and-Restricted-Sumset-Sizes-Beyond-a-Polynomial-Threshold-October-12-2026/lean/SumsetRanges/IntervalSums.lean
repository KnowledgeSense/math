import SumsetRanges.BalancedSubsets
import Mathlib.Algebra.Order.Group.Int.Sum

open Finset
namespace SumsetRanges

theorem sum_range_natCast (q : ℕ) : (∑ i∈range q,(i:ℤ))=(q.choose 2 : ℤ) := by
  rw [← Nat.cast_sum,Finset.sum_range_id,Nat.choose_two_right]

theorem nat_finset_sum_bounds (S : Finset ℕ) (n : ℕ) (hn : 1≤n)
    (hS : S ⊆ range n) :
    S.card.choose 2 ≤ ∑ a∈S,a ∧ (∑ a∈S,a)+S.card.choose 2 ≤ S.card*(n-1) := by
  let T : Finset ℤ := S.image Nat.cast
  have hcard : T.card=S.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hsum : (∑ a∈T,a)=((∑ a∈S,a : ℕ):ℤ) := by
    dsimp only [T]
    rw [Finset.sum_image]
    · exact (Nat.cast_sum S id).symm
    · exact Nat.cast_injective.injOn
  have hlo : ∀ a∈T,(0:ℤ)≤a := by
    intro a ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
    positivity
  have hup : ∀ a∈T,a≤((n-1:ℕ):ℤ) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    have hb' := mem_range.mp (hS hb)
    exact_mod_cast (show b≤n-1 by omega)
  have hl := Finset.sum_range_le_sum hlo
  have hu := Finset.sum_le_sum_range hup
  rw [hcard,hsum] at hl hu
  simp only [zero_add] at hl
  rw [sum_range_natCast] at hl
  rw [Finset.sum_sub_distrib,sum_range_natCast] at hu
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hu
  constructor
  · exact_mod_cast hl
  · have hi : ((∑ a∈S,a : ℕ):ℤ)+(S.card.choose 2 : ℤ) ≤ (S.card:ℤ)*(n-1:ℕ) := by linarith
    exact_mod_cast hi

theorem choose_two_double (q : ℕ) : 2*q.choose 2=q*(q-1) := by
  have h := Finset.sum_range_id_mul_two q
  rw [Finset.sum_range_id,← Nat.choose_two_right] at h
  omega

/-- All restricted q-fold sums of an interval, including every intermediate value. -/
theorem restrictedSums_range (n q : ℕ) (hn : 1≤n) (hqn : q≤n) :
    restrictedSums (range n) q = Icc (q.choose 2) (q*(n-q)+q.choose 2) := by
  ext t
  constructor
  · intro ht
    obtain ⟨S,hS,hSc,rfl⟩ := mem_restrictedSums.mp ht
    have hs := nat_finset_sum_bounds S n hn hS
    rw [hSc] at hs
    apply mem_Icc.mpr
    refine ⟨hs.1,?_⟩
    have hd := choose_two_double q
    have hqn' := Nat.sub_add_cancel hqn
    have hq : q=0 ∨ 1≤q := by omega
    rcases hq with rfl | hq
    · have hS0 : S=∅ := Finset.card_eq_zero.mp hSc
      subst S
      simp
    · have hq' := Nat.sub_add_cancel hq
      have hn' := Nat.sub_add_cancel hn
      nlinarith
  · intro ht
    obtain ⟨hl,hu⟩ := mem_Icc.mp ht
    by_cases hq : q=0
    · subst q
      simp at hl hu
      subst t
      simp
    · have hq' : 0<q := Nat.pos_of_ne_zero hq
      let r := t-q.choose 2
      have hr : r≤q*(n-q) := by omega
      let S := (Finset.univ : Finset (Fin q)).image (balancedPoint q r)
      refine mem_restrictedSums.mpr ⟨S,?_,?_,?_⟩
      · intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
        exact mem_range.mpr (balancedPoint_lt n q r hq' hqn hr i)
      · dsimp only [S]
        rw [Finset.card_image_of_injective _ (balancedPoint_strictMono q r).injective]
        simp
      · dsimp only [S]
        rw [Finset.sum_image]
        · rw [sum_balancedPoint q r hq']
          omega
        · exact (balancedPoint_strictMono q r).injective.injOn

end SumsetRanges
