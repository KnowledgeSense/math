import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace BoseBurton
open Finset

def rankDegreeDomain (r : ℕ) : Finset (Σ _ : ℕ,ℕ) :=
  (Icc 1 r).sigma (fun d=>range (d+1))
def orientationDomain (r : ℕ) : Finset (Σ _ : ℕ,ℕ) :=
  (Icc 1 r).sigma (fun h=>range (min h (r-h)+1))

theorem lower_triangle_sum {A : Type*} [AddCommMonoid A] (r : ℕ) (f : ℕ→ℕ→A) :
    (∑ p∈(rankDegreeDomain r).filter (fun p=>p.2≤p.1-p.2),f p.1 p.2)=
      ∑ p∈orientationDomain r,f (p.1+p.2) p.2 := by
  apply sum_bij (fun p _=>⟨p.1-p.2,p.2⟩)
  · rintro ⟨d,i⟩ hp
    simp only [rankDegreeDomain,orientationDomain,mem_filter,mem_sigma,mem_Icc,mem_range] at hp ⊢
    omega
  · rintro ⟨d,i⟩ hp ⟨e,j⟩ hq he
    simp only [rankDegreeDomain,mem_filter,mem_sigma,mem_Icc,mem_range] at hp hq
    simp only [Sigma.mk.inj_iff,heq_eq_eq] at he ⊢
    omega
  · rintro ⟨h,l⟩ hp
    simp only [orientationDomain,mem_sigma,mem_Icc,mem_range] at hp
    refine ⟨⟨h+l,l⟩,?_,?_⟩
    · simp only [rankDegreeDomain,mem_filter,mem_sigma,mem_Icc,mem_range]
      omega
    · simp
  · rintro ⟨d,i⟩ hp
    simp only [rankDegreeDomain,mem_filter,mem_sigma,mem_Icc,mem_range] at hp
    change f d i=f (d-i+i) i
    rw [Nat.sub_add_cancel (by omega)]

theorem upper_triangle_sum {A : Type*} [AddCommMonoid A] (r : ℕ) (f : ℕ→ℕ→A) :
    (∑ p∈(rankDegreeDomain r).filter (fun p=>¬p.2≤p.1-p.2),f p.1 p.2)=
      ∑ p∈(orientationDomain r).filter (fun p=>p.2<p.1),f (p.1+p.2) p.1 := by
  apply sum_bij (fun p _=>⟨p.2,p.1-p.2⟩)
  · rintro ⟨d,i⟩ hp
    simp only [rankDegreeDomain,orientationDomain,mem_filter,mem_sigma,mem_Icc,mem_range] at hp ⊢
    omega
  · rintro ⟨d,i⟩ hp ⟨e,j⟩ hq he
    simp only [rankDegreeDomain,mem_filter,mem_sigma,mem_Icc,mem_range] at hp hq
    simp only [Sigma.mk.inj_iff,heq_eq_eq] at he ⊢
    omega
  · rintro ⟨h,l⟩ hp
    simp only [orientationDomain,mem_filter,mem_sigma,mem_Icc,mem_range] at hp
    refine ⟨⟨h+l,h⟩,?_,?_⟩
    · simp only [rankDegreeDomain,mem_filter,mem_sigma,mem_Icc,mem_range]
      omega
    · simp
  · rintro ⟨d,i⟩ hp
    simp only [rankDegreeDomain,mem_filter,mem_sigma,mem_Icc,mem_range] at hp
    change f d i=f (i+(d-i)) i
    rw [Nat.add_sub_of_le (by omega)]

theorem triangular_sum_reindex {A : Type*} [AddCommMonoid A] (r : ℕ) (f : ℕ→ℕ→A) :
    (∑ d∈Icc 1 r,∑ i∈range (d+1),f d i)=
      ∑ h∈Icc 1 r,∑ l∈range (min h (r-h)+1),
        (f (h+l) l+if l<h then f (h+l) h else 0) := by
  have h1 : (∑ p∈rankDegreeDomain r,f p.1 p.2)=∑ d∈Icc 1 r,∑ i∈range (d+1),f d i := by
    rw [rankDegreeDomain,sum_sigma]
  have h2 : (∑ p∈orientationDomain r,(f (p.1+p.2) p.2+if p.2<p.1 then f (p.1+p.2) p.1 else 0))=
      ∑ h∈Icc 1 r,∑ l∈range (min h (r-h)+1),(f (h+l) l+if l<h then f (h+l) h else 0) := by
    rw [orientationDomain,sum_sigma]
  rw [← h1,← h2]
  rw [← sum_filter_add_sum_filter_not (rankDegreeDomain r) (fun p=>p.2≤p.1-p.2),
    lower_triangle_sum,upper_triangle_sum,sum_filter,← sum_add_distrib]

end BoseBurton
