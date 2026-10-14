import Dowling.DeletionIncidencePush

noncomputable section
namespace Dowling
open Finset LaurentPolynomial MatroidInverseZ
open scoped Classical
variable {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]
  [LocallyFiniteOrder α]

theorem deletionLift_shift (d e : ℤ) (p : Polynomial ℤ) :
    T d*deletionLift e p=deletionLift (d+e) p := by
  rw [deletionLift,deletionLift,T_add,mul_assoc]

omit [Fintype β] [PartialOrder β] in
/-- A rank-preserving top has a polynomial-supported pushed KL vector. -/
theorem deletionKL_push_polynomial (r : α→ℕ) (s : β→ℕ) (d : α→β)
    (hdrop : ∀ a,r a≤s (d a)+1) (b : α) (hb : s (d b)=r b) (x : β) :
    ∃ p : Polynomial ℤ,deletionPush r s d (deletionKLVector r b) x=p.toLaurent := by
  have ht : ∀ a,∃ p : Polynomial ℤ,
      (if d a=x then T ((s x : ℤ)-r a)*deletionKLVector r b a else 0)=p.toLaurent := by
    intro a
    by_cases hax : d a=x
    · rw [ite_eq_left hax]
      by_cases hab : a≤b
      · rw [deletionKLVector,ite_eq_left hab,deletionLift_shift]
        by_cases he : a=b
        · subst a
          have heq : (s x : ℤ)-r b+((r b : ℤ)-r b)=0 := by rw [← hax,hb]; omega
          exact ⟨1,by rw [heq,kl_self]; simp [deletionLift_one]⟩
        apply deletionLift_polynomial
        intro k hk
        have hlt : 2*k<r b-r a := by
          by_contra h
          exact hk (kl_high_coeff r a b he k (by omega))
        have hda := hdrop a
        rw [hax] at hda
        omega
      · exact ⟨0,by simp [deletionKLVector,hab]⟩
    · exact ⟨0,by simp [hax]⟩
  choose p hp using ht
  refine ⟨∑ a,p a,?_⟩
  rw [map_sum]
  exact sum_congr rfl (fun a _=>hp a)

 theorem deletionKL_push_perverse (r : α→ℕ) (s : β→ℕ) (d : α→β) (c : β→α)
    (hr : Monotone r) (hgc : ∀ x a,c x≤a↔x≤d a) (hcr : ∀ x,r (c x)=s x)
    (hdrop : ∀ a,r a≤s (d a)+1) (b : α) (hb : s (d b)=r b) :
    DeletionPerverse s (deletionPush r s d (deletionKLVector r b)) := by
  constructor
  · exact deletionKL_push_polynomial r s d hdrop b hb
  · exact deletionPush_palindromic r s d c hgc hcr (deletionKLVector_perverse r hr b)

variable [LocallyFiniteOrder β]

/-- The genuine deletion intertwiner before extracting its degree-one coefficients. -/
theorem deletionKL_push_expansion (r : α→ℕ) (s : β→ℕ) (d : α→β) (c : β→α)
    (hr : Monotone r) (hs : Monotone s)
    (hgc : ∀ x a,c x≤a↔x≤d a) (hcr : ∀ x,r (c x)=s x)
    (hdrop : ∀ a,r a≤s (d a)+1) (b : α) (hb : s (d b)=r b) (x : β) :
    deletionPush r s d (deletionKLVector r b) x=
      ∑ y,C ((deletionPush r s d (deletionKLVector r b) y).coeff 0)*deletionKLVector s y x :=
  (deletionKL_push_perverse r s d c hr hgc hcr hdrop b hb).kl_expansion hs x

end Dowling
