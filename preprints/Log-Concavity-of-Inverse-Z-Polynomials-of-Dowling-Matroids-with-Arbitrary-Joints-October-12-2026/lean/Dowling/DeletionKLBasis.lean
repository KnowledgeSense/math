import Dowling.DeletionIncidenceReflection

noncomputable section
namespace Dowling
open Finset LaurentPolynomial MatroidInverseZ
open scoped Classical
variable {α : Type*} [Fintype α] [PartialOrder α] [LocallyFiniteOrder α]

/-- The actual KL basis vector on a finite ranked interval. -/
def deletionKLVector (r : α→ℕ) (b a : α) : DeletionLaurent :=
  if a≤b then deletionLift ((r b : ℤ)-r a) (kl r b a) else 0

 theorem deletionLift_one (d : ℤ) : deletionLift d 1=T d := by
  simp [deletionLift]

 omit [Fintype α] in
 theorem deletionKLVector_self (r : α→ℕ) (a : α) : deletionKLVector r a a=1 := by
  simp [deletionKLVector,deletionLift_one]

 omit [Fintype α] in
 theorem deletionKLVector_polynomial (r : α→ℕ) (a b : α) :
    ∃ p : Polynomial ℤ,deletionKLVector r b a=p.toLaurent := by
  by_cases hab : a≤b
  · rw [deletionKLVector,ite_eq_left hab]
    by_cases he : a=b
    · subst b
      exact ⟨1,by simp [deletionLift_one]⟩
    apply deletionLift_polynomial
    intro k hk
    have hlt : 2*k<r b-r a := by
      by_contra h
      exact hk (kl_high_coeff r a b he k (by omega))
    omega
  · exact ⟨0,by simp [deletionKLVector,hab]⟩

 omit [Fintype α] in
 theorem deletionKLVector_constantCoeff (r : α→ℕ) (a b : α) :
    (deletionKLVector r b a).coeff 0=if a=b then 1 else 0 := by
  by_cases he : a=b
  · subst b
    rw [deletionKLVector_self,ite_eq_left rfl]
    simp
  rw [ite_eq_right he]
  by_cases hab : a≤b
  · rw [deletionKLVector,ite_eq_left hab]
    apply deletionLift_coeff_zero
    intro k hk
    have hlt : 2*k<r b-r a := by
      by_contra h
      exact hk (kl_high_coeff r a b he k (by omega))
    omega
  · simp [deletionKLVector,hab]

 omit [Fintype α] in
 theorem deletionZ_natDegree_le (r : α→ℕ) (hr : Monotone r) (a b : α) :
    (zKernel r a b).natDegree≤r b-r a := by
  rw [zKernel_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  have hax := hr (mem_Icc.mp hx).1
  have hxb := hr (mem_Icc.mp hx).2
  calc
    _ ≤ (Polynomial.X^(r x-r a) : Polynomial ℤ).natDegree+(kl r b x).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (r x-r a)+(r b-r x) := by rw [Polynomial.natDegree_X_pow]; exact Nat.add_le_add_left (kl_natDegree_le r x b) _
    _ = _ := by omega

 theorem deletionLift_Xpow_mul (d : ℤ) (k : ℕ) (p : Polynomial ℤ) :
    deletionLift d (Polynomial.X^k*p)=T (d-2*k)*deletionSubst p := by
  rw [deletionLift,map_mul,map_pow,deletionSubst_X,T_pow]
  rw [show d-2*(k : ℤ)=d+(k : ℤ)*(-2) by ring,T_add]
  ring

 theorem deletionKLVector_rankSum (r : α→ℕ) (hr : Monotone r) (a b : α) (_hab : a≤b) :
    deletionRankSum r (deletionKLVector r b) a=
      deletionLift ((r b : ℤ)-r a) (zKernel r a b) := by
  have hs : (∑ x ∈ Icc a b,T ((r a : ℤ)-r x)*deletionKLVector r b x)=
      deletionRankSum r (deletionKLVector r b) a := by
    apply sum_subset
    · intro x hx
      exact mem_filter.mpr ⟨mem_univ _,(mem_Icc.mp hx).1⟩
    · intro x hx hnot
      have hxb : ¬x≤b := by
        intro hxb
        exact hnot (mem_Icc.mpr ⟨(mem_filter.mp hx).2,hxb⟩)
      simp [deletionKLVector,hxb]
  rw [← hs,zKernel_apply,deletionLift_finset_sum]
  apply sum_congr rfl
  intro x hx
  rw [deletionKLVector,ite_eq_left (mem_Icc.mp hx).2,deletionLift_Xpow_mul,deletionLift]
  rw [← mul_assoc,← T_add]
  congr 1
  have hax := hr (mem_Icc.mp hx).1
  congr 1
  omega

 theorem deletionKLVector_perverse (r : α→ℕ) (hr : Monotone r) (b : α) :
    DeletionPerverse r (deletionKLVector r b) := by
  constructor
  · intro a
    exact deletionKLVector_polynomial r a b
  · intro a
    by_cases hab : a≤b
    · rw [deletionKLVector_rankSum r hr a b hab]
      have hd : ((r b-r a : ℕ) : ℤ)=(r b : ℤ)-r a := by have := hr hab; omega
      rw [← hd]
      exact deletionLift_palindromic _ _ (deletionZ_natDegree_le r hr a b) (zKernel_reflect r hr a b)
    · have hz : deletionRankSum r (deletionKLVector r b) a=0 := by
        apply sum_eq_zero
        intro x hx
        have hxb : ¬x≤b := fun h=>hab ((mem_filter.mp hx).2.trans h)
        simp [deletionKLVector,hxb]
      rw [hz,map_zero]

end Dowling
