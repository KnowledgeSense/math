import Dowling.DeletionKLBasis

noncomputable section
namespace Dowling
open Finset LaurentPolynomial MatroidInverseZ
open scoped Classical
variable {α : Type*} [Fintype α] [PartialOrder α]

theorem DeletionPerverse.zero (r : α→ℕ) : DeletionPerverse r (fun _=>0) := by
  constructor
  · exact fun _=>⟨0,by simp⟩
  · simp [deletionRankSum]

theorem DeletionPerverse.add {r : α→ℕ} {v w : α→DeletionLaurent}
    (hv : DeletionPerverse r v) (hw : DeletionPerverse r w) :
    DeletionPerverse r (fun a=>v a+w a) := by
  constructor
  · intro a
    obtain ⟨p,hp⟩ := hv.polynomial a
    obtain ⟨q,hq⟩ := hw.polynomial a
    exact ⟨p+q,by rw [map_add,← hp,← hq]⟩
  · intro a
    simp only [deletionRankSum,mul_add,sum_add_distrib,map_add]
    exact congrArg₂ (·+·) (hv.palindromic a) (hw.palindromic a)

theorem DeletionPerverse.C_mul {r : α→ℕ} {v : α→DeletionLaurent}
    (hv : DeletionPerverse r v) (c : ℤ) : DeletionPerverse r (fun a=>C c*v a) := by
  constructor
  · intro a
    obtain ⟨p,hp⟩ := hv.polynomial a
    exact ⟨Polynomial.C c*p,by rw [map_mul,Polynomial.toLaurent_C,← hp]⟩
  · intro a
    have hs : deletionRankSum r (fun b=>C c*v b) a=C c*deletionRankSum r v a := by
      simp only [deletionRankSum,mul_sum]
      apply sum_congr rfl
      intro b hb
      ring
    rw [hs,map_mul,invert_C,hv.palindromic]

theorem DeletionPerverse.sum {ι : Type*} (s : Finset ι) {r : α→ℕ}
    (v : ι→α→DeletionLaurent) (hv : ∀ i∈s,DeletionPerverse r (v i)) :
    DeletionPerverse r (fun a=>∑ i∈s,v i a) := by
  induction s using Finset.induction_on with
  | empty => simpa using DeletionPerverse.zero r
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (hv i (mem_insert_self _ _)).add (ih (fun j hj=>hv j (mem_insert_of_mem hj)))

variable [LocallyFiniteOrder α]

/-- The corrected KL basis expansion is proved only for polynomial-supported perverse vectors. -/
theorem DeletionPerverse.kl_expansion {r : α→ℕ} (hr : Monotone r)
    {v : α→DeletionLaurent} (hv : DeletionPerverse r v) (a : α) :
    v a=∑ b,C ((v b).coeff 0)*deletionKLVector r b a := by
  have hw : DeletionPerverse r (fun a=>∑ b,C ((v b).coeff 0)*deletionKLVector r b a) :=
    DeletionPerverse.sum univ _ (fun b _=>(deletionKLVector_perverse r hr b).C_mul _)
  have he := hv.ext hw (fun c=>by
    simp only [AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
    simp only [show ∀ b,(C ((v b).coeff 0)*deletionKLVector r b c).coeff 0=
      (v b).coeff 0*(deletionKLVector r b c).coeff 0 from fun b=>by
        rw [← smul_eq_C_mul,AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply]; rfl,
      deletionKLVector_constantCoeff]
    simp)
  exact congrFun he a

end Dowling
