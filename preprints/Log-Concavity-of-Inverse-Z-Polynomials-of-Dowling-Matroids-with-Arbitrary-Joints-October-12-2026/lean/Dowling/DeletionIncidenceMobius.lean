import Dowling.DeletionIncidencePush

noncomputable section
namespace Dowling
open Finset LaurentPolynomial IncidenceAlgebra
open scoped Classical
variable {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]

 theorem deletion_fiber_upper_sum {R : Type*} [AddCommMonoid R]
    (d : α→β) (c : β→α) (hgc : ∀ b a,c b≤a↔b≤d a) (v : α→R) (b : β) :
    (∑ y∈univ.filter (fun y=>b≤y),∑ a,if d a=y then v a else 0)=
      ∑ a∈univ.filter (fun a=>c b≤a),v a := by
  simp only [sum_filter,ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [sum_eq_single (d a)]
  · simp only [ite_true]
    rw [hgc]
  · intro y hy hya
    by_cases hby : b≤y
    · simp [hby,Ne.symm hya]
    · simp [hby]
  · simp

 theorem deletion_upper_column_unique {R : Type*} [AddCommGroup R]
    (v w : α→R)
    (h : ∀ a,(∑ b∈univ.filter (fun b=>a≤b),v b)=∑ b∈univ.filter (fun b=>a≤b),w b) : v=w := by
  funext a
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    have hs : (∑ b∈univ.filter (fun b=>a≤b),(v b-w b))=v a-w a := by
      rw [sum_eq_single a]
      · intro b hb hba
        rw [ih b (lt_of_le_of_ne (mem_filter.mp hb).2 (Ne.symm hba)),sub_self]
      · simp
    have hz : (∑ b∈univ.filter (fun b=>a≤b),(v b-w b))=0 := by
      rw [sum_sub_distrib,h,sub_self]
    exact sub_eq_zero.mp (hs.symm.trans hz)

variable [LocallyFiniteOrder α] [LocallyFiniteOrder β]

/-- Möbius columns push through the genuine closure/deletion Galois insertion. -/
theorem deletion_mobius_fiber (d : α→β) (c : β→α)
    (hgc : ∀ b a,c b≤a↔b≤d a) (hdc : ∀ b,d (c b)=b)
    (t : α) (u : β) (ht : ∀ a,a≤t) (hu : ∀ b,b≤u) (hct : c u=t) (b : β) :
    (∑ a,if d a=b then mu ℤ a t else 0)=mu ℤ b u := by
  have he := deletion_upper_column_unique
    (fun y=>∑ a,if d a=y then mu ℤ a t else 0) (fun y=>mu ℤ y u) (fun x=>by
      rw [deletion_fiber_upper_sum d c hgc]
      have hα : univ.filter (fun a=>c x≤a)=Icc (c x) t := by ext a; simp [ht]
      have hβ : univ.filter (fun b=>x≤b)=Icc x u := by ext b; simp [hu]
      rw [hα,hβ,sum_Icc_mu_left,sum_Icc_mu_left]
      have heq : c x=t↔x=u := by
        constructor
        · intro h
          have hd := congrArg d (h.trans hct.symm)
          simpa only [hdc] using hd
        · rintro rfl
          exact hct
      rw [heq])
  exact congrFun he b

 theorem deletionPush_mobius (r : α→ℕ) (s : β→ℕ) (d : α→β) (c : β→α)
    (hgc : ∀ b a,c b≤a↔b≤d a) (hdc : ∀ b,d (c b)=b)
    (t : α) (u : β) (ht : ∀ a,a≤t) (hu : ∀ b,b≤u) (hct : c u=t) (b : β) :
    deletionPush r s d (fun a=>T (r a)*C (mu ℤ a t)) b=T (s b)*C (mu ℤ b u) := by
  rw [← deletion_mobius_fiber d c hgc hdc t u ht hu hct b,map_sum,mul_sum]
  unfold deletionPush
  apply sum_congr rfl
  intro a ha
  by_cases hab : d a=b
  · rw [ite_eq_left hab,ite_eq_left hab,← mul_assoc,← T_add]
    congr 2
    ring
  · simp [hab]

end Dowling
