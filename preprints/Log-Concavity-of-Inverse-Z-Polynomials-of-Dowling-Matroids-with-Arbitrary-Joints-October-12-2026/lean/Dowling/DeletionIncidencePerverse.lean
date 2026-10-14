import Dowling.DeletionIncidenceLaurent

noncomputable section
namespace Dowling
open Finset LaurentPolynomial
variable {α : Type*} [Fintype α] [PartialOrder α]
open scoped Classical

/-- The exact weighted upper sum in the corrected perverse condition. -/
def deletionRankSum (r : α→ℕ) (v : α→DeletionLaurent) (a : α) : DeletionLaurent :=
  ∑ b ∈ univ.filter (fun b=>a≤b),T ((r a : ℤ)-r b)*v b

/-- Polynomial support is essential in addition to the involutive rank sums. -/
structure DeletionPerverse (r : α→ℕ) (v : α→DeletionLaurent) : Prop where
  polynomial : ∀ a,∃ p : Polynomial ℤ,v a=p.toLaurent
  palindromic : ∀ a,invert (deletionRankSum r v a)=deletionRankSum r v a

 theorem deletionRankSum_sub (r : α→ℕ) (v w : α→DeletionLaurent) (a : α) :
    deletionRankSum r (fun b=>v b-w b) a=deletionRankSum r v a-deletionRankSum r w a := by
  simp only [deletionRankSum,mul_sub,sum_sub_distrib]

 theorem DeletionPerverse.sub {r : α→ℕ} {v w : α→DeletionLaurent}
    (hv : DeletionPerverse r v) (hw : DeletionPerverse r w) :
    DeletionPerverse r (fun a=>v a-w a) := by
  constructor
  · intro a
    obtain ⟨p,hp⟩ := hv.polynomial a
    obtain ⟨q,hq⟩ := hw.polynomial a
    exact ⟨p-q,by rw [map_sub,← hp,← hq]⟩
  · intro a
    rw [deletionRankSum_sub,map_sub,hv.palindromic,hw.palindromic]

/-- A perverse polynomial vector is determined by its literal constant coefficients. -/
theorem DeletionPerverse.eq_zero {r : α→ℕ} {v : α→DeletionLaurent}
    (hv : DeletionPerverse r v) (hc : ∀ a,(v a).coeff 0=0) : ∀ a,v a=0 := by
  intro a
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    have hs : deletionRankSum r v a=v a := by
      rw [deletionRankSum,sum_eq_single a]
      · simp
      · intro b hb hba
        have hab : a<b := lt_of_le_of_ne (mem_filter.mp hb).2 (Ne.symm hba)
        rw [ih b hab,mul_zero]
      · simp
    obtain ⟨p,hp⟩ := hv.polynomial a
    have hinv := hv.palindromic a
    rw [hs,hp] at hinv
    have hconst := deletionPolynomial_invert_constant p hinv
    have hp0 : p.coeff 0=0 := by
      have h := hc a
      rw [hp] at h
      change p.toLaurent.coeff (0 : ℕ)=0 at h
      rw [deletionPolynomial_coeff_nat] at h
      exact h
    rw [hp,hconst,hp0,map_zero,map_zero]

 theorem DeletionPerverse.ext {r : α→ℕ} {v w : α→DeletionLaurent}
    (hv : DeletionPerverse r v) (hw : DeletionPerverse r w)
    (hc : ∀ a,(v a).coeff 0=(w a).coeff 0) : v=w := by
  funext a
  apply sub_eq_zero.mp
  exact (hv.sub hw).eq_zero (by intro b; simp only [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,hc,sub_self]) a

end Dowling
