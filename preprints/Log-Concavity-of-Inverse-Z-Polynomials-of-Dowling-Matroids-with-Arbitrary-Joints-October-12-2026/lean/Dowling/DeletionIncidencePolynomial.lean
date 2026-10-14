import Dowling.DeletionIncidenceNormalization

noncomputable section
namespace Dowling
open Finset LaurentPolynomial MatroidInverseZ
open scoped Classical
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]

 theorem deletionTau_rank_even (r : α→ℕ) (hr : Monotone r) (e b : α)
    (he : r e=1) (hτ : deletionTau r e b≠0) : r b%2=0 := by
  have h : e≤b ∧ (r b-r e)%2=1 := by
    by_contra hn
    exact hτ (by simp [deletionTau,hn])
  have := hr h.1
  rw [he] at *
  omega

 theorem deletionYCoordinate_tau (r : α→ℕ) (hr : Monotone r) (t e b : α)
    (hbt : b≤t) (he : r e=1) :
    C (deletionTau r e b)*deletionYCoordinate r t b=
      deletionLift (2*(r t : ℤ)) (Polynomial.C ((-1 : ℤ)^r t)*
        (Polynomial.C (deletionTau r e b)*Polynomial.X^(r b/2)*inverseZ r b t)) := by
  by_cases hτ : deletionTau r e b=0
  · simp [hτ,deletionLift]
  · rw [deletionYCoordinate_even r hr t b hbt (deletionTau_rank_even r hr e b he hτ)]
    simp only [deletionLift,map_mul,deletionSubst_C]
    ring

variable {β : Type*} [Fintype α] [Fintype β] [PartialOrder β] [LocallyFiniteOrder β]

omit [Fintype β] in
/-- Clearing the proved Laurent rank normalization recovers an ordinary polynomial deletion formula. -/
theorem deletion_inverseZ_of_coordinate_relation (r : α→ℕ) (s : β→ℕ)
    (hr : Monotone r) (hs : Monotone s) (d : α→β)
    (t a e : α) (u x : β) (ht : ∀ b,b≤t) (hxu : x≤u)
    (ha : r a=0) (he : r e=1) (hx : s x=0) (hu : s u=r t)
    (h : deletionYCoordinate s u x=deletionYCoordinate r t a+
      (T 1+T (-1))*deletionYCoordinate r t e+
      ∑ b,if s (d b)=r b then C (deletionTau r e b)*deletionYCoordinate r t b else 0) :
    inverseZ r a t=inverseZ s x u+(1+Polynomial.X)*inverseZ r e t-
      ∑ b,if s (d b)=r b then
        Polynomial.C (deletionTau r e b)*Polynomial.X^(r b/2)*inverseZ r b t else 0 := by
  let S : Polynomial ℤ := ∑ b,if s (d b)=r b then
    Polynomial.C (deletionTau r e b)*Polynomial.X^(r b/2)*inverseZ r b t else 0
  have hsum : (∑ b,if s (d b)=r b then C (deletionTau r e b)*deletionYCoordinate r t b else 0)=
      deletionLift (2*(r t : ℤ)) (Polynomial.C ((-1 : ℤ)^r t)*S) := by
    dsimp only [S]
    rw [mul_sum,deletionLift_finset_sum]
    apply sum_congr rfl
    intro b hb
    by_cases hp : s (d b)=r b
    · rw [ite_eq_left hp,ite_eq_left hp]
      exact deletionYCoordinate_tau r hr t e b (ht b) he
    · simp [hp,deletionLift]
  rw [deletionYCoordinate_bottom s hs u x hxu hx,
    deletionYCoordinate_bottom r hr t a (ht a) ha,
    deletionYCoordinate_atom r hr t e (ht e) he,hu,hsum] at h
  have hp : Polynomial.C ((-1 : ℤ)^r t)*inverseZ s x u=
      Polynomial.C ((-1 : ℤ)^r t)*
        (inverseZ r a t-(1+Polynomial.X)*inverseZ r e t+S) := by
    apply deletionLift_injective (2*(r t : ℤ))
    rw [h]
    simp only [deletionLift,map_add,map_sub,mul_add,mul_sub]
    ring
  have hc : Polynomial.C ((-1 : ℤ)^r t)≠(0 : Polynomial ℤ) := by simp
  have heq := mul_left_cancel₀ hc hp
  change inverseZ r a t=inverseZ s x u+(1+Polynomial.X)*inverseZ r e t-S
  rw [heq]
  ring

end Dowling
