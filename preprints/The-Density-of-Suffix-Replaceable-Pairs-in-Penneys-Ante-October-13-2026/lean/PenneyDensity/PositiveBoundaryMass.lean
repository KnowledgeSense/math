import PenneyDensity.BoundaryNoOverlap
import PenneyDensity.ExceptionalBounds

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 theorem geometric_positive_tail_bound (L K : ℕ) (hL : 0<L) :
    (∑ k : Fin (K+1),if 2*L≤k.val then (1/2 : ℝ)^k.val else 0)≤2*(1/2 : ℝ)^(2*L) := by
  have he : (fun k : Fin (K+1) => if 2*L≤k.val then (1/2 : ℝ)^k.val else 0)=
      (fun k : Fin (K+1) => if 2*L-1<k.val then (1/2 : ℝ)^k.val else 0) := by
    funext k
    have hh : 2*L≤k.val ↔ 2*L-1<k.val := by omega
    simp only [hh]
  rw [he]
  have hp : (1/2 : ℝ)^(2*L)=(1/2 : ℝ)^(2*L-1)*(1/2) := by
    rw [← pow_succ]
    congr 1
    omega
  have hb := geometric_tail_bound (2*L-1) (K+1)
  rw [hp]
  linarith

 theorem boundary_probability_lower_bound {K L : ℕ} (hL : 0<L) (hLK : L≤K) :
    (1/2 : ℝ)^(4*L)*(1-8*(1/2 : ℝ)^(2*L))≤boundaryProbability K := by
  let P : Bool × Bool × Fin (K+1) → (Bool × Fin (2*K) → Bool) → Prop :=
    fun p g => 0<p.2.2.val ∧
      properOverlap (boundaryWords g p.1) (boundaryWords g p.2.1) p.2.2.val ∧
      BoundaryCylinder L hLK g
  have hp (p : Bool × Bool × Fin (K+1)) :
      probability (P p)≤(1/2 : ℝ)^(4*L)*
        (if 2*L≤p.2.2.val then (1/2 : ℝ)^p.2.2.val else 0) := by
    by_cases hkL : 2*L≤p.2.2.val
    · rw [ite_eq_left hkL]
      exact (probability_mono (fun _ hx => hx.2)).trans_eq
        (probability_cylinder_overlap hL hkL (by omega) p.1 p.2.1)
    · rw [ite_eq_right hkL,mul_zero]
      have he : P p=(fun _ => False) := by
        funext g
        apply propext
        constructor
        · rintro ⟨hk0,ho,hC⟩
          exact cylinder_forbids_short_overlap hL hLK hk0 (by omega) (by omega) p.1 p.2.1 g hC ho
        · exact False.elim
      rw [he,probability_false]
  have hbad : probability (fun g => ∃ p,P p g)≤
      8*(1/2 : ℝ)^(4*L)*(1/2 : ℝ)^(2*L) := by
    calc
      _ ≤ ∑ p,probability (P p) := probability_exists_le P
      _ ≤ ∑ p : Bool × Bool × Fin (K+1),(1/2 : ℝ)^(4*L)*
          (if 2*L≤p.2.2.val then (1/2 : ℝ)^p.2.2.val else 0) :=
        Finset.sum_le_sum fun p _ => hp p
      _ = 4*(1/2 : ℝ)^(4*L)*
          ∑ k : Fin (K+1),if 2*L≤k.val then (1/2 : ℝ)^k.val else 0 := by
        simp only [Fintype.sum_prod_type,Fintype.sum_bool,← Finset.mul_sum]
        ring
      _ ≤ 4*(1/2 : ℝ)^(4*L)*(2*(1/2 : ℝ)^(2*L)) :=
        mul_le_mul_of_nonneg_left (geometric_positive_tail_bound L K hL) (by positivity)
      _ = _ := by ring
  have hcover : probability (fun g : Bool × Fin (2*K) → Bool => BoundaryCylinder L hLK g)≤
      boundaryProbability K+probability (fun g => ∃ p,P p g) := by
    refine (probability_mono (Q := fun g => SmallOverlapAgreement (boundaryWords g) K ∨ ∃ p,P p g)
      ?_).trans (probability_or_le _ _)
    intro g hC
    by_cases hb : ∃ p,P p g
    · exact Or.inr hb
    · left
      intro b k hk0 hkK
      constructor
      · intro ho
        exact False.elim (hb ⟨(b,false,⟨k,by omega⟩),hk0,ho,hC⟩)
      · intro ho
        exact False.elim (hb ⟨(b,true,⟨k,by omega⟩),hk0,ho,hC⟩)
  rw [probability_cylinder K L hLK] at hcover
  nlinarith

end PenneyDensity
