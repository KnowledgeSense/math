import Paving.UpperMobius

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α] {M : Matroid α}

theorem choose_pascal_sub (h f d : ℕ) (hfd : f≤d) (hdh : d+1≤h) :
    ((h-f-1).choose (d-f):ℤ) + ((h-f-1).choose (d-f+1):ℤ) =
      ((h-f).choose (d-f+1):ℤ) := by
  have he := Nat.choose_succ_succ (h-f-1) (d-f)
  simp only [Nat.succ_eq_add_one] at he
  rw [show h-f-1+1=h-f by omega] at he
  exact_mod_cast he.symm

/-- Pascal's identity applied to the exact pointed hyperplane partition. -/
theorem IsPaving.pointed_pascal_payment (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (F : MatroidInverseZ.Flat M) (hF : F.1.ncard≤d) :
    (∑ H ∈ (hyperplanes M).filter (fun H => F.1 ⊆ H),
      ((H.ncard-F.1.ncard-1).choose (d-F.1.ncard):ℤ)) -
        ((M.E.ncard-F.1.ncard-1).choose (d-F.1.ncard):ℤ) =
      ((M.E.ncard-F.1.ncard-1).choose (d-F.1.ncard+1):ℤ) -
        ∑ H ∈ (hyperplanes M).filter (fun H => F.1 ⊆ H),
          ((H.ncard-F.1.ncard-1).choose (d-F.1.ncard+1):ℤ) := by
  have hp := hM.pointed_hyperplane_packing (by omega) F.1 F.2.subset_ground (by omega)
  rw [← sum_filter] at hp
  have hindex : rank M-1-F.1.ncard=d-F.1.ncard+1 := by omega
  rw [hindex] at hp
  have hz : (∑ H ∈ (hyperplanes M).filter (fun H => F.1 ⊆ H),
      ((H.ncard-F.1.ncard).choose (d-F.1.ncard+1):ℤ)) =
      ((M.E.ncard-F.1.ncard).choose (d-F.1.ncard+1):ℤ) := by exact_mod_cast hp
  have hs : (∑ H ∈ (hyperplanes M).filter (fun H => F.1 ⊆ H),
      (((H.ncard-F.1.ncard-1).choose (d-F.1.ncard):ℤ) +
        ((H.ncard-F.1.ncard-1).choose (d-F.1.ncard+1):ℤ))) =
      ((M.E.ncard-F.1.ncard-1).choose (d-F.1.ncard):ℤ) +
        ((M.E.ncard-F.1.ncard-1).choose (d-F.1.ncard+1):ℤ) := by
    rw [choose_pascal_sub M.E.ncard F.1.ncard d hF (by have := rank_le_ground_card M; omega)]
    rw [← hz]
    apply sum_congr rfl
    intro H hH
    have hc := hyperplane_card_lower ((mem_hyperplanes M H).mp (mem_filter.mp hH).1)
    exact choose_pascal_sub H.ncard F.1.ncard d hF (by omega)
  rw [sum_add_distrib] at hs
  omega

/-- The actual paving upper Möbius formula, with all hyperplanes still explicit. -/
theorem IsPaving.upper_mu_subtraction (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (F : MatroidInverseZ.Flat M) (hF : F.1.ncard≤d) :
    IncidenceAlgebra.mu ℤ F ⊤ =
      (-1 : ℤ)^(d+2-F.1.ncard) *
        (((M.E.ncard-F.1.ncard-1).choose (d-F.1.ncard+1):ℤ) -
          ∑ H ∈ (hyperplanes M).filter (fun H => F.1 ⊆ H),
            ((H.ncard-F.1.ncard-1).choose (d-F.1.ncard+1):ℤ)) := by
  rw [hM.upper_mu_recurrence d hr F hF, hM.pointed_pascal_payment d hr F hF]

end Paving
