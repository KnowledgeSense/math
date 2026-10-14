import SumsetRanges.CarryLength

open Finset
namespace SumsetRanges

/-- Every amount up to the total capacity can be allocated among the actual finite coordinates. -/
theorem bounded_allocation (r : ℕ) (d : Fin r→ℕ) (t : ℕ) (ht : t≤∑i,d i) :
    ∃a : Fin r→ℕ,(∀i,a i≤d i) ∧ ∑i,a i=t := by
  induction r generalizing t with
  | zero =>
      have ht0 : t=0 := by simpa using ht
      exact ⟨Fin.elim0,fun i => Fin.elim0 i,by simp [ht0]⟩
  | succ r ih =>
      let a0 := min t (d 0)
      have htail : t-a0≤∑i : Fin r,d i.succ := by
        rw [Fin.sum_univ_succ] at ht
        dsimp [a0]
        omega
      obtain ⟨a,ha,he⟩ := ih (fun i => d i.succ) (t-a0) htail
      refine ⟨Fin.cons a0 a,?_,?_⟩
      · intro i
        refine Fin.cases (by simp [a0]) (fun j => ?_) i
        exact ha j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ]
        rw [he]
        dsimp [a0]
        omega

end SumsetRanges
