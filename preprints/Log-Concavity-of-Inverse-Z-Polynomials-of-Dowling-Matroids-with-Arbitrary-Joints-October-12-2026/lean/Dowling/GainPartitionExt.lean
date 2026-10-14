import Dowling.GainPartitionEquations

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem code_right_of_relation (p : GainPartition G n) (i j r : Fin n) (a g : G)
    (hi : p.code i = some (r,a))
    (h : ∀ x ∈ p.solutionSet, x j = gainAct G (x i) g) : p.code j = some (r,a*g) := by
  rcases (p.solution_link_iff i j g).mp h with ⟨hz,_⟩ | ⟨u,b,c,hb,hc,he⟩
  · rw [hi] at hz
    cases hz
  · have hp : (u,b) = (r,a) := Option.some.inj (hb.symm.trans hi)
    rcases Prod.mk.inj hp with ⟨rfl,rfl⟩
    simpa only [he] using hc

theorem code_left_of_relation (p : GainPartition G n) (i j r : Fin n) (b g : G)
    (hj : p.code j = some (r,b))
    (h : ∀ x ∈ p.solutionSet, x j = gainAct G (x i) g) : p.code i = some (r,b*g⁻¹) := by
  exact p.code_right_of_relation j i r b g⁻¹ hj
    (fun x hx => (gainAct_reverse _ _ _).mp (h x hx))

/-- The least-root normalization removes all potential-label and partition ambiguity. -/
theorem solutionSet_injective : Function.Injective (solutionSet (G := G) (n := n)) := by
  intro p q hpq
  have hcode : p.code = q.code := by
    funext i
    cases hi : p.code i with
    | none =>
      have hq : q.code i = none := (q.solution_zero_iff i).mp (by
        rw [← hpq]
        exact (p.solution_zero_iff i).mpr hi)
      exact hq.symm
    | some v =>
      rcases v with ⟨r,a⟩
      have hr : p.code r = some (r,1) := p.rooted i r a hi
      have rel : ∀ x ∈ q.solutionSet, x i = gainAct G (x r) a := by
        intro x hx
        rw [← hpq] at hx
        exact ((p.mem_solutionSet x).mp hx).2 i r a hi
      cases hqr : q.code r with
      | none =>
        have hz : p.code r = none := (p.solution_zero_iff r).mp (by
          rw [hpq]
          exact (q.solution_zero_iff r).mpr hqr)
        rw [hr] at hz
        cases hz
      | some v =>
        rcases v with ⟨s,b⟩
        have hqi := q.code_right_of_relation r i s b a hqr rel
        have rel' : ∀ x ∈ p.solutionSet, x r = gainAct G (x s) b := by
          intro x hx
          rw [hpq] at hx
          exact ((q.mem_solutionSet x).mp hx).2 r s b hqr
        have hps := p.code_left_of_relation s r r 1 b hr rel'
        have hrs : r = s := le_antisymm (p.least s r (1*b⁻¹) hps) (q.least r s b hqr)
        subst s
        have hqb := q.rooted r r b hqr
        have hb : b = 1 := congrArg Prod.snd (Option.some.inj (hqr.symm.trans hqb))
        simpa [hb] using hqi.symm
  cases p
  cases q
  cases hcode
  rfl

end Dowling.GainPartition
