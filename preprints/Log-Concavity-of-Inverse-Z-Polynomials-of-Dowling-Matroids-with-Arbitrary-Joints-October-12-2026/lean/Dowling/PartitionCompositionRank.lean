import Dowling.PartitionUpperEquiv

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

def composeSolutionEquiv (p : GainPartition G n) (q : GainPartition G p.roots.card) :
    (p.compose q).solutionSet ≃ q.solutionSet where
  toFun x := ⟨fun i => x.val (p.rootVertex i),p.compose_solution_restrict q x.val x.property⟩
  invFun a := ⟨(p.coordinateEquiv.symm a.val).val, by
    apply (p.mem_compose_solutionSet q _).mpr
    refine ⟨(p.coordinateEquiv.symm a.val).property,?_⟩
    simpa only [coordinateEquiv_symm_root] using a.property⟩
  left_inv x := by
    apply Subtype.ext
    have hp := p.compose_solution_subset q x.property
    have he : p.coordinateEquiv.symm (p.coordinateEquiv ⟨x.val,hp⟩) = ⟨x.val,hp⟩ :=
      p.coordinateEquiv.symm_apply_apply _
    exact congrArg (fun y : p.solutionSet => y.val) he
  right_inv a := by
    apply Subtype.ext
    funext i
    exact p.coordinateEquiv_symm_root a.val i

theorem compose_roots_card [Finite G] (p : GainPartition G n)
    (q : GainPartition G p.roots.card) : (p.compose q).roots.card = q.roots.card := by
  have hc := Nat.card_congr (p.composeSolutionEquiv q)
  rw [solution_card_roots,solution_card_roots] at hc
  have hb : 1 < Nat.card G + 1 := by have := Finite.card_pos (α := G); omega
  exact le_antisymm ((pow_le_pow_iff_right₀ hb).mp hc.le)
    ((pow_le_pow_iff_right₀ hb).mp hc.ge)

theorem compose_rank_difference [Finite G] (p : GainPartition G n)
    (q r : GainPartition G p.roots.card) :
    (n-(p.compose r).roots.card)-(n-(p.compose q).roots.card) =
      (p.roots.card-r.roots.card)-(p.roots.card-q.roots.card) := by
  rw [compose_roots_card,compose_roots_card]
  have hp := p.roots_card_le
  have hq := q.roots_card_le
  have hr := r.roots_card_le
  omega

end Dowling.GainPartition
