import Dowling.GainCirclesPolygons

noncomputable section
namespace Dowling
variable {G : Type*} [Group G] {n : ℕ}

/-- The label of a traversal of one canonical link. -/
def Link.Traverses (e : Link G n) (i j : Fin n) (g : G) : Prop :=
  (e.tail = i ∧ e.head = j ∧ e.gain = g) ∨
  (e.head = i ∧ e.tail = j ∧ e.gain⁻¹ = g)

/-- Opposite traversals are an inverse pair exactly when they use the same
canonical link. Thus the length-two polygon predicate retains precisely the
cycles with two distinct parallel edges. -/
theorem Link.inverse_traversals_iff_eq {e f : Link G n} {i j : Fin n} {g h : G}
    (he : e.Traverses i j g) (hf : f.Traverses j i h) : h = g⁻¹ ↔ e = f := by
  rcases he with he | he <;> rcases hf with hf | hf
  · have heo := e.ordered
    have hfo := f.ordered
    rw [he.1, he.2.1] at heo
    rw [hf.1, hf.2.1] at hfo
    exact False.elim ((not_lt_of_ge (le_of_lt heo)) hfo)
  · rcases he with ⟨hei,hej,heg⟩
    rcases hf with ⟨hfj,hfi,hfg⟩
    constructor
    · intro h
      have hgain : e.gain = f.gain := by
        apply inv_injective
        rw [heg,hfg,h]
      cases e
      cases f
      simp_all
    · intro h
      subst f
      rw [← hfg,heg]
  · rcases he with ⟨hei,hej,heg⟩
    rcases hf with ⟨hfj,hfi,hfg⟩
    constructor
    · intro h
      have hgain : e.gain = f.gain := by rw [hfg,h,← heg,inv_inv]
      cases e
      cases f
      simp_all
    · intro h
      subst f
      rw [← heg,inv_inv,← hfg]
  · have heo := e.ordered
    have hfo := f.ordered
    rw [he.2.1, he.1] at heo
    rw [hf.2.1, hf.1] at hfo
    exact False.elim ((not_lt_of_ge (le_of_lt heo)) hfo)

end Dowling
