import MainTheorems.Tuza.SteinerRestriction
import MainTheorems.Tuza.PerfectFactors

namespace ResearchMain.Tuza
namespace SteinerOperation

variable {V : Type*} [Fintype V] [DecidableEq V] (S : SteinerOperation V)

def Closed (R : Set V) : Prop := ∀ x ∈ R, ∀ y ∈ R, S.third x y ∈ R

omit [Fintype V] [DecidableEq V] in
theorem closed_singleton (v : V) : S.Closed {v} := by
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy ⊢
  subst x
  subst y
  exact S.idempotent v

omit [Fintype V] in
theorem closed_block (a b : V) : S.Closed (S.block a b : Set V) := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simpa [S.idempotent] using hx
  · have he := S.block_eq_of_pair hx hy hxy
    rw [← he]
    simp [block]

def deletedGraph (R : Set V) (i : R) : SimpleGraph {x : V // x ∉ R} where
  Adj x y := x ≠ y ∧ S.third x.val y.val = i.val
  symm := ⟨by intro x y h; exact ⟨h.1.symm, (S.comm _ _).trans h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def deletedFactors (R : Set V) (hR : S.Closed R) : PerfectFactors {x : V // x ∉ R} R where
  graph := S.deletedGraph R
  matching := by
    intro i x y z hy hz
    have hey : y.val = S.third x.val i.val := by
      rw [← hy.2, S.involutive]
    have hez : z.val = S.third x.val i.val := by
      rw [← hz.2, S.involutive]
    exact Subtype.ext (hey.trans hez.symm)
  separated := by
    intro i j x y hi hj
    exact Subtype.ext (hi.2.symm.trans hj.2)
  perfect := by
    intro i x
    have hxi : x.val ≠ i.val := by
      intro he
      exact x.property (he.symm ▸ i.property)
    have hkeep : S.third x.val i.val ∉ R := by
      intro hz
      have hr := hR i.val i.property (S.third x.val i.val) hz
      rw [S.comm x.val i.val, S.involutive] at hr
      exact x.property hr
    refine ⟨⟨S.third x.val i.val, hkeep⟩, ?_, S.involutive x.val i.val⟩
    intro he
    exact S.third_ne_left hxi (congrArg Subtype.val he).symm

omit [Fintype V] [DecidableEq V] in
theorem restrictedGraph_eq_factor_complement (R : Set V) (hR : S.Closed R) :
    S.restrictedGraph (· ∉ R) = ⊤ \ (S.deletedFactors R hR).unionGraph := by
  ext x y
  change (x ≠ y ∧ S.third x.val y.val ∉ R) ↔
    x ≠ y ∧ ¬∃ i : R, x ≠ y ∧ S.third x.val y.val = i.val
  constructor
  · rintro ⟨hxy, hkeep⟩
    refine ⟨hxy, ?_⟩
    rintro ⟨i, _, hi⟩
    exact hkeep (hi.symm ▸ i.property)
  · rintro ⟨hxy, hnot⟩
    refine ⟨hxy, ?_⟩
    intro hi
    exact hnot ⟨⟨S.third x.val y.val, hi⟩, hxy, rfl⟩

theorem exists_deleted_factor_decomposition (R : Set V) (hR : S.Closed R) :
    Nonempty (FactorDecomposition {x : V // x ∉ R} R) := by
  obtain ⟨D⟩ := S.exists_restricted_decomposition (· ∉ R)
  rw [S.restrictedGraph_eq_factor_complement R hR] at D
  exact ⟨⟨S.deletedFactors R hR, D⟩⟩

end SteinerOperation
end ResearchMain.Tuza
