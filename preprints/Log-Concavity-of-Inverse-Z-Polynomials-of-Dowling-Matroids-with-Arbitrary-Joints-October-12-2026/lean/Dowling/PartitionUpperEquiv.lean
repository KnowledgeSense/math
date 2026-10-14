import Dowling.PartitionCompression

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem code_injective : Function.Injective (code (G := G) (n := n)) := by
  intro p q h
  cases p
  cases q
  cases h
  rfl

theorem compose_compress (p q : GainPartition G n) (hpq : p ≤ q) :
    p.compose (p.compress q hpq) = q := by
  have hcode : (p.compose (p.compress q hpq)).code = q.code := by
    funext i
    cases hi : p.code i with
    | none =>
      exact (p.compositeCode_none _ i hi).trans (code_none_of_le hpq i hi).symm
    | some v =>
      rcases v with ⟨r,a⟩
      let k := p.rootOrderIso.symm ⟨r,p.rooted i r a hi⟩
      have hkr : p.rootVertex k = r := congrArg Subtype.val (p.rootOrderIso.apply_symm_apply _)
      have hrel : ∀ x ∈ q.solutionSet, x i = gainAct G (x r) a :=
        fun x hx => ((p.mem_solutionSet x).mp (hpq hx)).2 i r a hi
      change p.compositeCode (p.compress q hpq) i = q.code i
      rw [p.compositeCode_some _ i r a hi]
      change ((p.compress q hpq).code k).map _ = q.code i
      cases hr : q.code r with
      | none =>
        have hk : q.code (p.rootVertex k) = none := hkr ▸ hr
        have hqi : q.code i = none := (q.solution_zero_iff i).mp (by
          intro x hx
          rw [hrel x hx,(q.solution_zero_iff r).mpr hr x hx,gainAct_none])
        change (compressedCode p q hpq k).map _ = _
        rw [compressedCode_none p q hpq k hk,hqi]
        rfl
      | some v =>
        rcases v with ⟨s,b⟩
        have hk : q.code (p.rootVertex k) = some (s,b) := hkr ▸ hr
        have hqi := q.code_right_of_relation r i s b a hr hrel
        change (compressedCode p q hpq k).map _ = _
        rw [compressedCode_some p q hpq k s b hk,hqi]
        simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
        exact ⟨congrArg Subtype.val (p.rootOrderIso.apply_symm_apply _),trivial⟩
  exact code_injective hcode

theorem compose_le_compose_iff (p : GainPartition G n)
    (q r : GainPartition G p.roots.card) : p.compose q ≤ p.compose r ↔ q ≤ r := by
  constructor
  · intro h a ha
    let x := p.coordinateEquiv.symm a
    have hx : x.val ∈ (p.compose r).solutionSet := by
      apply (p.mem_compose_solutionSet r x.val).mpr
      refine ⟨x.property,?_⟩
      simpa only [x,coordinateEquiv_symm_root] using ha
    have hq := p.compose_solution_restrict q x.val (h hx)
    simpa only [x,coordinateEquiv_symm_root] using hq
  · intro h x hx
    obtain ⟨hp,hr⟩ := (p.mem_compose_solutionSet r x).mp hx
    exact (p.mem_compose_solutionSet q x).mpr ⟨hp,h hr⟩

/-- The entire upper interval of a full group partition is another full group
partition lattice, on its actual free components. -/
def upperOrderIso (p : GainPartition G n) :
    GainPartition G p.roots.card ≃o Set.Ici p where
  toFun q := ⟨p.compose q,p.compose_solution_subset q⟩
  invFun q := p.compress q.val q.property
  left_inv q := by
    change p.compress (p.compose q) (p.compose_solution_subset q) = q
    apply le_antisymm
    · apply (p.compose_le_compose_iff _ _).mp
      rw [compose_compress]
    · apply (p.compose_le_compose_iff _ _).mp
      rw [compose_compress]
  right_inv q := Subtype.ext (p.compose_compress q.val q.property)
  map_rel_iff' := p.compose_le_compose_iff _ _

end Dowling.GainPartition
