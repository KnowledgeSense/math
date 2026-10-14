import Dowling.PartitionComposition

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem compose_code_root (p : GainPartition G n) (q : GainPartition G p.roots.card)
    (i : Fin p.roots.card) :
    (p.compose q).code (p.rootVertex i) = (q.code i).map (fun v => (p.rootVertex v.1,v.2)) :=
  p.compositeCode_rootVertex q i

theorem compose_solution_restrict (p : GainPartition G n) (q : GainPartition G p.roots.card)
    (x : Fin n → Option G) (hx : x ∈ (p.compose q).solutionSet) :
    (fun i => x (p.rootVertex i)) ∈ q.solutionSet := by
  apply (q.mem_solutionSet _).mpr
  have h := ((p.compose q).mem_solutionSet x).mp hx
  constructor
  · intro i hi
    apply h.1
    rw [compose_code_root,hi]
    rfl
  · intro i j g hi
    apply h.2
    rw [compose_code_root,hi]
    rfl

theorem compose_solution_subset (p : GainPartition G n) (q : GainPartition G p.roots.card) :
    (p.compose q).solutionSet ⊆ p.solutionSet := by
  intro x hx
  have hc := ((p.compose q).mem_solutionSet x).mp hx
  have hq := (q.mem_solutionSet _).mp (p.compose_solution_restrict q x hx)
  apply (p.mem_solutionSet x).mpr
  constructor
  · intro i hi
    exact hc.1 i (p.compositeCode_none q i hi)
  · intro i r a hi
    let k := p.rootOrderIso.symm ⟨r,p.rooted i r a hi⟩
    have hkr : p.rootVertex k = r := congrArg Subtype.val (p.rootOrderIso.apply_symm_apply _)
    cases hk : q.code k with
    | none =>
      have hz : (p.compose q).code i = none := by
        change p.compositeCode q i = none
        rw [p.compositeCode_some q i r a hi]
        change (q.code k).map _ = none
        rw [hk]; rfl
      rw [hc.1 i hz, ← hkr, hq.1 k hk, gainAct_none]
    | some v =>
      rcases v with ⟨s,b⟩
      have hs : (p.compose q).code i = some (p.rootVertex s,b*a) := by
        change p.compositeCode q i = _
        rw [p.compositeCode_some q i r a hi]
        change (q.code k).map _ = _
        rw [hk]; rfl
      rw [hc.2 i _ _ hs, ← hkr, hq.2 k s b hk, gainAct_mul]

theorem mem_compose_solutionSet (p : GainPartition G n) (q : GainPartition G p.roots.card)
    (x : Fin n → Option G) :
    x ∈ (p.compose q).solutionSet ↔ x ∈ p.solutionSet ∧
      (fun i => x (p.rootVertex i)) ∈ q.solutionSet := by
  constructor
  · intro hx
    exact ⟨p.compose_solution_subset q hx,p.compose_solution_restrict q x hx⟩
  · rintro ⟨hp,hq⟩
    have hp' := (p.mem_solutionSet x).mp hp
    have hq' := (q.mem_solutionSet _).mp hq
    apply ((p.compose q).mem_solutionSet x).mpr
    constructor
    · intro i hz
      cases hi : p.code i with
      | none => exact hp'.1 i hi
      | some v =>
        rcases v with ⟨r,a⟩
        let k := p.rootOrderIso.symm ⟨r,p.rooted i r a hi⟩
        have hkr : p.rootVertex k = r := congrArg Subtype.val (p.rootOrderIso.apply_symm_apply _)
        change p.compositeCode q i = none at hz
        rw [p.compositeCode_some q i r a hi] at hz
        have hk : q.code k = none := Option.map_eq_none_iff.mp hz
        rw [hp'.2 i r a hi, ← hkr, hq'.1 k hk, gainAct_none]
    · intro i j g he
      cases hi : p.code i with
      | none =>
        change p.compositeCode q i = _ at he
        rw [p.compositeCode_none q i hi] at he
        cases he
      | some v =>
        rcases v with ⟨r,a⟩
        let k := p.rootOrderIso.symm ⟨r,p.rooted i r a hi⟩
        have hkr : p.rootVertex k = r := congrArg Subtype.val (p.rootOrderIso.apply_symm_apply _)
        change p.compositeCode q i = _ at he
        rw [p.compositeCode_some q i r a hi] at he
        change (q.code k).map _ = _ at he
        cases hk : q.code k with
        | none => simp [hk] at he
        | some v =>
          rcases v with ⟨s,b⟩
          simp only [hk,Option.map_some,Option.some.injEq,Prod.mk.injEq] at he
          obtain ⟨rfl,rfl⟩ := he
          rw [hp'.2 i r a hi, ← hkr, hq'.2 k s b hk, gainAct_mul]

end Dowling.GainPartition
