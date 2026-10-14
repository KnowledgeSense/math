import Dowling.BraidBlockRootInverse

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- The source potentials themselves are a nonzero solution of the balanced block. -/
theorem braidTop_potential_solution (u : Fin (n+1) → G) :
    (fun i => some (u i)) ∈ (braidTop u).solutionSet := by
  apply (mem_fromBlockRoots_solution _ _ _ _ _).mpr
  intro i
  simp [gainAct]

 theorem code_some_of_le_braidTop (u : Fin (n+1) → G) (p : GainPartition G (n+1))
    (hp : p≤braidTop u) (i : Fin (n+1)) :
    ∃ r, p.code i=some (r,(u r)⁻¹*u i) := by
  have hx := hp (braidTop_potential_solution u)
  have he := (p.mem_solutionSet _).mp hx
  cases hi : p.code i with
  | none => have h := he.1 i hi; cases h
  | some v =>
    rcases v with ⟨r,g⟩
    have h := he.2 i r g hi
    have hg : u i=u r*g := by simpa only [gainAct,Option.map_some,Option.some.injEq] using h
    have hgain : g=(u r)⁻¹*u i := by rw [hg]; group
    exact ⟨r,by rw [hgain]⟩

/-- Read the root from a nonzero code, with an irrelevant fallback for zero codes. -/
def readRoot (p : GainPartition G n) (i : Fin n) : Fin n :=
  match p.code i with | none => i | some (r,_) => r

 theorem readRoot_some (p : GainPartition G n) (i r : Fin n) (g : G)
    (hi : p.code i=some (r,g)) : p.readRoot i=r := by simp [readRoot,hi]

 theorem readRoot_le (p : GainPartition G n) (i : Fin n) : p.readRoot i ≤ i := by
  cases hi : p.code i with
  | none => simp [readRoot,hi]
  | some v =>
    rcases v with ⟨r,g⟩
    rw [p.readRoot_some i r g hi]
    exact p.least i r g hi

 theorem readRoot_idempotent (p : GainPartition G n) (i : Fin n) :
    p.readRoot (p.readRoot i)=p.readRoot i := by
  cases hi : p.code i with
  | none => simp [readRoot,hi]
  | some v =>
    rcases v with ⟨r,g⟩
    rw [p.readRoot_some i r g hi]
    exact p.readRoot_some r r 1 (p.rooted i r g hi)

 theorem eq_fromBlockRoots_of_le_braidTop (u : Fin (n+1) → G)
    (p : GainPartition G (n+1)) (hp : p≤braidTop u) :
    p=fromBlockRoots p.readRoot p.readRoot_idempotent p.readRoot_le u := by
  have hc : p.code=(fromBlockRoots p.readRoot p.readRoot_idempotent p.readRoot_le u).code := by
    funext i
    obtain ⟨r,hi⟩ := code_some_of_le_braidTop u p hp i
    change p.code i=some (p.readRoot i,(u (p.readRoot i))⁻¹*u i)
    rw [p.readRoot_some i r _ hi]
    exact hi
  exact ext_code hc

 theorem braidLift_surjective_below (u : Fin (n+1) → G)
    (p : GainPartition G (n+1)) (hp : p≤braidTop u) :
    ∃ q : GainPartition Unit n, q.braidLift u=p := by
  refine ⟨unitFromRoots p.readRoot p.readRoot_idempotent p.readRoot_le,?_⟩
  apply ext_code
  funext i
  have hr := unitBlockRoot_unitFromRoots p.readRoot p.readRoot_idempotent p.readRoot_le
  change some ((unitFromRoots p.readRoot p.readRoot_idempotent p.readRoot_le).unitBlockRoot i,
    (u ((unitFromRoots p.readRoot p.readRoot_idempotent p.readRoot_le).unitBlockRoot i))⁻¹*u i)=p.code i
  rw [hr]
  obtain ⟨r,hi⟩ := code_some_of_le_braidTop u p hp i
  rw [p.readRoot_some i r _ hi]
  exact hi.symm

end Dowling.GainPartition
