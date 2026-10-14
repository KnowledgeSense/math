import Dowling.GainWalks

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem balanced_of_nonzero_solution (S : Set (Edge G n)) (i : Fin n)
    {x : Fin n → Option G} (hx : x ∈ solutions G n S) (hi : x i ≠ none) : BalancedAt S i := by
  constructor
  · intro j hj he
    obtain ⟨g,p⟩ := hj
    have hp := p.equation hx
    have hz : x j = none := hx (Sum.inl j) he
    rw [hz] at hp
    exact hi ((gainAct_eq_none_iff _ _).mp hp.symm)
  · intro g p
    have hp := p.equation hx
    have hh : gainAct G (x i) g = gainAct G (x i) 1 := by
      rw [gainAct_one]
      exact hp.symm
    exact ((gainAct_same_base _ _ _).mp hh).resolve_left hi

theorem BalancedAt.gain_unique {S : Set (Edge G n)} {i j : Fin n} (hi : BalancedAt S i)
    {g h : G} (p : GainWalk S i j g) (q : GainWalk S i j h) : g = h := by
  have he := hi.2 (g*h⁻¹) (p.trans q.reverse)
  exact mul_inv_eq_one.mp he

/-- A literal potential supported on one balanced connected component. -/
def componentPotential (S : Set (Edge G n)) (i : Fin n) (j : Fin n) : Option G :=
  if hj : Connected S i j then some hj.choose else none

theorem componentPotential_nonzero (S : Set (Edge G n)) (i j : Fin n) :
    componentPotential S i j ≠ none ↔ Connected S i j := by
  by_cases hj : Connected S i j <;> simp [componentPotential, hj]

theorem componentPotential_arc {S : Set (Edge G n)} {i j k : Fin n}
    (hi : BalancedAt S i) {g : G} (h : Arc S j k g) :
    componentPotential S i k = gainAct G (componentPotential S i j) g := by
  by_cases hj : Connected S i j
  · have hk : Connected S i k := ⟨hj.choose*g,hj.choose_spec.trans (GainWalk.single h)⟩
    have he : hk.choose = hj.choose*g := hi.gain_unique hk.choose_spec
      (hj.choose_spec.trans (GainWalk.single h))
    simp [componentPotential, hj, hk, gainAct, he]
  · have hk : ¬ Connected S i k := by
      rintro ⟨a,p⟩
      exact hj ⟨a*g⁻¹,p.trans (GainWalk.single h.reverse)⟩
    simp [componentPotential, hj, hk, gainAct]

theorem componentPotential_mem {S : Set (Edge G n)} {i : Fin n} (hi : BalancedAt S i) :
    componentPotential S i ∈ solutions G n S := by
  intro e he
  cases e with
  | inl j =>
    change componentPotential S i j = none
    have hj : ¬ Connected S i j := fun hj => hi.1 j hj he
    simp [componentPotential, hj]
  | inr e =>
    exact componentPotential_arc hi ⟨e,he,Or.inl ⟨rfl,rfl,rfl⟩⟩

/-- Balancedness is equivalent to having a nonzero solution at the vertex. -/
theorem balanced_iff_nonzero_solution (S : Set (Edge G n)) (i : Fin n) :
    BalancedAt S i ↔ ∃ x ∈ solutions G n S, x i ≠ none := by
  constructor
  · intro hi
    refine ⟨componentPotential S i,componentPotential_mem hi,?_⟩
    exact (componentPotential_nonzero S i i).mpr ⟨1,GainWalk.nil i⟩
  · rintro ⟨x,hx,hi⟩
    exact balanced_of_nonzero_solution S i hx hi

end Dowling
