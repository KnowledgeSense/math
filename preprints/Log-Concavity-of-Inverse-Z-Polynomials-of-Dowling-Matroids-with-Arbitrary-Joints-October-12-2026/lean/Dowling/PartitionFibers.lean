import Dowling.PartitionRestrictionSolutions

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- The zero block has color none; each free block has its actual least root as color. -/
def blockColor (p : GainPartition G n) (i : Fin n) : Option (Fin n) := (p.code i).map Prod.fst

def fiber (p : GainPartition G n) (c : Option (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p.blockColor i=c)

def fiberEmbedding (p : GainPartition G n) (c : Option (Fin n)) : Fin (p.fiber c).card ↪o Fin n where
  toFun i := ((p.fiber c).orderIsoOfFin rfl i).val
  inj' := by
    intro i j h
    exact ((p.fiber c).orderIsoOfFin rfl).injective (Subtype.ext h)
  map_rel_iff' := ((p.fiber c).orderIsoOfFin rfl).map_rel_iff

theorem fiberEmbedding_color (p : GainPartition G n) (c : Option (Fin n)) (i : Fin (p.fiber c).card) :
    p.blockColor (p.fiberEmbedding c i)=c :=
  (Finset.mem_filter.mp (((p.fiber c).orderIsoOfFin rfl i).property)).2

theorem fiberEmbedding_range (p : GainPartition G n) (c : Option (Fin n)) (j : Fin n)
    (hj : p.blockColor j=c) : ∃ i, p.fiberEmbedding c i=j := by
  let v : p.fiber c := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  exact ⟨((p.fiber c).orderIsoOfFin rfl).symm v,
    congrArg Subtype.val (((p.fiber c).orderIsoOfFin rfl).apply_symm_apply v)⟩

theorem blockColor_eq_of_lower_code (p q : GainPartition G n) (hqp : q ≤ p)
    (i j : Fin n) (g : G) (hij : q.code i=some (j,g)) : p.blockColor i=p.blockColor j := by
  have hrel : ∀ x ∈ p.solutionSet, x i=gainAct G (x j) g :=
    fun x hx => ((q.mem_solutionSet x).mp (hqp hx)).2 i j g hij
  rcases (p.solution_link_iff j i g).mp hrel with ⟨hj,hi⟩ | ⟨r,a,b,hj,hi,_⟩
  · simp only [blockColor,hi,hj,Option.map_none]
  · simp only [blockColor,hi,hj,Option.map_some]

theorem fiber_rootClosed (p q : GainPartition G n) (hqp : q ≤ p) (c : Option (Fin n)) :
    q.RootClosed (p.fiberEmbedding c) := by
  intro i r g hi
  apply p.fiberEmbedding_range c r
  rw [← p.blockColor_eq_of_lower_code q hqp _ r g hi,p.fiberEmbedding_color c i]

def fiberTop (p : GainPartition G n) (c : Option (Fin n)) : GainPartition G (p.fiber c).card :=
  p.restrict (p.fiberEmbedding c) (p.fiber_rootClosed p le_rfl c)

def fiberRestriction (p q : GainPartition G n) (hqp : q ≤ p) (c : Option (Fin n)) :
    GainPartition G (p.fiber c).card := q.restrict (p.fiberEmbedding c) (p.fiber_rootClosed q hqp c)

theorem fiberRestriction_le (p q : GainPartition G n) (hqp : q ≤ p) (c : Option (Fin n)) :
    p.fiberRestriction q hqp c ≤ p.fiberTop c :=
  restrict_mono _ _ _ hqp

/-- All actual vertex fibers form a disjoint exhaustive partition, including
empty colors and an empty zero block. -/
def fiberEquiv (p : GainPartition G n) : (Σ c : Option (Fin n), Fin (p.fiber c).card) ≃ Fin n :=
  Equiv.ofBijective (fun ci => p.fiberEmbedding ci.1 ci.2) (by
    constructor
    · rintro ⟨c,i⟩ ⟨d,j⟩ h
      have hcd : c=d := (p.fiberEmbedding_color c i).symm.trans
        ((congrArg p.blockColor h).trans (p.fiberEmbedding_color d j))
      subst d
      exact congrArg (Sigma.mk c) ((p.fiberEmbedding c).injective h)
    · intro j
      obtain ⟨i,hi⟩ := p.fiberEmbedding_range (p.blockColor j) j rfl
      exact ⟨⟨p.blockColor j,i⟩,hi⟩)

end Dowling.GainPartition
