import Dowling.PartitionFibers

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

def glueCode (p : GainPartition G n) (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card)
    (i : Fin n) : Option (Fin n × G) :=
  let v := p.fiberEquiv.symm i
  ((q v.1).code v.2).map (fun w => (p.fiberEmbedding v.1 w.1,w.2))

theorem glueCode_vertex (p : GainPartition G n)
    (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card)
    (c : Option (Fin n)) (i : Fin (p.fiber c).card) :
    p.glueCode q (p.fiberEmbedding c i) = ((q c).code i).map (fun w => (p.fiberEmbedding c w.1,w.2)) := by
  change (let v := p.fiberEquiv.symm (p.fiberEquiv ⟨c,i⟩)
          ; ((q v.1).code v.2).map (fun w => (p.fiberEmbedding v.1 w.1,w.2))) = _
  rw [p.fiberEquiv.symm_apply_apply]

def glue (p : GainPartition G n) (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card) :
    GainPartition G n where
  code := p.glueCode q
  rooted := by
    intro i j g hij
    obtain ⟨⟨c,i⟩,rfl⟩ := p.fiberEquiv.surjective i
    change p.glueCode q (p.fiberEmbedding c i)=_ at hij
    rw [glueCode_vertex] at hij
    cases hi : (q c).code i with
    | none => simp [hi] at hij
    | some v =>
      rcases v with ⟨r,a⟩
      simp only [hi,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hij
      obtain ⟨rfl,rfl⟩ := hij
      rw [glueCode_vertex,(q c).rooted i r a hi]
      rfl
  least := by
    intro i j g hij
    obtain ⟨⟨c,i⟩,rfl⟩ := p.fiberEquiv.surjective i
    change p.glueCode q (p.fiberEmbedding c i)=_ at hij
    rw [glueCode_vertex] at hij
    cases hi : (q c).code i with
    | none => simp [hi] at hij
    | some v =>
      rcases v with ⟨r,a⟩
      simp only [hi,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hij
      obtain ⟨rfl,rfl⟩ := hij
      exact (p.fiberEmbedding c).monotone ((q c).least i r a hi)

theorem glue_rootClosed (p : GainPartition G n)
    (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card) (c : Option (Fin n)) :
    (p.glue q).RootClosed (p.fiberEmbedding c) := by
  intro i r g hi
  change p.glueCode q (p.fiberEmbedding c i)=_ at hi
  rw [glueCode_vertex] at hi
  cases hq : (q c).code i with
  | none => simp [hq] at hi
  | some v =>
    rcases v with ⟨s,a⟩
    simp only [hq,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hi
    exact ⟨s,hi.1⟩

theorem restrict_glue (p : GainPartition G n)
    (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card) (c : Option (Fin n)) :
    (p.glue q).restrict (p.fiberEmbedding c) (p.glue_rootClosed q c) = q c := by
  apply code_injective
  funext i
  apply restrictionCode_map_injective (p.fiberEmbedding c)
  rw [restrict_code_map]
  exact p.glueCode_vertex q c i

theorem glue_fiberRestriction (p q : GainPartition G n) (hqp : q ≤ p) :
    p.glue (p.fiberRestriction q hqp) = q := by
  apply code_injective
  funext i
  obtain ⟨⟨c,i⟩,rfl⟩ := p.fiberEquiv.surjective i
  change p.glueCode (p.fiberRestriction q hqp) (p.fiberEmbedding c i)=q.code (p.fiberEmbedding c i)
  rw [glueCode_vertex]
  exact q.restrict_code_map _ _ i

end Dowling.GainPartition
