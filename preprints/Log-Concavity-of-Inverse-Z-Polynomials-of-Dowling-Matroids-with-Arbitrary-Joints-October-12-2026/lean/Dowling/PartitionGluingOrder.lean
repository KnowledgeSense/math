import Dowling.PartitionGluing

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem mem_glue_solutionSet (p : GainPartition G n)
    (q : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card) (x : Fin n → Option G) :
    x ∈ (p.glue q).solutionSet ↔ ∀ c, (fun i => x (p.fiberEmbedding c i)) ∈ (q c).solutionSet := by
  constructor
  · intro hx c
    have h := ((p.glue q).mem_solutionSet x).mp hx
    apply ((q c).mem_solutionSet _).mpr
    constructor
    · intro i hi
      apply h.1
      change p.glueCode q (p.fiberEmbedding c i)=none
      rw [glueCode_vertex,hi]
      rfl
    · intro i j g hi
      apply h.2
      change p.glueCode q (p.fiberEmbedding c i)=some (p.fiberEmbedding c j,g)
      rw [glueCode_vertex,hi]
      rfl
  · intro hx
    apply ((p.glue q).mem_solutionSet x).mpr
    constructor
    · intro i hi
      obtain ⟨⟨c,i⟩,rfl⟩ := p.fiberEquiv.surjective i
      change p.glueCode q (p.fiberEmbedding c i)=none at hi
      rw [glueCode_vertex] at hi
      exact (((q c).mem_solutionSet _).mp (hx c)).1 i (Option.map_eq_none_iff.mp hi)
    · intro i j g hi
      obtain ⟨⟨c,i⟩,rfl⟩ := p.fiberEquiv.surjective i
      change p.glueCode q (p.fiberEmbedding c i)=_ at hi
      rw [glueCode_vertex] at hi
      cases hq : (q c).code i with
      | none => simp [hq] at hi
      | some v =>
        rcases v with ⟨r,a⟩
        simp only [hq,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hi
        obtain ⟨rfl,rfl⟩ := hi
        exact (((q c).mem_solutionSet _).mp (hx c)).2 i r a hq

theorem glue_mono (p : GainPartition G n)
    {q r : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card} (hqr : q ≤ r) :
    p.glue q ≤ p.glue r := by
  intro x hx
  rw [p.mem_glue_solutionSet] at hx ⊢
  exact fun c => hqr c (hx c)

theorem glue_le_iff (p : GainPartition G n)
    (q r : ∀ c : Option (Fin n), GainPartition G (p.fiber c).card) :
    p.glue q ≤ p.glue r ↔ q ≤ r := by
  constructor
  · intro h c
    have hr := restrict_mono (p.fiberEmbedding c) (p.glue_rootClosed q c) (p.glue_rootClosed r c) h
    rwa [restrict_glue,restrict_glue] at hr
  · exact p.glue_mono

theorem glue_fiberTop (p : GainPartition G n) : p.glue p.fiberTop = p :=
  p.glue_fiberRestriction p le_rfl

/-- A genuine product decomposition of the complete lower interval into the
zero-block interval and all balanced-block intervals. Empty blocks are retained. -/
def lowerProductOrderIso (p : GainPartition G n) :
    (∀ c : Option (Fin n), Set.Iic (p.fiberTop c)) ≃o Set.Iic p where
  toFun q := ⟨p.glue (fun c => (q c).val), by
    exact (p.glue_mono (fun c => (q c).property)).trans_eq p.glue_fiberTop⟩
  invFun q c := ⟨p.fiberRestriction q.val q.property c,p.fiberRestriction_le q.val q.property c⟩
  left_inv q := by
    funext c
    apply Subtype.ext
    exact p.restrict_glue (fun c => (q c).val) c
  right_inv q := Subtype.ext (p.glue_fiberRestriction q.val q.property)
  map_rel_iff' := by
    intro q r
    exact p.glue_le_iff (fun c => (q c).val) (fun c => (r c).val)

end Dowling.GainPartition
