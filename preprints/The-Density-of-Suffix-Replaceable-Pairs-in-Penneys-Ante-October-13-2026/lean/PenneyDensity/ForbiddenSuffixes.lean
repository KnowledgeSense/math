import PenneyDensity.Occurrences

namespace PenneyDensity

 theorem crossing_iff_overlap {a u t : Word} :
    Crossing a u t ↔ ∃ k, properOverlap a t k ∧ (a.take (a.length-k)).IsSuffix u := by
  constructor
  · rintro ⟨x,y,hx,hy,rfl,hxu,hyt⟩
    refine ⟨y.length,⟨?_,?_,?_⟩,?_⟩
    · exact List.length_pos_iff.mpr hy
    · have := List.length_pos_iff.mpr hx
      simp only [List.length_append]
      omega
    · simp only [List.length_append,Nat.add_sub_cancel,List.drop_left]
      exact List.prefix_iff_eq_take.mp hyt
    · simpa only [List.length_append,Nat.add_sub_cancel,List.take_left] using hxu
  · rintro ⟨k,⟨hk,hka,he⟩,hs⟩
    refine ⟨a.take (a.length-k),a.drop (a.length-k),?_,?_,?_,hs,?_⟩
    · intro hz
      have := congrArg List.length hz
      simp only [List.length_take,List.length_nil] at this
      omega
    · intro hz
      have := congrArg List.length hz
      simp only [List.length_drop,List.length_nil] at this
      omega
    · exact (List.take_append_drop _ _).symm
    · rw [he]
      exact List.take_prefix _ _

 theorem forbidden_suffix_iff {v w t u : Word} :
    (∃ b∈forbidden v w t,b.IsSuffix u) ↔ Crossing v u t ∨ Crossing w u t := by
  simp only [forbidden,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b,⟨a,ha,k,hk,rfl⟩,hs⟩
    rcases ha with rfl | rfl
    · exact Or.inl (crossing_iff_overlap.mpr ⟨k,hk,hs⟩)
    · exact Or.inr (crossing_iff_overlap.mpr ⟨k,hk,hs⟩)
  · rintro (hv | hw)
    · obtain ⟨k,hk,hs⟩ := crossing_iff_overlap.mp hv
      exact ⟨_,⟨v,Or.inl rfl,k,hk,rfl⟩,hs⟩
    · obtain ⟨k,hk,hs⟩ := crossing_iff_overlap.mp hw
      exact ⟨_,⟨w,Or.inr rfl,k,hk,rfl⟩,hs⟩

/-- Exact bridge from the original stopped contexts to finite forbidden
suffix generators, including the empty context. -/
theorem stopped_iff_forbidden {v w u : Word} (hlen : v.length=w.length)
    (hne : v≠w) (hv : v≠[]) :
    u∈StoppedLanguage v w ↔ Avoids v w u ∧ ¬∃ b∈forbidden v w v,b.IsSuffix u := by
  rw [stopped_iff_avoids_crossings hlen hne hv,forbidden_suffix_iff]
  tauto

 theorem forbidden_length_lt {v w t b : Word} (hlen : v.length=w.length)
    (hb : b∈forbidden v w t) : b.length<v.length := by
  obtain ⟨a,ha,k,⟨hk,hka,_⟩,rfl⟩ := hb
  have haLen : a.length=v.length := by rcases ha with rfl | rfl <;> simp_all
  simp only [List.length_take]
  omega

 theorem short_avoids {v w b : Word} (hlen : v.length=w.length) (hb : b.length<v.length) :
    Avoids v w b := by
  constructor
  · intro hh
    have := hh.length_le
    omega
  · intro hh
    have := hh.length_le
    omega

/-- Finite suffix-containment criterion for equality of the literal infinite
stopped languages. -/
theorem propertyR_iff_suffix_cover {v w : Word} (hlen : v.length=w.length)
    (hne : v≠w) (hv : v≠[]) : PropertyR v w ↔
    (∀ b∈forbidden v w v,∃ c∈forbidden v w w,c.IsSuffix b) ∧
    (∀ c∈forbidden v w w,∃ b∈forbidden v w v,b.IsSuffix c) := by
  have hw : w≠[] := by intro he; subst w; simp only [List.length_nil] at hlen; exact hv (List.length_eq_zero_iff.mp hlen)
  have hswap (t : Word) : forbidden w v t=forbidden v w t := by
    ext b
    simp only [forbidden,Set.mem_ofPred_eq,or_comm]
  constructor
  · intro hR
    have hE : StoppedLanguage v w=StoppedLanguage w v := hR
    constructor
    · intro b hb
      by_contra hh
      have hIn : b∈StoppedLanguage w v := by
        rw [stopped_iff_forbidden hlen.symm hne.symm hw,hswap]
        exact ⟨by simpa only [Avoids,and_comm] using short_avoids hlen (forbidden_length_lt hlen hb),hh⟩
      rw [← hE,stopped_iff_forbidden hlen hne hv] at hIn
      exact hIn.2 ⟨b,hb,List.suffix_refl b⟩
    · intro c hc
      by_contra hh
      have hIn : c∈StoppedLanguage v w := by
        rw [stopped_iff_forbidden hlen hne hv]
        exact ⟨short_avoids hlen (forbidden_length_lt hlen hc),hh⟩
      rw [hE,stopped_iff_forbidden hlen.symm hne.symm hw,hswap] at hIn
      exact hIn.2 ⟨c,hc,List.suffix_refl c⟩
  · rintro ⟨hvw,hwv⟩
    apply Set.ext
    intro u
    rw [stopped_iff_forbidden hlen hne hv,
      stopped_iff_forbidden hlen.symm hne.symm hw,hswap]
    have hf : (∃ b∈forbidden v w v,b.IsSuffix u) ↔ ∃ c∈forbidden v w w,c.IsSuffix u := by
      constructor
      · rintro ⟨b,hb,hbu⟩
        obtain ⟨c,hc,hcb⟩ := hvw b hb
        exact ⟨c,hc,hcb.trans hbu⟩
      · rintro ⟨c,hc,hcu⟩
        obtain ⟨b,hb,hbc⟩ := hwv c hc
        exact ⟨b,hb,hbc.trans hcu⟩
    rw [hf]
    simp only [Avoids,and_comm]

end PenneyDensity
