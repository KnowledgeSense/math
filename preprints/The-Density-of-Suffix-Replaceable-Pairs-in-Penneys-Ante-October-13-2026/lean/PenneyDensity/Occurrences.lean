import PenneyDensity.Definitions

namespace PenneyDensity

/-- An occurrence ending strictly before the end of a word. -/
def EarlyOccurrence (a z : Word) : Prop :=
  ∃ l r : Word, l++a++r=z ∧ r≠[]

/-- A target straddles the concatenation boundary. -/
def Crossing (a u t : Word) : Prop :=
  ∃ x y : Word, x≠[] ∧ y≠[] ∧ a=x++y ∧ x.IsSuffix u ∧ y.IsPrefix t

 theorem early_append_iff {a u t : Word} (hlen : a.length=t.length) (ht : t≠[]) :
    EarlyOccurrence a (u++t) ↔ a.IsInfix u ∨ Crossing a u t := by
  constructor
  · rintro ⟨l,r,he,hr⟩
    rcases List.append_eq_append_iff.mp he with ⟨b,hu,_⟩ | ⟨b,hl,htb⟩
    · exact Or.inl ⟨l,b,hu.symm⟩
    · rcases List.append_eq_append_iff.mp hl with ⟨x,hux,hax⟩ | ⟨d,hld,hbd⟩
      · by_cases hx : x=[]
        · subst x
          simp only [List.nil_append] at hax
          have hh := congrArg List.length htb
          simp only [List.length_append,← hax] at hh
          have : r.length=0 := by omega
          exact False.elim (hr (List.length_eq_zero_iff.mp this))
        · by_cases hb : b=[]
          · subst b
            simp only [List.append_nil] at hax
            exact Or.inl ⟨l,[],by simpa [hax] using hux.symm⟩
          · exact Or.inr ⟨x,b,hx,hb,hax,⟨l,hux.symm⟩,⟨r,htb.symm⟩⟩
      · have hh := congrArg List.length htb
        simp only [hbd,List.length_append] at hh
        have : r.length=0 := by omega
        exact False.elim (hr (List.length_eq_zero_iff.mp this))
  · rintro (⟨l,r,hu⟩ | ⟨x,y,hx,hy,ha,⟨l,hu⟩,⟨r,htr⟩⟩)
    · refine ⟨l,r++t,?_,?_⟩
      · simp only [← List.append_assoc,hu]
      · intro hh
        exact ht ((List.append_eq_nil_iff.mp hh).2)
    · refine ⟨l,r,?_,?_⟩
      · simp only [ha,← hu,← htr,List.append_assoc]
      · intro hr
        subst r
        simp only [List.append_nil] at htr
        have hh := congrArg List.length ha
        have hyt := congrArg List.length htr
        simp only [List.length_append] at hh
        have : x.length=0 := by omega
        exact hx (List.length_eq_zero_iff.mp this)

 theorem stopped_iff_no_early {v w u : Word} :
    u∈StoppedLanguage v w ↔ ¬EarlyOccurrence v (u++v) ∧ ¬w.IsInfix (u++v) := by
  constructor
  · rintro ⟨hv,hw⟩
    refine ⟨?_,hw⟩
    rintro ⟨l,r,he,hr⟩
    exact hr (hv l r he.symm).2
  · rintro ⟨hv,hw⟩
    refine ⟨?_,hw⟩
    intro l r he
    have hr : r=[] := by
      by_contra hh
      exact hv ⟨l,r,he.symm,hh⟩
    refine ⟨?_,hr⟩
    simpa only [hr,List.append_nil,List.append_left_inj] using he.symm

 theorem infix_append_of_equal_length {a u t : Word} (hlen : a.length=t.length)
    (hne : a≠t) : a.IsInfix (u++t) ↔ a.IsInfix u ∨ Crossing a u t := by
  rw [List.infix_append_iff_ne_nil]
  constructor
  · rintro (ha | ha | hc)
    · exact Or.inl ha
    · exact False.elim (hne (ha.eq_of_length hlen))
    · exact Or.inr hc
  · rintro (ha | hc)
    · exact Or.inl ha
    · exact Or.inr (Or.inr hc)

 theorem stopped_iff_avoids_crossings {v w u : Word} (hlen : v.length=w.length)
    (hne : v≠w) (hv : v≠[]) :
    u∈StoppedLanguage v w ↔ Avoids v w u ∧ ¬Crossing v u v ∧ ¬Crossing w u v := by
  rw [stopped_iff_no_early,early_append_iff rfl hv,
    infix_append_of_equal_length hlen.symm hne.symm]
  simp only [Avoids,not_or]
  tauto

end PenneyDensity
