import FourGeneratedSemigroups.StaircaseFiniteness

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma zero_variable_not_mem_staircase : Finsupp.single 0 1∉staircase G := by
  intro h
  simpa using h.1

lemma boundary_positive_zero_eq (a : Factorization) (ha : a∈staircaseBoundary G)
    (h : 0<a 0) : a=Finsupp.single 0 1 := by
  have hle : Finsupp.single 0 1≤a := Finsupp.single_le_iff.mpr h
  by_contra hn
  exact zero_variable_not_mem_staircase G (ha.2 _ (lt_of_le_of_ne hle (Ne.symm hn)))

lemma zero_variable_mem_boundary : Finsupp.single 0 1∈staircaseBoundary G := by
  obtain ⟨b,hb,hble⟩ := exists_boundary_le G _ (zero_variable_not_mem_staircase G)
  have hbpos : 0<b 0 := by
    by_contra hn
    have hbzero : b=0 := by
      ext i
      by_cases hi : i=0
      · subst i; simp only [Finsupp.zero_apply]; omega
      · have hh := hble i
        simp [Ne.symm hi] at hh
        simpa using hh
    exact boundary_nonzero G hb hbzero
  simpa [boundary_positive_zero_eq G b hb hbpos] using hb

/-- The four-variable boundary consists of the three-variable boundary and the
single eliminated variable. -/
def boundaryOptionEquiv : (staircaseBoundary G) ≃
    Option {a : Factorization // a∈staircaseBoundary G ∧ a 0=0} where
  toFun a := if h : a.val 0=0 then some ⟨a.val,a.property,h⟩ else none
  invFun a := match a with
    | none => ⟨Finsupp.single 0 1,zero_variable_mem_boundary G⟩
    | some a => ⟨a.val,a.property.1⟩
  left_inv a := by
    by_cases h : a.val 0=0
    · simp [h]
    · simp only [dite_eq_right h]
      apply Subtype.ext
      exact (boundary_positive_zero_eq G a.val a.property (Nat.pos_of_ne_zero h)).symm
  right_inv a := by
    cases a with
    | none => simp
    | some a => simp [a.property.2]

theorem boundary_card_eq_generatorNumber_add_one :
    Nat.card (staircaseBoundary G)=staircaseGeneratorNumber G+1 := by
  let : Finite {a : Factorization // a∈staircaseBoundary G ∧ a 0=0} :=
    Set.Finite.to_subtype ((finite_staircaseBoundary G (finite_staircase G)).subset (by intro a ha; exact ha.1))
  let := Fintype.ofFinite {a : Factorization // a∈staircaseBoundary G ∧ a 0=0}
  rw [Nat.card_congr (boundaryOptionEquiv G)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_option,staircaseGeneratorNumber]

end FourGeneratedSemigroups
