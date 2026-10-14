import FourGeneratedSemigroups.BoundaryPresentation

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

def FullSupportBoundary (a : Factorization) : Prop :=
  a∈staircaseBoundary G ∧ a 0=0 ∧ ∀ i : Fin 4,i≠0 → 0<a i

lemma boundary_predecessor (a : Factorization) (ha : a∈staircaseBoundary G)
    (i : Fin 4) (hi : 0<a i) :
    a-Finsupp.single i 1∈staircase G := by
  apply ha.2
  apply lt_of_le_of_ne tsub_le_self
  intro he
  have hh := congrArg (fun c : Factorization => c i) he
  simp only [Finsupp.tsub_apply,Finsupp.single_eq_same] at hh
  omega

lemma fullSupport_factorization_pure_zero (a : Factorization) (ha : FullSupportBoundary G a)
    (c : Factorization) (hc : factorizationMap G.generators c=factorizationMap G.generators a)
    (hc0 : 0<c 0) : c=Finsupp.single 0 (c 0) := by
  ext i
  by_cases hi : i=0
  · subst i; simp
  · have hci : c i=0 := by
      by_contra hci
      have haPred := boundary_predecessor G a ha.1 i (ha.2.2 i hi)
      have hale : Finsupp.single i 1≤a := Finsupp.single_le_iff.mpr (ha.2.2 i hi)
      have hcle : Finsupp.single i 1≤c := Finsupp.single_le_iff.mpr (by omega)
      have har := tsub_add_cancel_of_le hale
      have hcr := tsub_add_cancel_of_le hcle
      have hw : factorizationMap G.generators (c-Finsupp.single i 1)=
          factorizationMap G.generators (a-Finsupp.single i 1) := by
        have hh1 := congrArg (factorizationMap G.generators) har
        have hh2 := congrArg (factorizationMap G.generators) hcr
        simp only [map_add] at hh1 hh2
        omega
      have hz := G.factorization_coordinate_zero_of_apery 0 (c-Finsupp.single i 1)
        (by simpa only [hw] using haPred.2.2)
      simp [Finsupp.tsub_apply,Ne.symm hi] at hz
      omega
    simp [hi,hci]

/-- Every full-support boundary monomial is a critical relation for generator zero. -/
theorem fullSupportBoundary_weight (a : Factorization) (ha : FullSupportBoundary G a) :
    factorizationMap G.generators a=
      criticalExponent G.generators G.positive 0*G.generators 0 := by
  have hne : a≠topPower G := by
    intro he
    have hh := ha.2.2 1 (by decide)
    simp [he,topPower] at hh
  have hnA := boundary_not_apery G a ((mem_threeBoundaryFinset G a).mpr ⟨ha.1,ha.2.1⟩) hne
  obtain ⟨c,hc0,hc⟩ := exists_factorization_using_zero G a hnA
  have he := fullSupport_factorization_pure_zero G a ha c hc hc0
  have hw : factorizationMap G.generators a=c 0*G.generators 0 := by
    calc
      _ = factorizationMap G.generators c := hc.symm
      _ = factorizationMap G.generators (Finsupp.single 0 (c 0)) := congrArg _ he
      _ = _ := factorizationMap_single _ _ _
  have hmin := criticalExponent_le G.generators G.positive 0 (c 0) ⟨hc0,a,ha.2.1,hw⟩
  have hq : c 0=criticalExponent G.generators G.positive 0 := by
    by_contra hq
    obtain ⟨v,hv0,hv⟩ := (criticalExponent_spec G.generators G.positive 0).2
    let b : Factorization := Finsupp.single 0 (c 0-criticalExponent G.generators G.positive 0)+v
    have hb0 : 0<b 0 := by simp only [b,Finsupp.add_apply,Finsupp.single_eq_same,hv0,add_zero]; omega
    have hb : factorizationMap G.generators b=factorizationMap G.generators a := by
      simp only [b,map_add,factorizationMap_single,hv,hw]
      rw [←add_mul,Nat.sub_add_cancel hmin]
    have hbPure := fullSupport_factorization_pure_zero G a ha b hb hb0
    have hvzero : v=0 := by
      ext i
      by_cases hi : i=0
      · subst i; exact hv0
      · have hh := congrArg (fun x : Factorization => x i) hbPure
        simpa [b,hi] using hh
    have hpos := (criticalExponent_spec G.generators G.positive 0).1
    have hd := G.positive 0
    rw [hvzero,map_zero] at hv
    nlinarith
  simpa [hq] using hw

theorem fullSupportBoundary_all_arcs (a : Factorization) (ha : FullSupportBoundary G a) :
    ∀ i : Fin 4,i≠0 → CriticalArc G.generators G.positive 0 i := by
  intro i hi
  exact ⟨Ne.symm hi,a,ha.2.1,ha.2.2 i hi,fullSupportBoundary_weight G a ha⟩


lemma fullSupportBoundary_axis_bound (a : Factorization) (ha : FullSupportBoundary G a)
    (i j : Fin 4) (hj0 : j≠0) (hji : j≠i) (n : ℕ)
    (hn : Finsupp.single i n∉staircase G) : a i<n := by
  by_contra h
  have hle : Finsupp.single i n≤a := Finsupp.single_le_iff.mpr (Nat.le_of_not_gt h)
  have hne : Finsupp.single i n≠a := by
    intro he
    have hh := congrArg (fun c : Factorization => c j) he
    have hpos := ha.2.2 j hj0
    simp [hji] at hh
    omega
  exact hn (ha.1.2 _ (lt_of_le_of_ne hle hne))

lemma primary_fullSupport_bounds (hG : PrimaryOrdering G) (a : Factorization)
    (ha : FullSupportBoundary G a) :
    ∀ i : Fin 4,i≠0 → a i<criticalExponent G.generators G.positive i := by
  intro i hi
  fin_cases i
  · contradiction
  · apply fullSupportBoundary_axis_bound G a ha 1 2 (by decide) (by decide)
    intro hh
    exact (criticalDegree_not_apery_iff_arc G 1 (by decide)).mpr hG.1 (by simpa using hh.2.2)
  · apply fullSupportBoundary_axis_bound G a ha 2 1 (by decide) (by decide)
    intro hh
    exact (criticalDegree_not_apery_iff_arc G 2 (by decide)).mpr hG.2 (by simpa using hh.2.2)
  · apply fullSupportBoundary_axis_bound G a ha 3 1 (by decide) (by decide)
    exact (top_power_mem_boundary G).1

/-- In a primary ordering there is at most one full-support boundary monomial. -/
theorem primary_fullSupport_subsingleton (hG : PrimaryOrdering G) :
    Set.Subsingleton {a : Factorization | FullSupportBoundary G a} := by
  intro a ha b hb
  apply criticalBox_weight_injective G.generators G.positive a b ha.2.1 hb.2.1
    (primary_fullSupport_bounds G hG a ha) (primary_fullSupport_bounds G hG b hb)
  rw [fullSupportBoundary_weight G a ha,fullSupportBoundary_weight G b hb]

/-- A secondary critical graph permits no full-support boundary monomial. -/
theorem secondary_no_fullSupport
    (hsecondary : ∀ v,incomingDegree (CriticalArc G.generators G.positive) v≤1)
    (a : Factorization) : ¬FullSupportBoundary G a := by
  intro ha
  have hu := criticalArc_unique_of_secondary G.generators G.positive hsecondary
  have hh := hu 0 1 2 (fullSupportBoundary_all_arcs G a ha 1 (by decide))
    (fullSupportBoundary_all_arcs G a ha 2 (by decide))
  cases hh

lemma fullSupportBoundary_iff (a : Factorization) :
    FullSupportBoundary G a ↔
      a∈staircaseBoundary G ∧ a 0=0 ∧ 0<a 1 ∧ 0<a 2 ∧ 0<a 3 := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2 1 (by decide),h.2.2 2 (by decide),h.2.2 3 (by decide)⟩
  · rintro ⟨ha,ha0,h1,h2,h3⟩
    refine ⟨ha,ha0,?_⟩
    intro i hi
    fin_cases i <;> simp_all

theorem primary_fullSupportGeneratorNumber_le_one (hG : PrimaryOrdering G) :
    fullSupportGeneratorNumber G≤1 := by
  let f : {a : Factorization // a∈staircaseBoundary G ∧ a 0=0 ∧ 0<a 1 ∧ 0<a 2 ∧ 0<a 3} → Unit :=
    fun _ => ()
  have hf : Function.Injective f := by
    intro a b _
    exact Subtype.ext (primary_fullSupport_subsingleton G hG
      ((fullSupportBoundary_iff G a.val).mpr a.property)
      ((fullSupportBoundary_iff G b.val).mpr b.property))
  simpa only [Nat.card_unique,fullSupportGeneratorNumber] using Nat.card_le_card_of_injective f hf

end FourGeneratedSemigroups
