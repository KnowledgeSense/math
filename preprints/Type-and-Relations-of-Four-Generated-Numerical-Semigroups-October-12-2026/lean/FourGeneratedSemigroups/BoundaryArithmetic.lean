import FourGeneratedSemigroups.FullSupportBoundary

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

def PlaneBoundary (a : Factorization) : Prop :=
  a∈staircaseBoundary G ∧ a 0=0 ∧ a 3=0 ∧ 0<a 1 ∧ 0<a 2

/-- A boundary monomial and a factorization using generator zero cannot overlap
in any variable appearing in the boundary monomial. -/
lemma boundary_factorization_disjoint (a : Factorization) (ha : a∈staircaseBoundary G)
    (c : Factorization) (hc : factorizationMap G.generators c=factorizationMap G.generators a)
    (hc0 : 0<c 0) (i : Fin 4) (hi : i≠0) (hai : 0<a i) : c i=0 := by
  by_contra hci
  have haPred := boundary_predecessor G a ha i hai
  have hale : Finsupp.single i 1≤a := Finsupp.single_le_iff.mpr hai
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

lemma plane_carry_third_lt (p : Factorization) (hp0 : p 0=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (a : Factorization) (ha : PlaneBoundary G a) (c : Factorization)
    (hc : factorizationMap G.generators c=factorizationMap G.generators a) (hc0 : 0<c 0) :
    c 3<criticalExponent G.generators G.positive 3 := by
  by_contra hn
  have hle : topPower G≤c := Finsupp.single_le_iff.mpr (Nat.le_of_not_gt hn)
  obtain ⟨r,hr⟩ := le_iff_exists_add.mp hle
  have hw : factorizationMap G.generators (p+r)=factorizationMap G.generators a := by
    simpa [hr,topPower,hp] using hc
  have hpos : 0<(p+r) 0 := by simpa [hr,topPower,hp0] using hc0
  have hz := boundary_factorization_disjoint G a ha.1 (p+r) hw hpos 2 (by decide) ha.2.2.2.2
  simp only [Finsupp.add_apply] at hz
  omega

/-- The zero coefficient of every carry factorization of a plane boundary
generator is bounded by the actual critical exponent at zero. -/
lemma plane_carry_zero_le (p : Factorization) (hp0 : p 0=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (a : Factorization) (ha : PlaneBoundary G a) (c : Factorization)
    (hc : factorizationMap G.generators c=factorizationMap G.generators a) (_hc0 : 0<c 0) :
    c 0≤criticalExponent G.generators G.positive 0 := by
  by_contra hn
  have hle : Finsupp.single 0 (criticalExponent G.generators G.positive 0)≤c :=
    Finsupp.single_le_iff.mpr (by omega)
  obtain ⟨r,hr⟩ := le_iff_exists_add.mp hle
  obtain ⟨v,hv0,hv⟩ := (criticalExponent_spec G.generators G.positive 0).2
  have hw : factorizationMap G.generators (v+r)=factorizationMap G.generators a := by
    simpa [hr,hv] using hc
  have hpos : 0<(v+r) 0 := by
    have hh : c 0=criticalExponent G.generators G.positive 0+r 0 := by simp [hr]
    simp only [Finsupp.add_apply,hv0,zero_add]
    omega
  have hv1 := boundary_factorization_disjoint G a ha.1 (v+r) hw hpos 1 (by decide) ha.2.2.2.1
  have hv2 := boundary_factorization_disjoint G a ha.1 (v+r) hw hpos 2 (by decide) ha.2.2.2.2
  simp only [Finsupp.add_apply] at hv1 hv2
  have hshape : v=Finsupp.single 3 (v 3) := by
    ext i; fin_cases i <;> simp_all
  have hweight : v 3*G.generators 3=
      criticalExponent G.generators G.positive 0*G.generators 0 := by
    rw [hshape,factorizationMap_single] at hv
    exact hv
  have hv3pos : 0<v 3 := by
    have := (criticalExponent_spec G.generators G.positive 0).1
    have := G.positive 0
    nlinarith
  have hmin := criticalExponent_le G.generators G.positive 3 (v 3)
    ⟨hv3pos,Finsupp.single 0 (criticalExponent G.generators G.positive 0),by simp,
      by simpa using hweight.symm⟩
  have hbound := plane_carry_third_lt G p hp0 hp2 hp a ha (v+r) hw hpos
  simp only [Finsupp.add_apply] at hbound
  omega

lemma boundary_axis_bound (a : Factorization) (ha : a∈staircaseBoundary G)
    (i j : Fin 4) (hji : j≠i) (haj : 0<a j) (n : ℕ)
    (hn : Finsupp.single i n∉staircase G) : a i<n := by
  by_contra h
  have hle : Finsupp.single i n≤a := Finsupp.single_le_iff.mpr (Nat.le_of_not_gt h)
  have hne : Finsupp.single i n≠a := by
    intro he
    have hh := congrArg (fun c : Factorization => c j) he
    simp [hji] at hh
    omega
  exact hn (ha.2 _ (lt_of_le_of_ne hle hne))

lemma primary_plane_bounds (hG : PrimaryOrdering G) (a : Factorization) (ha : PlaneBoundary G a) :
    a 1<criticalExponent G.generators G.positive 1 ∧
      a 2<criticalExponent G.generators G.positive 2 := by
  constructor
  · apply boundary_axis_bound G a ha.1 1 2 (by decide) ha.2.2.2.2
    intro hh
    exact (criticalDegree_not_apery_iff_arc G 1 (by decide)).mpr hG.1 (by simpa using hh.2.2)
  · apply boundary_axis_bound G a ha.1 2 1 (by decide) ha.2.2.2.1
    intro hh
    exact (criticalDegree_not_apery_iff_arc G 2 (by decide)).mpr hG.2 (by simpa using hh.2.2)

/-- At most one plane boundary generator can have the exceptional critical-zero degree. -/
theorem exceptional_plane_boundary_unique (hG : PrimaryOrdering G)
    (a b : Factorization) (ha : PlaneBoundary G a) (hb : PlaneBoundary G b)
    (q r : ℕ) (hq : q<criticalExponent G.generators G.positive 3)
    (hr : r<criticalExponent G.generators G.positive 3)
    (hwa : factorizationMap G.generators a=
      criticalExponent G.generators G.positive 0*G.generators 0+q*G.generators 3)
    (hwb : factorizationMap G.generators b=
      criticalExponent G.generators G.positive 0*G.generators 0+r*G.generators 3) : a=b := by
  have habounds := primary_plane_bounds G hG a ha
  have hbbounds := primary_plane_bounds G hG b hb
  have he : a+Finsupp.single 3 r=b+Finsupp.single 3 q := by
    apply criticalBox_weight_injective G.generators G.positive
    · simp [ha.2.1]
    · simp [hb.2.1]
    · intro i hi; fin_cases i <;> simp_all [ha.2.2.1]
    · intro i hi; fin_cases i <;> simp_all [hb.2.2.1]
    · simp only [map_add,factorizationMap_single,hwa,hwb]
      omega
  have hqr : r=q := by
    have hh := congrArg (fun c : Factorization => c 3) he
    simpa [ha.2.2.1,hb.2.2.1] using hh
  rw [hqr] at he
  exact add_right_cancel he

end FourGeneratedSemigroups
