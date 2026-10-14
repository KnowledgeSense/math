import FourGeneratedSemigroups.BoundaryGeneratorFamily
import FourGeneratedSemigroups.OrderedTypeComparison
import FourGeneratedSemigroups.FiniteGeneratorExtraction

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma primary_critical_normal_form_first_positive (hG : PrimaryOrdering G)
    (p : Factorization) (hpT : p∈staircase G) (hp3 : p 3=0)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3) : 0<p 1 := by
  by_contra hn
  have hp1 : p 1=0 := by omega
  have hshape : p=Finsupp.single 2 (p 2) := by
    ext i
    fin_cases i <;> simp_all [hpT.1]
  have hw : p 2*G.generators 2=
      criticalExponent G.generators G.positive 3*G.generators 3 := by
    rw [hshape,factorizationMap_single] at hp
    exact hp
  have hpos : 0<p 2 := by
    have := (criticalExponent_spec G.generators G.positive 3).1
    have := G.positive 3
    nlinarith
  have hmin := criticalExponent_le G.generators G.positive 2 (p 2)
    ⟨hpos,Finsupp.single 3 (criticalExponent G.generators G.positive 3),by simp,
      by simpa using hw.symm⟩
  have hbound := apery_coordinate_lt_of_criticalArc G 2 hG.2 p hpT.2.2
  omega

lemma no_fullSupport_of_number_zero (hr : fullSupportGeneratorNumber G=0) :
    ∀a, ¬FullSupportBoundary G a := by
  intro a ha
  let T := {b : Factorization // b∈staircaseBoundary G ∧ b 0=0 ∧ 0<b 1 ∧ 0<b 2 ∧ 0<b 3}
  let : Finite T := Set.Finite.to_subtype
    ((finite_staircaseBoundary G (finite_staircase G)).subset (by intro b hb; exact hb.1))
  let : Nonempty T := ⟨⟨a,(fullSupportBoundary_iff G a).mp ha⟩⟩
  have hh := Nat.card_pos (α := T)
  change 0<fullSupportGeneratorNumber G at hh
  omega

lemma secondary_critical_degree_mem_apery (hG : SecondaryCriticalOrdering G)
    (hsecondary : ∀v, incomingDegree (CriticalArc G.generators G.positive) v≤1) :
    ((criticalExponent G.generators G.positive 3*G.generators 3 : ℕ) : ℤ)∈S.apery (G.generators 0) := by
  by_contra hn
  have h30 := (criticalDegree_not_apery_iff_arc G 3 (by decide)).mp hn
  have h32 : CriticalArc G.generators G.positive 3 2 := by
    refine ⟨by decide,Finsupp.single 2 (criticalExponent G.generators G.positive 2),by simp,?_,?_⟩
    · simpa using (criticalExponent_spec G.generators G.positive 2).1
    · simpa using hG.2
  have hh := criticalArc_unique_of_secondary G.generators G.positive hsecondary 3 0 2 h30 h32
  contradiction

end FourGeneratedSemigroups
