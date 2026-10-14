import FourGeneratedSemigroups.Reindex
import FourGeneratedSemigroups.OrderedTypeComparison
import Mathlib.Logic.Equiv.Fintype

noncomputable section
namespace FourGeneratedSemigroups

lemma exists_perm_three (m i j : Fin 4) (hmi : m≠i) (hmj : m≠j) (hij : i≠j) :
    ∃ e : Equiv.Perm (Fin 4),e 0=m ∧ e 1=i ∧ e 2=j := by
  let f : Fin 3 → Fin 4 := fun a => a.castSucc
  let g : Fin 3 → Fin 4 := ![m,i,j]
  have hf : Function.Injective f := Fin.castSucc_injective 3
  have hg : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [g]
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨e,by simpa [f,g] using he 0,by simpa [f,g] using he 1,by simpa [f,g] using he 2⟩

def criticalFullSupport (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4) : Prop :=
  ∃ a : Factorization,a i=0 ∧ (∀ j,j≠i → 0<a j) ∧
    factorizationMap d a=criticalExponent d hd i*d i

lemma criticalFullSupport_outdegree (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (i : Fin 4) (hi : criticalFullSupport d hd i) :
    outgoingDegree (CriticalArc d hd) i=3 := by
  classical
  obtain ⟨a,hai,hpos,ha⟩ := hi
  have he : ∀ j,CriticalArc d hd i j ↔ j≠i := by
    intro j
    exact ⟨fun h => Ne.symm h.1,fun h => ⟨Ne.symm h,a,hai,hpos j h,ha⟩⟩
  simp only [outgoingDegree,he]
  fin_cases i <;> norm_num [Fin.sum_univ_succ]

lemma two_incoming (E : Fin 4 → Fin 4 → Prop) (m : Fin 4)
    (hm : 2 ≤ incomingDegree E m) :
    ∃ i j,i≠j ∧ E i m ∧ E j m := by
  classical
  have hc : 1<(Finset.univ.filter (fun i => E i m)).card := by
    have hh : (Finset.univ.filter (fun i => E i m)).card=incomingDegree E m := by
      simp [incomingDegree]
    omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hc
  exact ⟨i,j,hij,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2⟩

lemma incoming_three_all (E : Fin 4 → Fin 4 → Prop) (hloop : ∀i,¬E i i)
    (m : Fin 4) (hm : incomingDegree E m=3) :
    ∀ i,i≠m → E i m := by
  classical
  let A := Finset.univ.filter (fun i => E i m)
  have hsub : A⊆Finset.univ.erase m := by
    intro i hi
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    intro he
    subst i
    exact hloop m (Finset.mem_filter.mp hi).2
  have hcard : A.card=3 := by simpa [A,incomingDegree] using hm
  have he : A=Finset.univ.erase m := Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  intro i hi
  have hh : i∈A := he.symm ▸ Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩
  exact (Finset.mem_filter.mp hh).2

lemma fullSupport_reindex_implies_criticalFullSupport {S : NumericalSemigroup}
    (G : FourGenerated S) (e : Equiv.Perm (Fin 4)) (a : Factorization)
    (ha : FullSupportBoundary (G.reindex e) a) :
    criticalFullSupport G.generators G.positive (e 0) := by
  refine ⟨Finsupp.domCongr e a,?_,?_,?_⟩
  · simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using ha.2.1
  · intro j hj
    have hne : e.symm j≠0 := by intro he; apply hj; simpa [he] using (e.apply_symm_apply j).symm
    simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using ha.2.2 (e.symm j) hne
  · rw [factorizationMap_reindex]
    have hh := fullSupportBoundary_weight (G.reindex e) a ha
    change factorizationMap (G.generators ∘ e) a=
      criticalExponent (G.generators ∘ e) (fun i => G.positive (e i)) 0*G.generators (e 0) at hh
    rw [criticalExponent_reindex] at hh
    exact hh

/-- Every primary semigroup admits the source's distinguished-generator choice:
the full-support boundary count vanishes or the reduction is monomial. -/
theorem exists_good_primary_ordering {S : NumericalSemigroup} (G : FourGenerated S)
    (hprimary : ∃ m,2 ≤ incomingDegree (CriticalArc G.generators G.positive) m) :
    ∃ e : Equiv.Perm (Fin 4),PrimaryOrdering (G.reindex e) ∧
      (fullSupportGeneratorNumber (G.reindex e)=0 ∨
        ((criticalExponent (G.reindex e).generators (G.reindex e).positive 3*
          (G.reindex e).generators 3 : ℕ) : ℤ)∉S.apery ((G.reindex e).generators 0)) := by
  classical
  let E := CriticalArc G.generators G.positive
  let Φ := Finset.univ.filter (criticalFullSupport G.generators G.positive)
  have hloop : ∀ i,¬E i i := fun i h => h.1 rfl
  obtain ⟨m,hm,hgood⟩ := exists_primary_ordering_vertex E Φ hloop
    (criticalArc_outgoing_positive G.generators G.positive)
    (fun i hi => criticalFullSupport_outdegree G.generators G.positive i (Finset.mem_filter.mp hi).2)
    hprimary
  obtain ⟨i,j,hij,him,hjm⟩ := two_incoming E m hm
  obtain ⟨e,he0,he1,he2⟩ := exists_perm_three m i j (Ne.symm him.1) (Ne.symm hjm.1) hij
  have hG : PrimaryOrdering (G.reindex e) := by
    constructor
    · apply (criticalArc_reindex G.generators G.positive e 1 0).mpr
      simpa only [he0,he1] using him
    · apply (criticalArc_reindex G.generators G.positive e 2 0).mpr
      simpa only [he0,he2] using hjm
  refine ⟨e,hG,?_⟩
  rcases hgood with hout|hthree
  · left
    let : IsEmpty {a : Factorization // a∈staircaseBoundary (G.reindex e) ∧ a 0=0 ∧
        0<a 1 ∧ 0<a 2 ∧ 0<a 3} := ⟨by
      intro a
      apply hout
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have hh := fullSupport_reindex_implies_criticalFullSupport G e a.val
        ((fullSupportBoundary_iff (G.reindex e) a.val).mpr a.property)
      simpa only [he0] using hh⟩
    simp [fullSupportGeneratorNumber]
  · right
    apply (criticalDegree_not_apery_iff_arc (G.reindex e) 3 (by decide)).mpr
    apply (criticalArc_reindex G.generators G.positive e 3 0).mpr
    rw [he0]
    apply incoming_three_all E hloop m hthree
    intro he
    have hh := e.injective (he.trans he0.symm)
    cases hh

end FourGeneratedSemigroups
