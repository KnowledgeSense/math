import FourGeneratedSemigroups.GoodOrdering

noncomputable section
namespace FourGeneratedSemigroups

lemma exists_perm_two (m i : Fin 4) (hmi : m≠i) :
    ∃ e : Equiv.Perm (Fin 4),e 0=m ∧ e 1=i := by
  let f : Fin 2 → Fin 4 := fun a => ⟨a.val,by omega⟩
  let g : Fin 2 → Fin 4 := ![m,i]
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun x : Fin 4 => x.val) hab
  have hg : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [g]
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨e,by simpa [f,g] using he 0,by simpa [f,g] using he 1⟩

theorem incomingDegree_critical_reindex (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (e : Equiv.Perm (Fin 4)) (v : Fin 4) :
    incomingDegree (CriticalArc (d ∘ e) (fun i => hd (e i))) v=
      incomingDegree (CriticalArc d hd) (e v) := by
  classical
  simp only [incomingDegree]
  simp_rw [criticalArc_reindex]
  exact Equiv.sum_comp e (fun u => if CriticalArc d hd u (e v) then 1 else 0)

/-- A nonprimary semigroup can always be relabeled into the secondary paired ordering. -/
theorem exists_secondary_ordering {S : NumericalSemigroup} (G : FourGenerated S)
    (hsecondary : ∀ v,incomingDegree (CriticalArc G.generators G.positive) v≤1) :
    ∃ e : Equiv.Perm (Fin 4),SecondaryCriticalOrdering (G.reindex e) ∧
      ∀ v,incomingDegree (CriticalArc (G.reindex e).generators (G.reindex e).positive) v≤1 := by
  obtain ⟨j,hj⟩ := criticalArc_exists G.generators G.positive 0
  obtain ⟨e,he0,he1⟩ := exists_perm_two j 0 (Ne.symm hj.1)
  have hs : ∀ v,incomingDegree (CriticalArc (G.reindex e).generators (G.reindex e).positive) v≤1 := by
    intro v
    change incomingDegree (CriticalArc (G.generators ∘ e) (fun i => G.positive (e i))) v≤1
    rw [incomingDegree_critical_reindex]
    exact hsecondary (e v)
  have h10 : CriticalArc (G.reindex e).generators (G.reindex e).positive 1 0 := by
    apply (criticalArc_reindex G.generators G.positive e 1 0).mpr
    simpa only [he0,he1] using hj
  exact ⟨e,secondaryCriticalOrdering_of_pair (G.reindex e) hs h10,hs⟩

/-- The distinguished-generator choices used by the proof exist for every
actual minimally four-generated numerical semigroup. -/
theorem exists_ordering {S : NumericalSemigroup} (G : FourGenerated S) :
    ∃ e : Equiv.Perm (Fin 4),
      (PrimaryOrdering (G.reindex e) ∧
        (fullSupportGeneratorNumber (G.reindex e)=0 ∨
          ((criticalExponent (G.reindex e).generators (G.reindex e).positive 3*
            (G.reindex e).generators 3 : ℕ) : ℤ)∉S.apery ((G.reindex e).generators 0))) ∨
      (SecondaryCriticalOrdering (G.reindex e) ∧
        ∀ v,incomingDegree (CriticalArc (G.reindex e).generators (G.reindex e).positive) v≤1) := by
  by_cases hp : ∃ m,2 ≤ incomingDegree (CriticalArc G.generators G.positive) m
  · obtain ⟨e,he⟩ := exists_good_primary_ordering G hp
    exact ⟨e,Or.inl he⟩
  · have hs : ∀ v,incomingDegree (CriticalArc G.generators G.positive) v≤1 := by
      intro v
      have hh : ¬2 ≤ incomingDegree (CriticalArc G.generators G.positive) v := fun h => hp ⟨v,h⟩
      omega
    obtain ⟨e,he⟩ := exists_secondary_ordering G hs
    exact ⟨e,Or.inr he⟩

end FourGeneratedSemigroups
