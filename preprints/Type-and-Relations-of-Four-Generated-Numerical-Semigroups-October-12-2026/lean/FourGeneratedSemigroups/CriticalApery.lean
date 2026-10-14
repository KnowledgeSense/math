import FourGeneratedSemigroups.CriticalGraphClassification

noncomputable section
namespace FourGeneratedSemigroups

/-- A critical degree misses the Apéry set exactly when its critical relation
can involve the distinguished generator. -/
theorem criticalDegree_not_apery_iff_arc {S : NumericalSemigroup}
    (G : FourGenerated S) (i : Fin 4) (hi : i≠0) :
    ((criticalExponent G.generators G.positive i*G.generators i : ℕ) : ℤ)∉
      S.apery (G.generators 0) ↔ CriticalArc G.generators G.positive i 0 := by
  constructor
  · intro h
    have hm : S.memInt
        (((criticalExponent G.generators G.positive i*G.generators i : ℕ) : ℤ)-
          (G.generators 0 : ℤ)) := by
      by_contra hn
      apply h
      refine ⟨?_,hn⟩
      apply (NumericalSemigroup.memInt_natCast S _).mpr
      simpa using G.factorization_mem (Finsupp.single i (criticalExponent G.generators G.positive i))
    obtain ⟨n,hn,hnS⟩ := hm
    obtain ⟨c,hc⟩ := (G.generates n).mp hnS
    let t : Factorization := Finsupp.single 0 1+c
    have ht : factorizationMap G.generators t=
        criticalExponent G.generators G.positive i*G.generators i := by
      simp only [t,map_add,factorizationMap_single,one_mul,hc]
      omega
    have ht0 : 0<t 0 := by simp [t]
    have hti : t i=0 := by
      rcases critical_factorization_dichotomy G.generators G.positive i t ht with he|he
      · have hh := congrArg (fun a : Factorization => a 0) he
        simp [Ne.symm hi] at hh
        omega
      · exact he
    exact ⟨hi,t,hti,ht0,ht⟩
  · rintro ⟨_,c,hci,hc0,hc⟩ h
    have hle : Finsupp.single 0 1≤c := Finsupp.single_le_iff.mpr hc0
    obtain ⟨r,hr⟩ := le_iff_exists_add.mp hle
    apply h.2
    refine ⟨factorizationMap G.generators r,?_,G.factorization_mem r⟩
    have hh : G.generators 0+factorizationMap G.generators r=
      criticalExponent G.generators G.positive i*G.generators i := by simpa [hr] using hc
    omega

end FourGeneratedSemigroups
