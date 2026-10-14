import Fan.TrailingEquiv

namespace Fan
open Finset Polynomial
open scoped Classical

theorem singleton_true : singletonConfiguration true=(⊤ : Configuration 1) := by
  have h := configuration_one_eq (⊤ : Configuration 1)
  have hb : lastBit (⊤ : Configuration 1).val.1=true :=
    (lastBit_eq_true _).mpr (top_spoke (Fin.last 0))
  rwa [hb] at h

theorem upperMu_singleton_false : upperMu (singletonConfiguration false)=-1 := by
  classical
  have h := MatroidInverseZ.mu_interval_transport singletonEmbedding singletonEmbedding_fills false true
  change IncidenceAlgebra.mu ℤ (singletonConfiguration false) (singletonConfiguration true)=_ at h
  rw [singleton_true] at h
  change upperMu (singletonConfiguration false)=_ at h
  rw [h]
  have hb := MatroidInverseZ.mu_interval_transport bitEmbedding bitEmbedding_fills false true
  rw [← hb,MatroidInverseZ.boolean_mu _ _ (by exact Finset.empty_subset _)]
  change (-1 : ℤ)^((bitSet true).card-(bitSet false).card)= -1
  simp [bitSet]

theorem flatWeight_singleton_false : flatWeight (singletonConfiguration false)=X := by
  have hr := singleton_rank false
  change configurationRank (singletonConfiguration false)=0 at hr
  unfold flatWeight
  rw [hr,upperMu_singleton_false,singleton_lowerQ]
  norm_num

theorem flatWeight_zero (p : Configuration 0) : flatWeight p=1 := by
  rw [configuration_zero_eq p]
  unfold flatWeight upperMu lowerQ
  rw [configuration_bot_rank,configuration_zero_eq (⊤ : Configuration 0)]
  simp

theorem nonhubSum_zero : nonhubSum 0=X := by
  classical
  have hnot : Fin.last 0∉(singletonConfiguration false).val.1 := by
    simp [singletonConfiguration,bitSet]
  unfold nonhubSum
  rw [sum_eq_single (singletonConfiguration false)]
  · rw [ite_eq_right hnot,flatWeight_singleton_false]
  · intro p _ hne
    by_cases hp : Fin.last 0∈p.val.1
    · exact ite_eq_left hp
    · have hb : lastBit p.val.1=false := by
        cases h : lastBit p.val.1
        · rfl
        · exact False.elim (hp ((lastBit_eq_true _).mp h))
      have he := configuration_one_eq p
      rw [hb] at he
      exact False.elim (hne he.symm)
  · simp

noncomputable def prefixWeightSum (n : ℕ) : Polynomial ℤ :=
  ∑ p : NonhubConfiguration n, flatWeight p.val

theorem prefixWeightSum_zero : prefixWeightSum 0=1 := by
  classical
  let : Unique (NonhubConfiguration 0) := {
    default := ⟨⊥,fun i => Fin.elim0 i⟩
    uniq := fun p => Subtype.ext (configuration_zero_eq p.val) }
  unfold prefixWeightSum
  rw [Fintype.sum_unique,flatWeight_zero]

theorem prefixWeightSum_succ (n : ℕ) : prefixWeightSum (n+1)=nonhubSum n := by
  classical
  have h := Finset.sum_subtype (p:=(EndsNonhub : Configuration (n+1) → Prop)) (F := inferInstanceAs (Fintype (NonhubConfiguration (n+1)))) (univ.filter (EndsNonhub : Configuration (n+1) → Prop))
    (fun p => by simp) (flatWeight : Configuration (n+1) → Polynomial ℤ)
  rw [sum_filter] at h
  simpa only [prefixWeightSum,nonhubSum,endsNonhub_succ,ite_not] using h.symm

end Fan
