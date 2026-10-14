import MainTheorems.Corona.Positive

namespace ResearchMain.Corona

open Classical Polynomial

variable {W : Type} [Fintype W] [DecidableEq W]

def CliqueMinusEdge (H : SimpleGraph W) : Prop :=
  ∃ u v, u ≠ v ∧ ∀ w z, H.Adj w z ↔
    w ≠ z ∧ ¬(w = u ∧ z = v ∨ w = v ∧ z = u)

omit [Fintype W] in
theorem independent_pair (H : SimpleGraph W) (u v : W) :
    H.IsIndepSet ({u, v} : Finset W) ↔ ¬H.Adj u v := by
  rw [independent_iff]
  constructor
  · intro h
    exact h u (by simp) v (by simp)
  · intro h w hw z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
    rcases hw with rfl | rfl <;> rcases hz with rfl | rfl
    · exact H.irrefl
    · exact h
    · exact fun h' => h h'.symm
    · exact H.irrefl

theorem independentCount_one (H : SimpleGraph W) : independentCount H 1 = Fintype.card W := by
  have he : (independentSets H).filter (fun S => S.card = 1) =
      Finset.univ.image (fun w : W => ({w} : Finset W)) := by
    ext S
    simp only [Finset.mem_filter, mem_independentSets, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.card_eq_one]
    constructor
    · rintro ⟨_, w, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨independent_singleton H w, w, rfl⟩
  unfold independentCount
  rw [he, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro u v huv
    simpa only [Finset.singleton_inj] using huv

theorem independent_card_le_two_of_unique_pair (H : SimpleGraph W)
    (h₂ : independentCount H 2 = 1) {S : Finset W} (hS : H.IsIndepSet (S : Set W)) :
    S.card ≤ 2 := by
  obtain ⟨T, hT⟩ := Finset.card_eq_one.mp h₂
  have hpair {A : Finset W} (hA : H.IsIndepSet (A : Set W)) (hc : A.card = 2) : A = T := by
    have ha : A ∈ (independentSets H).filter (fun R => R.card = 2) :=
      Finset.mem_filter.mpr ⟨(mem_independentSets _ _).mpr hA, hc⟩
    rw [hT, Finset.mem_singleton] at ha
    exact ha
  by_contra h
  obtain ⟨A, hAS, hAc⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ S.card)
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hAc
  have h₁ := hpair (independent_mono H hS (by
    intro z hz
    exact hAS (by simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto)))
    (Finset.card_pair huv)
  have h₂' := hpair (A := {u, w}) (independent_mono H hS (by
    intro z hz
    exact hAS (by simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto)))
    (Finset.card_pair huw)
  have hv : v ∈ ({u, w} : Finset W) := by rw [h₂', ← h₁]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv
  · exact huv hv.symm
  · exact hvw hv

theorem cliqueMinusEdge_iff_unique_pair (H : SimpleGraph W) :
    CliqueMinusEdge H ↔ independentCount H 2 = 1 := by
  constructor
  · rintro ⟨u, v, huv, hAdj⟩
    have he : (independentSets H).filter (fun S => S.card = 2) = {{u, v}} := by
      ext S
      simp only [Finset.mem_filter, mem_independentSets, Finset.mem_singleton]
      constructor
      · rintro ⟨hS, hc⟩
        obtain ⟨w, z, hwz, rfl⟩ := Finset.card_eq_two.mp hc
        have h := (independent_pair H w z).mp hS
        rw [hAdj w z, not_and] at h
        have hp := not_not.mp (h hwz)
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Finset.pair_comm _ _
      · rintro rfl
        exact ⟨(independent_pair H u v).mpr (by simp [hAdj]), Finset.card_pair huv⟩
    unfold independentCount
    rw [he, Finset.card_singleton]
  · intro h₂
    obtain ⟨S, hS⟩ := Finset.card_eq_one.mp h₂
    have hm : S ∈ (independentSets H).filter (fun T => T.card = 2) := by rw [hS]; simp
    obtain ⟨hI, hc⟩ := Finset.mem_filter.mp hm
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc
    refine ⟨u, v, huv, ?_⟩
    intro w z
    have hnonadj : ¬H.Adj u v := (independent_pair H u v).mp ((mem_independentSets _ _).mp hI)
    constructor
    · intro hwz
      refine ⟨H.ne_of_adj hwz, ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hnonadj hwz
      · exact hnonadj hwz.symm
    · rintro ⟨hwz, hpair⟩
      by_contra h
      have hm' : ({w, z} : Finset W) ∈ (independentSets H).filter (fun T => T.card = 2) :=
        Finset.mem_filter.mpr ⟨(mem_independentSets _ _).mpr ((independent_pair H w z).mpr h),
          Finset.card_pair hwz⟩
      rw [hS, Finset.mem_singleton] at hm'
      have hw : w = u ∨ w = v := by have := Finset.mem_insert_self w {z}; rw [hm'] at this; simpa using this
      have hz : z = u ∨ z = v := by
        have hz' : z ∈ ({w, z} : Finset W) := by simp
        rw [hm'] at hz'
        simpa using hz'
      rcases hw with rfl | rfl <;> rcases hz with rfl | rfl
      · exact hwz rfl
      · exact hpair (Or.inl ⟨rfl, rfl⟩)
      · exact hpair (Or.inr ⟨rfl, rfl⟩)
      · exact hwz rfl

theorem unique_pair_polynomial (H : SimpleGraph W) (h₂ : independentCount H 2 = 1) :
    independencePolynomial H = symmetricQuadratic (Fintype.card W : ℝ) := by
  ext k
  rw [independencePolynomial_coeff, symmetricQuadratic]
  by_cases hk0 : k = 0
  · subst k
    simp [independentCount_zero, coeff_one]
  by_cases hk1 : k = 1
  · subst k
    simp [independentCount_one, coeff_one]
  by_cases hk2 : k = 2
  · subst k
    simp [h₂, coeff_one]
  · have he : independentCount H k = 0 := by
      unfold independentCount
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨hS, hc⟩ := Finset.mem_filter.mp hS
      have hb := independent_card_le_two_of_unique_pair H h₂ ((mem_independentSets _ _).mp hS)
      omega
    simp [he, hk0, Ne.symm hk1, hk2, coeff_one, coeff_X]

theorem unique_pair_order (H : SimpleGraph W) (h₂ : independentCount H 2 = 1) :
    2 ≤ Fintype.card W := by
  have hn : ((independentSets H).filter (fun S => S.card = 2)).Nonempty :=
    Finset.card_pos.mp (by change 0 < independentCount H 2; omega)
  obtain ⟨S, hS⟩ := hn
  have hc := (Finset.mem_filter.mp hS).2
  rw [← hc]
  exact Finset.card_le_univ S

theorem corona_unimodal_cliqueMinusEdge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (hH : CliqueMinusEdge H) :
    UnimodalAt (fun k => (independentCount (corona G H) k : ℝ)) (Fintype.card V) := by
  have h₂ := (cliqueMinusEdge_iff_unique_pair H).mp hH
  apply corona_counts_unimodal_of_polynomial G H (r := (Fintype.card W : ℝ))
    (by exact_mod_cast (show 1 ≤ Fintype.card W by have := unique_pair_order H h₂; omega))
  exact unique_pair_polynomial H h₂

end ResearchMain.Corona
