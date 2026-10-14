import GenericValueSemigroups.StructuralRank
import GenericValueSemigroups.JetRanks

namespace GenericValueSemigroups
open scoped Classical

noncomputable def greedyPrefixCount (w : ℕ → ℕ) (p L : ℕ) : ℕ :=
  ((Finset.range p).filter (fun j => greedy w j<L)).card

theorem greedyPrefixCount_le (w : ℕ → ℕ) (p L : ℕ) : greedyPrefixCount w p L≤p := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem greedy_lt_of_lt_prefixCount (w : ℕ → ℕ) (p L j : ℕ)
    (hj : j<greedyPrefixCount w p L) : greedy w j<L := by
  by_contra h
  have hsub : (Finset.range p).filter (fun k => greedy w k<L) ⊆ Finset.range j := by
    intro k hk
    have hg := (Finset.mem_filter.mp hk).2
    apply Finset.mem_range.mpr
    by_contra hkj
    have hh := (greedy_strictMono w).monotone (by omega : j≤k)
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range] at hc
  change greedyPrefixCount w p L≤j at hc
  omega

/-- Nonvanishing greedy minors attain the structural rank bound. -/
theorem rank_eq_greedy_count {K : Type*} [Field K] {L p : ℕ}
    (A : Matrix (Fin L) (Fin p) K) (w : ℕ → ℕ) (hw : Monotone w)
    (hz : ∀ a b, a.val<w b.val → A a b=0)
    (hm : ∀ (q : ℕ) (hq : q≤greedyPrefixCount w p L),
      Matrix.det (A.submatrix
        (fun i : Fin q => (⟨greedy w i.val,
          greedy_lt_of_lt_prefixCount w p L i.val (lt_of_lt_of_le i.isLt hq)⟩ : Fin L))
        (fun i : Fin q => (⟨i.val,lt_of_lt_of_le i.isLt
          (hq.trans (greedyPrefixCount_le w p L))⟩ : Fin p))) ≠ 0) :
    A.rank=greedyPrefixCount w p L := by
  apply le_antisymm (rank_le_greedy_count A w hw hz)
  let q := greedyPrefixCount w p L
  let rows : Fin q → Fin L := fun i =>
    ⟨greedy w i.val,greedy_lt_of_lt_prefixCount w p L i.val i.isLt⟩
  let cols : Fin q → Fin p := fun i =>
    ⟨i.val,lt_of_lt_of_le i.isLt (greedyPrefixCount_le w p L)⟩
  have he : (A.submatrix rows cols).rank=q := by
    simpa using Matrix.rank_of_det_ne_zero (hm q le_rfl)
  change q ≤ A.rank
  rw [← he]
  exact Matrix.rank_submatrix_le A rows cols

theorem greedyPrefixCount_step (w : ℕ → ℕ) (p n : ℕ) :
    greedyPrefixCount w p (n+1) = greedyPrefixCount w p n +
      if ∃ j<p, greedy w j=n then 1 else 0 := by
  let A := (Finset.range p).filter (fun j => greedy w j<n)
  let B := (Finset.range p).filter (fun j => greedy w j=n)
  have he : (Finset.range p).filter (fun j => greedy w j<n+1)=A∪B := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, A, B]
    omega
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro j ha hb
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    omega
  have hb : B.card=if ∃ j<p, greedy w j=n then 1 else 0 := by
    split_ifs with h
    · obtain ⟨j,hjp,hj⟩ := h
      have heq : B={j} := by
        ext k
        simp only [B, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨_,hk⟩
          exact (greedy_strictMono w).injective (hk.trans hj.symm)
        · rintro rfl; exact ⟨hjp,hj⟩
      simp [heq]
    · have heq : B=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        exact h ⟨j,Finset.mem_range.mp (Finset.mem_filter.mp hj).1,
          (Finset.mem_filter.mp hj).2⟩
      simp [heq]
  unfold greedyPrefixCount
  rw [he,Finset.card_union_of_disjoint hd,hb]

theorem greedyPrefixCount_step_iff (w : ℕ → ℕ) (p n : ℕ) :
    greedyPrefixCount w p (n+1)=greedyPrefixCount w p n+1 ↔
      ∃ j<p, greedy w j=n := by
  rw [greedyPrefixCount_step]
  split_ifs <;> simp_all

noncomputable def greedyMinor {p : ℕ} (f : Fin p → PowerSeries ℂ)
    (w : ℕ → ℕ) (q : ℕ) (hq : q≤p) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => PowerSeries.coeff (greedy w i.val) (f ⟨j.val,lt_of_lt_of_le j.isLt hq⟩)

theorem greedyPrefixCount_mono (w : ℕ → ℕ) (p : ℕ) {L N : ℕ} (hLN : L≤N) :
    greedyPrefixCount w p L≤greedyPrefixCount w p N := by
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
    lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hLN⟩

/-- The same finite list of nonzero minors determines all shorter prefix ranks. -/
theorem coefficient_rank_eq_greedy {p : ℕ} (f : Fin p → PowerSeries ℂ)
    (w : ℕ → ℕ) (hw : Monotone w) (hf : ∀ j, PowerSeries.order (f j)=w j.val)
    (N : ℕ) (hm : ∀ (q : ℕ) (hq : q≤greedyPrefixCount w p N),
      (greedyMinor f w q (hq.trans (greedyPrefixCount_le w p N))).det ≠ 0)
    (L : ℕ) (hL : L≤N) :
    (coefficientMatrix f L).rank=greedyPrefixCount w p L := by
  apply rank_eq_greedy_count _ w hw
  · intro a b hab
    apply PowerSeries.coeff_of_lt_order
    rw [hf]
    exact_mod_cast hab
  · intro q hq
    exact hm q (hq.trans (greedyPrefixCount_mono w p hL))

/-- In the actual finite series span, nonzero greedy minors identify all values below the cutoff. -/
theorem finite_span_values_of_greedy_minors {p : ℕ} (f : Fin p → PowerSeries ℂ)
    (w : ℕ → ℕ) (hw : Monotone w) (hf : ∀ j, PowerSeries.order (f j)=w j.val)
    (N : ℕ) (hm : ∀ (q : ℕ) (hq : q≤greedyPrefixCount w p N),
      (greedyMinor f w q (hq.trans (greedyPrefixCount_le w p N))).det ≠ 0)
    (n : ℕ) (hn : n<N) :
    (∃ c, PowerSeries.order (seriesCombination f c)=n) ↔ ∃ j<p, greedy w j=n := by
  rw [order_attained_iff_rank_step,
    coefficient_rank_eq_greedy f w hw hf N hm (n+1) (by omega),
    coefficient_rank_eq_greedy f w hw hf N hm n (by omega),
    greedyPrefixCount_step_iff]

end GenericValueSemigroups
