import ASR312.GappedCompletionASM

namespace ASR312

noncomputable def columnSupport {r k : ℕ} (A : Rectangle r k) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun j => ∃ i, A i j = .plus)

theorem mem_columnSupport {r k : ℕ} (A : Rectangle r k) (j : Fin k) :
    j ∈ columnSupport A ↔ ∃ i, A i j = .plus := by classical simp [columnSupport]

def SparseDescending {r k : ℕ} (A : Rectangle r k) : Prop :=
  (∀ i j, A i j ≠ .minus) ∧
  (∀ i j u, A i j = .plus → A i u = .plus → j = u) ∧
  (∀ i t j, A i j = .plus → A t j = .plus → i = t) ∧
  (∀ i t j u, i < t → A i j = .plus → A t u = .plus → u < j)

theorem SparseDescending.nonzero_plus {r k : ℕ} {A : Rectangle r k} (hA : SparseDescending A)
    {i : Fin r} {j : Fin k} (h : A i j ≠ .zero) : A i j = .plus := by
  have hm := hA.1 i j
  cases hx : A i j <;> simp_all

theorem SparseDescending.support_rank {r k : ℕ} {A : Rectangle r k} (hA : SparseDescending A)
    (i : Fin r) (j : Fin k) (hij : A i j = .plus) :
    ((rowSupport A).filter (· < i)).card = ((columnSupport A).filter (j < ·)).card := by
  classical
  have hex (t : Fin r) (ht : t ∈ (rowSupport A).filter (· < i)) : ∃ u, A t u = .plus := by
    obtain ⟨u,hu⟩ := (mem_rowSupport A t).mp (Finset.mem_filter.mp ht).1
    exact ⟨u,hA.nonzero_plus hu⟩
  let f := fun t ht => Classical.choose (hex t ht)
  have hf (t) (ht) : A t (f t ht) = .plus := Classical.choose_spec (hex t ht)
  apply Finset.card_bij f
  · intro t ht
    rw [Finset.mem_filter,mem_columnSupport]
    exact ⟨⟨t,hf t ht⟩,hA.2.2.2 t i _ j (Finset.mem_filter.mp ht).2 (hf t ht) hij⟩
  · intro t ht u hu htu
    apply hA.2.2.1 t u (f t ht) (hf t ht)
    rw [htu]
    exact hf u hu
  · intro u hu
    obtain ⟨hum,hju⟩ := Finset.mem_filter.mp hu
    obtain ⟨t,ht⟩ := (mem_columnSupport A u).mp hum
    have hti : t < i := by
      rcases lt_trichotomy t i with h | h | h
      · exact h
      · subst t
        exact False.elim ((ne_of_lt hju) (hA.2.1 i j u hij ht))
      · exact False.elim ((not_lt_of_ge (hA.2.2.2 i t j u h hij ht).le) hju)
    have htm : t ∈ (rowSupport A).filter (· < i) := by
      rw [Finset.mem_filter,mem_rowSupport]
      exact ⟨⟨u,by rw [ht]; decide⟩,hti⟩
    exact ⟨t,htm,hA.2.1 t _ u (hf t htm) ht⟩

theorem finset_upper_rank_injective {k : ℕ} (s : Finset (Fin k)) {j u : Fin k}
    (hj : j ∈ s) (hu : u ∈ s)
    (he : (s.filter (j < ·)).card = (s.filter (u < ·)).card) : j = u := by
  classical
  have mono {j u : Fin k} (hu : u ∈ s) (hju : j < u) :
      (s.filter (u < ·)).card < (s.filter (j < ·)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro x hx
      obtain ⟨hx,hux⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hx,lt_trans hju hux⟩
    · intro h
      have hum : u ∈ s.filter (j < ·) := Finset.mem_filter.mpr ⟨hu,hju⟩
      rw [← h] at hum
      exact (lt_irrefl u) (Finset.mem_filter.mp hum).2
  rcases lt_trichotomy j u with h | h | h
  · have hh := mono hu h; omega
  · exact h
  · have hh := mono hj h; omega

theorem sparseDescending_eq_of_supports {r k : ℕ} (A B : Rectangle r k)
    (ha : SparseDescending A) (hb : SparseDescending B)
    (hr : rowSupport A = rowSupport B) (hc : columnSupport A = columnSupport B) : A = B := by
  have hp (i : Fin r) (j : Fin k) (hij : A i j = .plus) : B i j = .plus := by
    have him : i ∈ rowSupport B := by
      rw [← hr,mem_rowSupport]
      exact ⟨j,by rw [hij]; decide⟩
    obtain ⟨u,hu⟩ := (mem_rowSupport B i).mp him
    have hip := hb.nonzero_plus hu
    have hra := ha.support_rank i j hij
    have hrb := hb.support_rank i u hip
    rw [hr,hc] at hra
    have hj : j ∈ columnSupport B := by rw [← hc,mem_columnSupport]; exact ⟨i,hij⟩
    have hu : u ∈ columnSupport B := (mem_columnSupport B u).mpr ⟨i,hip⟩
    have hju := finset_upper_rank_injective (columnSupport B) hj hu (hra.symm.trans hrb)
    simpa [hju] using hip
  funext i j
  by_cases hij : A i j = .plus
  · rw [hij,hp i j hij]
  · have haz : A i j = .zero := by
      by_contra h
      exact hij (ha.nonzero_plus h)
    rw [haz]
    by_contra hn
    have hbp := hb.nonzero_plus (Ne.symm hn)
    have him : i ∈ rowSupport A := by
      rw [hr,mem_rowSupport]
      exact ⟨j,by rw [hbp]; decide⟩
    obtain ⟨u,hu⟩ := (mem_rowSupport A i).mp him
    have hap := ha.nonzero_plus hu
    have hbp' := hp i u hap
    have hju := hb.2.1 i j u hbp hbp'
    exact hij (hju ▸ hap)

end ASR312
