import ASR312.PaddedRowSupport
import Mathlib.Order.Interval.Finset.Fin

namespace ASR312

noncomputable def rowSupport {r k : ℕ} (A : Rectangle r k) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j, A i j ≠ .zero)

theorem mem_rowSupport {r k : ℕ} (A : Rectangle r k) (i : Fin r) :
    i ∈ rowSupport A ↔ ∃ j, A i j ≠ .zero := by
  classical
  simp [rowSupport]

theorem rowSupport_card {r k : ℕ} (A : Rectangle r k) : (rowSupport A).card = nonemptyRows A := rfl

theorem emptyFirstRow_nonzero_plus {r k : ℕ} (A : Rectangle (r+1) k)
    (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero) {i : Fin (r+1)} {j : Fin k}
    (h : A i j ≠ .zero) : A i j = .plus := by
  have hm := emptyFirstRow_no_minus A he hz i j
  cases hx : A i j with
  | minus => exact False.elim (hm hx)
  | zero => exact False.elim (h hx)
  | plus => rfl

theorem emptyFirstRow_plus_strictAnti {r k : ℕ} (A : Rectangle (r+1) k)
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero)
    {i t : Fin (r+1)} {j u : Fin k} (hit : i < t)
    (hij : A i j = .plus) (htu : A t u = .plus) : u < j := by
  rcases lt_trichotomy j u with h | h | h
  · exact False.elim (emptyFirstRow_descending A he hz i t j u hit h hij htu)
  · subst u
    exact False.elim ((ne_of_lt hit) (emptyFirstRow_col_plus_unique A ha he hz j hij htu))
  · exact h

theorem emptyFirstRow_rank {r k : ℕ} (A : Rectangle (r+1) k)
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero)
    (i : Fin (r+1)) (j : Fin k) (hij : A i j = .plus) :
    ((rowSupport A).filter (· < i)).card = k-1-j.val := by
  classical
  rw [← Fin.card_Ioi j]
  have hex (t : Fin (r+1)) (ht : t ∈ (rowSupport A).filter (· < i)) : ∃ u, A t u = .plus := by
    obtain ⟨u,hu⟩ := (mem_rowSupport A t).mp (Finset.mem_filter.mp ht).1
    exact ⟨u,emptyFirstRow_nonzero_plus A he hz hu⟩
  let f := fun t ht => Classical.choose (hex t ht)
  have hf (t) (ht) : A t (f t ht) = .plus := Classical.choose_spec (hex t ht)
  apply Finset.card_bij f
  · intro t ht
    exact Finset.mem_Ioi.mpr (emptyFirstRow_plus_strictAnti A ha he hz
      (Finset.mem_filter.mp ht).2 (hf t ht) hij)
  · intro t ht u hu htu
    apply emptyFirstRow_col_plus_unique A ha he hz (f t ht) (hf t ht)
    rw [htu]
    exact hf u hu
  · intro u hu
    have hju := Finset.mem_Ioi.mp hu
    obtain ⟨t,ht⟩ := emptyFirstRow_plus_upper_closed A he hz i j u hju hij
    have hti : t < i := by
      rcases lt_trichotomy t i with h | h | h
      · exact h
      · subst t
        have h := emptyFirstRow_row_plus_unique A ha he hz i hij ht
        exact False.elim ((ne_of_lt hju) h)
      · have h := emptyFirstRow_plus_strictAnti A ha he hz h hij ht
        exact False.elim ((not_lt_of_ge h.le) hju)
    have htm : t ∈ (rowSupport A).filter (· < i) := by
      rw [Finset.mem_filter,mem_rowSupport]
      exact ⟨⟨u,by rw [ht]; decide⟩,hti⟩
    exact ⟨t,htm,emptyFirstRow_row_plus_unique A ha he hz t (hf t htm) ht⟩

theorem emptyFirstRow_eq_of_rowSupport {r k : ℕ} (A B : Rectangle (r+1) k)
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero)
    (hb : IsASR B) (hbe : ExtendablyAvoids312 B) (hbz : ∀ j, B 0 j = .zero)
    (hs : rowSupport A = rowSupport B) : A = B := by
  have hp (i : Fin (r+1)) (j : Fin k) (hij : A i j = .plus) : B i j = .plus := by
    have him : i ∈ rowSupport B := by
      rw [← hs,mem_rowSupport]
      exact ⟨j,by rw [hij]; decide⟩
    obtain ⟨u,hu⟩ := (mem_rowSupport B i).mp him
    have hip := emptyFirstRow_nonzero_plus B hbe hbz hu
    have hra := emptyFirstRow_rank A ha he hz i j hij
    have hrb := emptyFirstRow_rank B hb hbe hbz i u hip
    rw [hs] at hra
    have hj := j.isLt
    have hu := u.isLt
    have hju : j = u := Fin.ext (by omega)
    simpa [hju] using hip
  funext i j
  by_cases hij : A i j = .plus
  · rw [hij,hp i j hij]
  · have haz : A i j = .zero := by
      by_contra h
      exact hij (emptyFirstRow_nonzero_plus A he hz h)
    rw [haz]
    by_contra hn
    have hbp := emptyFirstRow_nonzero_plus B hbe hbz (Ne.symm hn)
    have him : i ∈ rowSupport A := by
      rw [hs,mem_rowSupport]
      exact ⟨j,by rw [hbp]; decide⟩
    obtain ⟨u,hu⟩ := (mem_rowSupport A i).mp him
    have hap := emptyFirstRow_nonzero_plus A he hz hu
    have hbp' := hp i u hap
    have hju := emptyFirstRow_row_plus_unique B hb hbe hbz i hbp hbp'
    exact hij (hju ▸ hap)

end ASR312
