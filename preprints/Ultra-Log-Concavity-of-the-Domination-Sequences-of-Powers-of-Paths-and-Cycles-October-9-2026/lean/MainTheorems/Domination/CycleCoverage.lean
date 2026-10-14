import MainTheorems.Domination.PathCoverage

namespace ResearchMain.Domination

theorem no_wrap_near_interior {n ℓ x a : ℕ} (ha : a < n)
    (hxlo : ℓ ≤ x) (hxhi : x + ℓ < n) :
    ℓ < n - Nat.dist a x := by
  unfold Nat.dist
  omega

theorem cycle_gap_criterion {n k ℓ : ℕ} (p : Fin (k + 1) → Fin n)
    (hp : StrictMono p) :
    Dominates (cyclePower n ℓ) (Finset.univ.image p) ↔
      n + (p 0).val ≤ (p (Fin.last k)).val + 2 * ℓ + 1 ∧
        ∀ i : Fin k, (p i.succ).val ≤ (p i.castSucc).val + 2 * ℓ + 1 := by
  rw [dominates_cyclePower_image]
  have hmin : ∀ j, (p 0).val ≤ (p j).val := by
    intro j
    exact hp.monotone (Fin.zero_le j)
  have hmax : ∀ j, (p j).val ≤ (p (Fin.last k)).val := by
    intro j
    exact hp.monotone (Fin.le_last j)
  constructor
  · intro hdom
    constructor
    · by_contra hwrap
      let u := (p (Fin.last k)).val + ℓ + 1
      have hfirst := (p 0).isLt
      have hlast := (p (Fin.last k)).isLt
      by_cases hun : u < n
      · obtain ⟨j, hj⟩ := hdom ⟨u, hun⟩
        dsimp only at hj
        have hjmin := hmin j
        have hjmax := hmax j
        unfold Nat.dist at hj
        dsimp only [u] at *
        omega
      · have hxn : u - n < n := by dsimp only [u] at *; omega
        obtain ⟨j, hj⟩ := hdom ⟨u - n, hxn⟩
        dsimp only at hj
        have hjmin := hmin j
        have hjmax := hmax j
        unfold Nat.dist at hj
        dsimp only [u] at *
        omega
    · intro i
      by_contra hgap
      have hx : (p i.castSucc).val + ℓ + 1 < n := by
        have := (p i.succ).isLt
        omega
      obtain ⟨j, hj⟩ := hdom ⟨(p i.castSucc).val + ℓ + 1, hx⟩
      dsimp only at hj
      have hnwrap := no_wrap_near_interior (p j).isLt
        (by omega : ℓ ≤ (p i.castSucc).val + ℓ + 1)
        (by have := (p i.succ).isLt; omega)
      have hnear : Nat.dist (p j).val ((p i.castSucc).val + ℓ + 1) ≤ ℓ := by
        rcases hj with hj | hj
        · exact hj
        · omega
      obtain ⟨hjlo, hjhi⟩ := (nat_distance_bound _ _ _).mp hnear
      by_cases hji : j ≤ i.castSucc
      · have hle := hp.monotone hji
        change (p j).val ≤ (p i.castSucc).val at hle
        omega
      · have hij : i.succ ≤ j := by
          change i.val + 1 ≤ j.val
          change ¬ j.val ≤ i.val at hji
          omega
        have hle := hp.monotone hij
        change (p i.succ).val ≤ (p j).val at hle
        omega
  · rintro ⟨hwrap, hgaps⟩ v
    have hv := v.isLt
    by_cases hfirst : (p 0).val ≤ v.val + ℓ
    · by_cases hlast : v.val ≤ (p (Fin.last k)).val + ℓ
      · obtain ⟨j, hj⟩ := chain_covers k ℓ (fun j => (p j).val) hgaps v.val hfirst hlast
        exact ⟨j, Or.inl ((nat_distance_bound _ _ _).mpr hj)⟩
      · refine ⟨0, Or.inr ?_⟩
        have h0last := hmin (Fin.last k)
        unfold Nat.dist
        omega
    · refine ⟨Fin.last k, Or.inr ?_⟩
      have h0last := hmin (Fin.last k)
      unfold Nat.dist
      omega

end ResearchMain.Domination
