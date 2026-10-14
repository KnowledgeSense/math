import MainTheorems.Domination.Powers

namespace ResearchMain.Domination

theorem chain_covers (k ℓ : ℕ) (p : Fin (k + 1) → ℕ)
    (hgaps : ∀ i : Fin k, p i.succ ≤ p i.castSucc + 2 * ℓ + 1)
    (x : ℕ) (hfirst : p 0 ≤ x + ℓ) (hlast : x ≤ p (Fin.last k) + ℓ) :
    ∃ j, p j ≤ x + ℓ ∧ x ≤ p j + ℓ := by
  induction k with
  | zero =>
    exact ⟨0, hfirst, hlast⟩
  | succ k ih =>
    let q : Fin (k + 1) → ℕ := fun i => p i.castSucc
    have hq : ∀ i : Fin k, q i.succ ≤ q i.castSucc + 2 * ℓ + 1 := by
      intro i
      exact hgaps i.castSucc
    by_cases hx : x ≤ q (Fin.last k) + ℓ
    · obtain ⟨j, hj⟩ := ih q hq hfirst hx
      exact ⟨j.castSucc, hj⟩
    · refine ⟨Fin.last (k + 1), ?_, hlast⟩
      have hgap := hgaps (Fin.last k)
      change p (Fin.last (k + 1)) ≤ q (Fin.last k) + 2 * ℓ + 1 at hgap
      omega

theorem path_gap_criterion {n k ℓ : ℕ} (p : Fin (k + 1) → Fin n)
    (hp : StrictMono p) :
    Dominates (pathPower n ℓ) (Finset.univ.image p) ↔
      (p 0).val ≤ ℓ ∧ n - 1 ≤ (p (Fin.last k)).val + ℓ ∧
        ∀ i : Fin k, (p i.succ).val ≤ (p i.castSucc).val + 2 * ℓ + 1 := by
  rw [dominates_pathPower_image]
  constructor
  · intro hdom
    have hn : 0 < n := by have := (p 0).isLt; omega
    have hfirst : (p 0).val ≤ ℓ := by
      obtain ⟨j, hj, _⟩ := hdom ⟨0, hn⟩
      dsimp only at hj
      have hmin := hp.monotone (Fin.zero_le j)
      change (p 0).val ≤ (p j).val at hmin
      omega
    have hlast : n - 1 ≤ (p (Fin.last k)).val + ℓ := by
      obtain ⟨j, _, hj⟩ := hdom ⟨n - 1, by omega⟩
      dsimp only at hj
      have hmax := hp.monotone (Fin.le_last j)
      change (p j).val ≤ (p (Fin.last k)).val at hmax
      omega
    refine ⟨hfirst, hlast, ?_⟩
    intro i
    by_contra hgap
    have hx : (p i.castSucc).val + ℓ + 1 < n := by
      have := (p i.succ).isLt
      omega
    obtain ⟨j, hjlo, hjhi⟩ := hdom ⟨(p i.castSucc).val + ℓ + 1, hx⟩
    dsimp only at hjlo hjhi
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
  · rintro ⟨hfirst, hlast, hgaps⟩ v
    exact chain_covers k ℓ (fun j => (p j).val) hgaps v.val (by omega)
      (by have := v.isLt; omega)

end ResearchMain.Domination
