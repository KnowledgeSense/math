import MainTheorems.Domination.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace ResearchMain.Domination

def pathPower (n ℓ : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ Nat.dist u.val v.val ≤ ℓ
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa only [Nat.dist_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def cyclePower (n ℓ : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (Nat.dist u.val v.val ≤ ℓ ∨ n - Nat.dist u.val v.val ≤ ℓ)
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa only [Nat.dist_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem pathPower_closed {n ℓ : ℕ} (u v : Fin n) :
    u = v ∨ (pathPower n ℓ).Adj u v ↔ Nat.dist u.val v.val ≤ ℓ := by
  constructor
  · rintro (rfl | h)
    · simp
    · exact h.2
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ⟨huv, h⟩

theorem cyclePower_closed {n ℓ : ℕ} (u v : Fin n) :
    u = v ∨ (cyclePower n ℓ).Adj u v ↔
      Nat.dist u.val v.val ≤ ℓ ∨ n - Nat.dist u.val v.val ≤ ℓ := by
  constructor
  · rintro (rfl | h)
    · exact Or.inl (by simp)
    · exact h.2
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ⟨huv, h⟩

theorem dominates_pathPower {n ℓ : ℕ} (S : Finset (Fin n)) :
    Dominates (pathPower n ℓ) S ↔
      ∀ v : Fin n, ∃ u ∈ S, Nat.dist u.val v.val ≤ ℓ := by
  simp only [Dominates, pathPower_closed]

theorem dominates_cyclePower {n ℓ : ℕ} (S : Finset (Fin n)) :
    Dominates (cyclePower n ℓ) S ↔ ∀ v : Fin n, ∃ u ∈ S,
      Nat.dist u.val v.val ≤ ℓ ∨ n - Nat.dist u.val v.val ≤ ℓ := by
  simp only [Dominates, cyclePower_closed]

theorem nat_distance_bound (a b ℓ : ℕ) :
    Nat.dist a b ≤ ℓ ↔ a ≤ b + ℓ ∧ b ≤ a + ℓ := by
  unfold Nat.dist
  omega

theorem dominates_pathPower_image {n k ℓ : ℕ} (p : Fin k → Fin n) :
    Dominates (pathPower n ℓ) (Finset.univ.image p) ↔
      ∀ v : Fin n, ∃ j : Fin k, (p j).val ≤ v.val + ℓ ∧ v.val ≤ (p j).val + ℓ := by
  rw [dominates_pathPower]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, nat_distance_bound]
  constructor
  · intro h v
    obtain ⟨u, ⟨j, rfl⟩, hj⟩ := h v
    exact ⟨j, hj⟩
  · intro h v
    obtain ⟨j, hj⟩ := h v
    exact ⟨p j, ⟨j, rfl⟩, hj⟩

theorem pathPower_one (n : ℕ) : pathPower n 1 = SimpleGraph.pathGraph n := by
  ext u v
  rw [SimpleGraph.pathGraph_adj]
  change (u ≠ v ∧ Nat.dist u.val v.val ≤ 1) ↔ _
  rw [nat_distance_bound]
  have hne : u ≠ v ↔ u.val ≠ v.val := not_congr Fin.ext_iff
  rw [hne]
  omega

theorem dominates_cyclePower_image {n k ℓ : ℕ} (p : Fin k → Fin n) :
    Dominates (cyclePower n ℓ) (Finset.univ.image p) ↔
      ∀ v : Fin n, ∃ j : Fin k, Nat.dist (p j).val v.val ≤ ℓ ∨
        n - Nat.dist (p j).val v.val ≤ ℓ := by
  rw [dominates_cyclePower]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h v
    obtain ⟨u, ⟨j, rfl⟩, hj⟩ := h v
    exact ⟨j, hj⟩
  · intro h v
    obtain ⟨j, hj⟩ := h v
    exact ⟨p j, ⟨j, rfl⟩, hj⟩

end ResearchMain.Domination
