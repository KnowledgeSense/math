import MainTheorems.Domination.Powers
import MainTheorems.Tuza.CoChain
import MainTheorems.Tuza.CompleteInequality

namespace ResearchMain.PathCycleTuza

open Tuza

abbrev pathPower := Domination.pathPower
abbrev cyclePower := Domination.cyclePower

instance (n k : ℕ) : DecidableRel (pathPower n k).Adj := by
  intro x y
  change Decidable (x ≠ y ∧ Nat.dist x.val y.val ≤ k)
  infer_instance

instance (n k : ℕ) : DecidableRel (cyclePower n k).Adj := by
  intro x y
  change Decidable (x ≠ y ∧ (Nat.dist x.val y.val ≤ k ∨ n - Nat.dist x.val y.val ≤ k))
  infer_instance

theorem pathPower_short_isCoChain (n k : ℕ) (hn : n ≤ 2 * k + 2) :
    IsCoChain (pathPower n k) := by
  let S : Set (Fin n) := {i | i.val ≤ k}
  refine ⟨S, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    change x.val ≤ k at hx
    change y.val ≤ k at hy
    refine ⟨hxy, ?_⟩
    unfold Nat.dist
    omega
  · intro x hx y hy hxy
    change ¬x.val ≤ k at hx
    change ¬y.val ≤ k at hy
    refine ⟨hxy, ?_⟩
    have hxn := x.isLt
    have hyn := y.isLt
    unfold Nat.dist
    omega
  · intro x hx y hy
    change x.val ≤ k at hx
    change y.val ≤ k at hy
    rcases le_total x.val y.val with hxy | hyx
    · left
      intro w hw hAdj
      change ¬w.val ≤ k at hw
      obtain ⟨h₁, h₂⟩ := hAdj
      refine ⟨?_, ?_⟩
      · intro he
        have he' := congrArg Fin.val he
        omega
      · unfold Nat.dist at h₂ ⊢
        omega
    · right
      intro w hw hAdj
      change ¬w.val ≤ k at hw
      obtain ⟨h₁, h₂⟩ := hAdj
      refine ⟨?_, ?_⟩
      · intro he
        have he' := congrArg Fin.val he
        omega
      · unfold Nat.dist at h₂ ⊢
        omega

theorem pathPower_complete (n k : ℕ) (hn : n ≤ k + 1) :
    pathPower n k = ⊤ := by
  ext x y
  change (x ≠ y ∧ Nat.dist x.val y.val ≤ k) ↔ x ≠ y
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  have hx := x.isLt
  have hy := y.isLt
  unfold Nat.dist
  omega

theorem cyclePower_complete (n k : ℕ) (hn : n ≤ 2 * k + 1) :
    cyclePower n k = ⊤ := by
  ext x y
  change (x ≠ y ∧ (Nat.dist x.val y.val ≤ k ∨ n - Nat.dist x.val y.val ≤ k)) ↔ x ≠ y
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  omega

theorem triangleFree_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : ∀ t : Finset V, ¬G.IsNClique 3 t) : Inequality G := by
  have hc : Cover G ∅ := ⟨by simp, fun t ht => False.elim (h t ht)⟩
  have hn := number_le_cover hc
  have hz : coverNumber G = 0 := by simpa using hn
  unfold Inequality
  rw [hz]
  exact Nat.zero_le _

theorem bottom_inequality (V : Type*) [Fintype V] [DecidableEq V] :
    Inequality (⊥ : SimpleGraph V) := by
  apply triangleFree_inequality
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := (⊥ : SimpleGraph V).is3Clique_iff.mp ht
  exact hab

theorem pathPower_zero (n : ℕ) : pathPower n 0 = ⊥ := by
  ext x y
  change (x ≠ y ∧ Nat.dist x.val y.val ≤ 0) ↔ False
  constructor
  · rintro ⟨hne, hd⟩
    exact hne (Fin.ext (Nat.eq_of_dist_eq_zero (Nat.le_zero.mp hd)))
  · exact False.elim

theorem cyclePower_zero (n : ℕ) : cyclePower n 0 = ⊥ := by
  ext x y
  change (x ≠ y ∧ (Nat.dist x.val y.val ≤ 0 ∨ n - Nat.dist x.val y.val ≤ 0)) ↔ False
  have hx := x.isLt
  have hy := y.isLt
  have hdist : Nat.dist x.val y.val < n := by unfold Nat.dist; omega
  constructor
  · rintro ⟨hne, hd | hd⟩
    · exact hne (Fin.ext (Nat.eq_of_dist_eq_zero (Nat.le_zero.mp hd)))
    · have hz := Nat.le_zero.mp hd
      have hn := Nat.sub_eq_zero_iff_le.mp hz
      omega
  · exact False.elim

theorem pathPower_one_triangleFree (n : ℕ) :
    ∀ t : Finset (Fin n), ¬(pathPower n 1).IsNClique 3 t := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := (pathPower n 1).is3Clique_iff.mp ht
  have h₁ : a.val ≠ b.val := (not_congr Fin.ext_iff).mp hab.ne
  have h₂ : a.val ≠ c.val := (not_congr Fin.ext_iff).mp hac.ne
  have h₃ : b.val ≠ c.val := (not_congr Fin.ext_iff).mp hbc.ne
  have hd₁ := hab.2
  have hd₂ := hac.2
  have hd₃ := hbc.2
  unfold Nat.dist at hd₁ hd₂ hd₃
  omega

theorem cyclePower_one_triangleFree (n : ℕ) (hn : 4 ≤ n) :
    ∀ t : Finset (Fin n), ¬(cyclePower n 1).IsNClique 3 t := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := (cyclePower n 1).is3Clique_iff.mp ht
  have h₁ : a.val ≠ b.val := (not_congr Fin.ext_iff).mp hab.ne
  have h₂ : a.val ≠ c.val := (not_congr Fin.ext_iff).mp hac.ne
  have h₃ : b.val ≠ c.val := (not_congr Fin.ext_iff).mp hbc.ne
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd₁ := hab.2
  have hd₂ := hac.2
  have hd₃ := hbc.2
  unfold Nat.dist at hd₁ hd₂ hd₃
  omega

end ResearchMain.PathCycleTuza
