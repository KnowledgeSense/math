import MeanMaximumForests.ForestOrderBound
import MeanMaximumForests.IndependenceCoefficients

namespace MeanMaximumForests
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The independent `k`-subsets of a fixed finite vertex set. -/
noncomputable def independentSetsOfSize (s : Finset V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact (independentSetsWithin G s).filter (fun J => J.card = k)

omit [DecidableEq V] in
@[simp] theorem mem_independentSetsOfSize {s J : Finset V} {k : ℕ} :
    J ∈ independentSetsOfSize G s k ↔ J ⊆ s ∧ Independent G J ∧ J.card = k := by
  classical
  simp only [independentSetsOfSize, mem_filter, mem_independentSetsWithin]
  tauto

/-- Vertices which may be adjoined to the current independent set. -/
noncomputable def extensions (s J : Finset V) : Finset V := by
  classical
  exact s.filter (fun v => v ∉ J ∧ ∀ u ∈ J, ¬ G.Adj v u)

@[simp] theorem mem_extensions {s J : Finset V} {v : V} :
    v ∈ extensions G s J ↔ v ∈ s ∧ v ∉ J ∧ ∀ u ∈ J, ¬ G.Adj v u := by
  classical
  simp [extensions]

/-- Nested independent sets may be counted either by extension or by deletion. -/
theorem extension_pairs_card (s : Finset V) (k : ℕ) :
    ((independentSetsOfSize G s k).sigma (extensions G s)).card =
      ((independentSetsOfSize G s (k + 1)).sigma (fun J => J)).card := by
  classical
  apply card_bij (fun p _ => ⟨insert p.2 p.1, p.2⟩)
  · intro p hp
    obtain ⟨hJ, hv⟩ := mem_sigma.mp hp
    obtain ⟨hJs, hJi, hJk⟩ := (mem_independentSetsOfSize G).mp hJ
    obtain ⟨hvs, hvJ, hvI⟩ := (mem_extensions G).mp hv
    apply mem_sigma.mpr
    refine ⟨(mem_independentSetsOfSize G).mpr ⟨insert_subset hvs hJs,
      (independent_insert G).mpr ⟨hJi, hvI⟩, ?_⟩, mem_insert_self _ _⟩
    rw [card_insert_of_notMem hvJ, hJk]
  · rintro ⟨J, v⟩ hp ⟨K, w⟩ hq he
    have hvw : v = w := congrArg (fun p : Σ _ : Finset V, V => p.2) he
    subst w
    have hJ : v ∉ J := ((mem_extensions G).mp (mem_sigma.mp hp).2).2.1
    have hK : v ∉ K := ((mem_extensions G).mp (mem_sigma.mp hq).2).2.1
    have hi : insert v J = insert v K := congrArg (fun p : Σ _ : Finset V, V => p.1) he
    have hJK : J = K := by
      have hh := congrArg (fun t : Finset V => t.erase v) hi
      simpa only [erase_insert hJ, erase_insert hK] using hh
    cases hJK
    rfl
  · rintro ⟨K, v⟩ hq
    obtain ⟨hK, hvK⟩ := mem_sigma.mp hq
    obtain ⟨hKs, hKi, hKk⟩ := (mem_independentSetsOfSize G).mp hK
    refine ⟨⟨K.erase v, v⟩, mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
    · apply (mem_independentSetsOfSize G).mpr
      refine ⟨(erase_subset v K).trans hKs, hKi.mono G (erase_subset v K), ?_⟩
      rw [card_erase_of_mem hvK, hKk]
      omega
    · apply (mem_extensions G).mpr
      exact ⟨hKs hvK, notMem_erase _ _, fun u hu => hKi v hvK u (mem_of_mem_erase hu)⟩
    · simp only [insert_erase hvK]

/-- The exact coefficient/extension identity used in the paper. -/
theorem coefficient_extension_identity (s : Finset V) (k : ℕ) :
    (k + 1) * independentSetCoefficient G s (k + 1) =
      ∑ J ∈ independentSetsOfSize G s k, (extensions G s J).card := by
  have h := extension_pairs_card G s k
  rw [card_sigma, card_sigma] at h
  have hs : (∑ J ∈ independentSetsOfSize G s (k + 1), J.card) =
      (independentSetsOfSize G s (k + 1)).card * (k + 1) := by
    calc _ = ∑ _J ∈ independentSetsOfSize G s (k + 1), (k + 1) :=
           sum_congr rfl (fun J hJ => ((mem_independentSetsOfSize G).mp hJ).2.2)
         _ = _ := by simp
  rw [hs] at h
  simpa only [independentSetCoefficient, independentSetsOfSize, Nat.mul_comm] using h.symm

end MeanMaximumForests
