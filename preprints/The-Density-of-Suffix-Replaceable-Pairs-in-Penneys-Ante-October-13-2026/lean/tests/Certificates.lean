import PenneyDensity

open PenneyDensity Filter
open scoped Topology

example : ∃ ρ : ℝ,
    Tendsto density atTop (𝓝 ρ) ∧ Tendsto distinctDensity atTop (𝓝 ρ) ∧
    Tendsto distinctNormalizedDensity atTop (𝓝 ρ) ∧
    positiveLowerBound≤ρ ∧ 0<ρ ∧ ρ≤1 :=
  suffix_replacement_positive_density

example (v : Word) : StoppedLanguage v v=∅ := stoppedLanguage_diagonal v

example (v w : Word) (hv : v.length=1) (hw : w.length=1) : PropertyR v w := by
  by_cases he : v=w
  · subst w; exact diagonal_propertyR v
  · have hn : v≠[] := by intro hh; simp only [hh,List.length_nil] at hv; omega
    rw [propertyR_iff_suffix_cover (hv.trans hw.symm) he hn]
    have hempty (t x : Word) (hx : x∈forbidden v w t) : False := by
      obtain ⟨a,ha,k,⟨hk,hka,_⟩,_⟩ := hx
      rcases ha with rfl | rfl <;> omega
    exact ⟨fun x hx => False.elim (hempty v x hx),fun x hx => False.elim (hempty w x hx)⟩

example : 0<positiveLowerBound := positiveLowerBound_pos

example : Nat.card {f : Fin 10 → Bool // EqualBlocks f 0 1 8 (by omega) (by omega)}=4 := by
  classical
  rw [Nat.card_eq_fintype_card]
  simpa using card_equal_blocks (N := 10) (i := 0) (j := 1) (m := 8) (by omega) (by omega)
