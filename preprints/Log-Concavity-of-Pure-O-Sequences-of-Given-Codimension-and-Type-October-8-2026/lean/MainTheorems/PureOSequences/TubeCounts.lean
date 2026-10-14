import MainTheorems.PureOSequences.HigherDimensions

namespace ResearchMain.PureOSequences

abbrev TubeCoordinates (k t : ℕ) := Fin (t + 3) × Fin 5 × Fin 5 × (Fin k → Fin 2)

def tubeWeight {k t : ℕ} (p : TubeCoordinates k t) : ℕ :=
  p.1.val + p.2.1.val + p.2.2.1.val + ∑ i, (p.2.2.2 i).val

noncomputable def tubeSection {k t : ℕ} (j : ℕ) (p : TubeCoordinates k t) : Monomial (4 + k) :=
  blockMonomial (higherDegree k t - j - tubeWeight p) p.1.val p.2.1.val p.2.2.1.val
    (fun i => (p.2.2.2 i).val)

theorem tubeWeight_bound {k t : ℕ} (p : TubeCoordinates k t) : tubeWeight p ≤ t + k + 10 := by
  have hsum : (∑ i, (p.2.2.2 i).val) ≤ k := by
    calc
      _ ≤ ∑ _ : Fin k, (1 : ℕ) := Finset.sum_le_sum (fun i _ => by
        have := (p.2.2.2 i).isLt
        omega)
      _ = k := by simp
  have h0 := p.1.isLt
  have h1 := p.2.1.isLt
  have h2 := p.2.2.1.isLt
  unfold tubeWeight
  omega

theorem tubeSection_degree {k t : ℕ} (j : ℕ) (p : TubeCoordinates k t)
    (hj : j ≤ k + 14) : totalDeg (tubeSection j p) = higherDegree k t - j := by
  have hw := tubeWeight_bound p
  simp only [tubeSection, degree_blockMonomial]
  unfold tubeWeight at hw ⊢
  unfold higherDegree
  omega

theorem tubeSection_mem {k t : ℕ} (j : ℕ) (p : TubeCoordinates k t)
    (ht : 2 ≤ t) (hlo : k + 12 ≤ j) (hhi : j ≤ k + 14) :
    tubeSection j p ∈ (generatedOrderIdeal (higherTubeGenerators k t)).carrier := by
  let q := p.1.val - 4
  have hq : q < t - 1 := by
    have := p.1.isLt
    dsimp [q]
    omega
  apply mem_generatedOrderIdeal_iff.mpr
  refine ⟨higherTube k t q, Finset.mem_image.mpr ⟨q, Finset.mem_range.mpr hq, rfl⟩, ?_⟩
  rw [higherTube, blockMonomial_le]
  simp only [tubeSection, blockMonomial_left, blockMonomial_right, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num
  have hweight := tubeWeight_bound p
  have hp0 := p.1.isLt
  have hp1 := p.2.1.isLt
  have hp2 := p.2.2.1.isLt
  have hqweight : q ≤ tubeWeight p := by
    unfold tubeWeight
    dsimp [q]
    omega
  refine ⟨?_, ?_, by omega, by omega, ?_⟩
  · unfold higherDegree
    omega
  · dsimp [q]
    omega
  · intro i
    have := (p.2.2.2 i).isLt
    omega

theorem tubeSection_injective {k t : ℕ} (j : ℕ) :
    Function.Injective (tubeSection (k := k) (t := t) j) := by
  intro p q heq
  apply Prod.ext
  · apply Fin.ext
    simpa [tubeSection] using congrArg (fun m => m (Fin.castAdd k 1)) heq
  · apply Prod.ext
    · apply Fin.ext
      simpa [tubeSection] using congrArg (fun m => m (Fin.castAdd k 2)) heq
    · apply Prod.ext
      · apply Fin.ext
        simpa [tubeSection] using congrArg (fun m => m (Fin.castAdd k 3)) heq
      · funext i
        apply Fin.ext
        simpa [tubeSection] using congrArg (fun m => m (Fin.natAdd 4 i)) heq

theorem tubeSection_surjective {k t : ℕ} (j : ℕ) (m : Monomial (4 + k))
    (hm : m ∈ (generatedOrderIdeal (higherTubeGenerators k t)).carrier)
    (hdeg : totalDeg m = higherDegree k t - j) :
    ∃ p : TubeCoordinates k t, tubeSection j p = m := by
  obtain ⟨g, hg, hmg⟩ := mem_generatedOrderIdeal_iff.mp hm
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
  have hqt := Finset.mem_range.mp hq
  rw [higherTube, blockMonomial_le] at hmg
  let p : TubeCoordinates k t :=
    (⟨m (Fin.castAdd k 1), by omega⟩,
      ⟨m (Fin.castAdd k 2), by omega⟩,
      ⟨m (Fin.castAdd k 3), by omega⟩,
      fun i => ⟨m (Fin.natAdd 4 i), by have := hmg.2.2.2.2 i; omega⟩)
  have hcoords := degree_block_coordinates m
  rw [hdeg] at hcoords
  have hfirst : higherDegree k t - j - tubeWeight p = m (Fin.castAdd k 0) := by
    dsimp [tubeWeight, p]
    omega
  refine ⟨p, ?_⟩
  rw [tubeSection, hfirst]
  exact blockMonomial_ext m

theorem tube_rank_count (k t j : ℕ) (ht : 2 ≤ t)
    (hlo : k + 12 ≤ j) (hhi : j ≤ k + 14) :
    pureOSequence (generatedOrderIdeal (higherTubeGenerators k t)) (higherDegree k t - j) =
      25 * (t + 3) * 2 ^ k := by
  classical
  have hcard : (Finset.univ : Finset (TubeCoordinates k t)).card = 25 * (t + 3) * 2 ^ k := by
    simp only [Finset.card_univ, TubeCoordinates, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin]
    ring
  rw [← hcard]
  symm
  apply Finset.card_bij (fun p _ => tubeSection j p)
  · intro p _
    exact Finset.mem_filter.mpr
      ⟨tubeSection_mem j p ht hlo hhi, tubeSection_degree j p hhi⟩
  · intro p _ q _ heq
    exact tubeSection_injective j heq
  · intro m hm
    obtain ⟨hmem, hdeg⟩ := Finset.mem_filter.mp hm
    obtain ⟨p, hp⟩ := tubeSection_surjective j m hmem hdeg
    exact ⟨p, Finset.mem_univ _, hp⟩

end ResearchMain.PureOSequences
