import MainTheorems.WishartBlocks.SpectralLaw.Eigenvalues.SortedSpectrum
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace

namespace ResearchMain.WishartBlocks

open Matrix Set
open scoped BigOperators Topology Matrix.Norms.L2Operator

theorem isClosed_ascendingSpectrum_graph (n : ℕ) :
    IsClosed (Function.graph (ascendingSpectrum (n := n))) := by
  have heq : Function.graph (ascendingSpectrum (n := n)) =
      {p : SymmetricMatrix n × (Fin n → ℝ) | Monotone p.2} ∩
      ⋂ t : ℝ, {p : SymmetricMatrix n × (Fin n → ℝ) |
        (Matrix.scalar (Fin n) t - p.1.val).det =
          (Matrix.scalar (Fin n) t - Matrix.diagonal p.2).det} := by
    ext p
    simp only [Function.graph, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [ascendingSpectrum_eq_iff]
    constructor
    · rintro ⟨hp, hc⟩
      refine ⟨hp, ?_⟩
      intro t
      have ht := congrArg (fun q : Polynomial ℝ => q.eval t) hc
      simpa only [Matrix.eval_charpoly] using ht
    · rintro ⟨hp, hc⟩
      refine ⟨hp, ?_⟩
      apply Polynomial.funext
      intro t
      simpa only [Matrix.eval_charpoly] using hc t
  rw [heq]
  apply (isClosed_monotone.preimage continuous_snd).inter
  apply isClosed_iInter
  intro t
  exact isClosed_eq (by fun_prop) (by fun_prop)

theorem continuous_ascendingSpectrum (n : ℕ) :
    Continuous (ascendingSpectrum (n := n)) := by
  classical
  rw [continuous_iff_continuousAt]
  intro W
  let s : Set (SymmetricMatrix n) := {V | ‖V.val‖ < ‖W.val‖ + 1}
  let M : ℝ := (‖W.val‖ + 1) * ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖
  let K : Set (Fin n → ℝ) := Set.Icc (fun _ => -M) (fun _ => M)
  have hs : IsOpen s := isOpen_lt (continuous_subtype_val.norm) continuous_const
  have hW : W ∈ s := by simp only [s, mem_ofPred_eq]; linarith
  have hmaps : ∀ V : s, ascendingSpectrum V.val ∈ K := by
    intro V
    have hb (i : Fin n) : ‖ascendingSpectrum V.val i‖ ≤ M :=
      (ascendingSpectrum_norm_le V.val i).trans
        (mul_le_mul_of_nonneg_right V.property.le (norm_nonneg _))
    constructor
    · intro i
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hb i)).1
    · intro i
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hb i)).2
  let g : s → K := fun V => ⟨ascendingSpectrum V.val, hmaps V⟩
  have hcompact : IsCompact K := isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  have hg : IsClosed (Function.graph g) := by
    have hmap : Continuous (fun p : s × K => (p.1.val, p.2.val)) := by fun_prop
    have h := (isClosed_ascendingSpectrum_graph n).preimage hmap
    convert h using 1
    ext p
    simp only [Function.graph, mem_ofPred_eq, mem_preimage, g, Subtype.ext_iff]
  have hcont : Continuous (s.domRestrict (ascendingSpectrum (n := n))) :=
    continuous_subtype_val.comp (continuous_of_isClosed_graph hg)
  exact (continuousOn_iff_continuous_domRestrict.mpr hcont).continuousAt (hs.mem_nhds hW)

noncomputable def hermitianSymmetrization (n : ℕ)
    (W : Matrix (Fin n) (Fin n) ℝ) : SymmetricMatrix n :=
  ⟨(1 / 2 : ℝ) • (W + W.transpose), by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_add_transpose_self W).smul
        (show IsSelfAdjoint (1 / 2 : ℝ) from by simp)⟩

theorem continuous_hermitianSymmetrization (n : ℕ) :
    Continuous (hermitianSymmetrization n) := by
  apply Continuous.subtype_mk
  fun_prop

theorem hermitianSymmetrization_eq {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.IsHermitian) : hermitianSymmetrization n W = ⟨W, hW⟩ := by
  apply Subtype.ext
  have ht : W.transpose = W := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hW.eq
  ext i j
  simp only [hermitianSymmetrization, ht, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

noncomputable def sortedEigenvalues (n : ℕ)
    (W : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  ascendingSpectrum (hermitianSymmetrization n W)

theorem continuous_sortedEigenvalues (n : ℕ) : Continuous (sortedEigenvalues n) :=
  (continuous_ascendingSpectrum n).comp (continuous_hermitianSymmetrization n)

theorem measurable_sortedEigenvalues (n : ℕ) : Measurable (sortedEigenvalues n) :=
  (continuous_sortedEigenvalues n).measurable

theorem sortedEigenvalues_eq_ascendingSpectrum {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.IsHermitian) :
    sortedEigenvalues n W = ascendingSpectrum ⟨W, hW⟩ := by
  rw [sortedEigenvalues, hermitianSymmetrization_eq hW]

theorem sortedEigenvalues_monotone {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) :
    Monotone (sortedEigenvalues n W) :=
  ascendingSpectrum_monotone _

theorem sortedEigenvalues_nonneg {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosSemidef) (i : Fin n) : 0 ≤ sortedEigenvalues n W i := by
  rw [sortedEigenvalues_eq_ascendingSpectrum hW.isHermitian]
  exact ascendingSpectrum_nonneg hW i

theorem sortedEigenvalues_pos {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) (i : Fin n) : 0 < sortedEigenvalues n W i := by
  rw [sortedEigenvalues_eq_ascendingSpectrum hW.isHermitian]
  exact ascendingSpectrum_pos hW i

theorem sortedEigenvalues_trace {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.IsHermitian) : W.trace = ∑ i, sortedEigenvalues n W i := by
  rw [sortedEigenvalues_eq_ascendingSpectrum hW]
  exact ascendingSpectrum_trace ⟨W, hW⟩

theorem sortedEigenvalues_det {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.IsHermitian) : W.det = ∏ i, sortedEigenvalues n W i := by
  rw [sortedEigenvalues_eq_ascendingSpectrum hW]
  exact ascendingSpectrum_det ⟨W, hW⟩

end ResearchMain.WishartBlocks
