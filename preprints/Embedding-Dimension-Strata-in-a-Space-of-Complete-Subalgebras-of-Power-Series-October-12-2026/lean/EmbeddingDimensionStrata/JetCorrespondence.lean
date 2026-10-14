import EmbeddingDimensionStrata.ClosedSubalgebras
import EmbeddingDimensionStrata.Semigroup
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The actual conductor-60 finite-jet correspondence

Jets are the quotient of the power-series algebra by `(t^c)`. The subalgebras
on the complete side are actual closed subalgebras, with their full order set.
-/
noncomputable section
namespace EmbeddingDimensionStrata
open scoped PowerSeries.WithPiTopology

variable (K : Type*) [Field K]

/-- The ideal `(t^c)` in the actual formal power-series ring. -/
def tailIdeal (c : ℕ) : Ideal (PowerSeries K) :=
  Ideal.span {(PowerSeries.X : PowerSeries K) ^ c}

/-- The algebra of finite `c`-jets. -/
abbrev Jet (c : ℕ) := PowerSeries K ⧸ tailIdeal K c

/-- The quotient algebra homomorphism, rather than a coefficient-table projection. -/
def jetMap (c : ℕ) : PowerSeries K →ₐ[K] Jet K c :=
  Ideal.Quotient.mkₐ K (tailIdeal K c)

variable {K}

theorem mem_tailIdeal_iff (c : ℕ) (f : PowerSeries K) :
    f ∈ tailIdeal K c ↔ InTail c f := by
  simp only [tailIdeal, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff, InTail]

theorem jetMap_eq_zero_iff (c : ℕ) (f : PowerSeries K) :
    jetMap K c f = 0 ↔ InTail c f := by
  change Ideal.Quotient.mk _ f = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_tailIdeal_iff]

theorem jetMap_eq_iff (c : ℕ) (f g : PowerSeries K) :
    jetMap K c f = jetMap K c g ↔
      ∀ i < c, PowerSeries.coeff i f = PowerSeries.coeff i g := by
  rw [← sub_eq_zero, ← map_sub, jetMap_eq_zero_iff]
  simp only [InTail, map_sub, sub_eq_zero]

theorem jetMap_surjective (c : ℕ) : Function.Surjective (jetMap K c) :=
  Ideal.Quotient.mkₐ_surjective K _

theorem hasOrder_of_same_jet {c n : ℕ} (hn : n < c)
    {f g : PowerSeries K} (h : jetMap K c f = jetMap K c g) :
    HasOrder f n ↔ HasOrder g n := by
  have heq := (jetMap_eq_iff c f g).mp h
  simp only [HasOrder]
  constructor
  · rintro ⟨hl, hnz⟩
    exact ⟨fun i hi => (heq i (by omega)).symm.trans (hl i hi),
      (heq n hn) ▸ hnz⟩
  · rintro ⟨hl, hnz⟩
    exact ⟨fun i hi => (heq i (by omega)).trans (hl i hi),
      (heq n hn).symm ▸ hnz⟩

/-- The order set of a finite-jet subalgebra, extended by the conductor tail.
Below the cutoff, order is defined using any lift; `hasOrder_of_same_jet`
proves this does not depend on the chosen lift. -/
def JetHasValue {c : ℕ} (T : Subalgebra K (Jet K c)) (n : ℕ) : Prop :=
  c ≤ n ∨ (n < c ∧ ∃ f : PowerSeries K, jetMap K c f ∈ T ∧ HasOrder f n)

theorem jetHasValue_map_iff {c n : ℕ} (hn : n < c)
    (S : Subalgebra K (PowerSeries K)) :
    JetHasValue (S.map (jetMap K c)) n ↔ HasValue S n := by
  constructor
  · rintro (h | ⟨_, f, hf, hord⟩)
    · omega
    · obtain ⟨g, hg, hgf⟩ := hf
      exact ⟨g, hg, (hasOrder_of_same_jet hn hgf).mpr hord⟩
  · rintro ⟨f, hf, hord⟩
    exact Or.inr ⟨hn, f, ⟨f, hf, rfl⟩, hord⟩

theorem jetHasValue_comap_iff {c n : ℕ} (hn : n < c)
    (T : Subalgebra K (Jet K c)) :
    HasValue (T.comap (jetMap K c)) n ↔ JetHasValue T n := by
  simp only [HasValue, Subalgebra.mem_comap, JetHasValue]
  constructor
  · intro h
    exact Or.inr ⟨hn, h⟩
  · rintro (h | ⟨_, h⟩)
    · omega
    · exact h

section Topology
variable [TopologicalSpace K] [DiscreteTopology K]

theorem isOpen_tailIdeal (c : ℕ) :
    IsOpen (tailIdeal K c : Set (PowerSeries K)) := by
  have heq : (tailIdeal K c : Set (PowerSeries K)) =
      ⋂ i : Fin c, {f : PowerSeries K | PowerSeries.coeff (i : ℕ) f = 0} := by
    apply Set.ext
    intro f
    change f ∈ tailIdeal K c ↔ _
    rw [mem_tailIdeal_iff]
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, InTail]
    exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_discrete ({0} : Set K)).preimage
    (PowerSeries.WithPiTopology.continuous_coeff K i)

theorem isClosed_comap_jetMap {c : ℕ} (T : Subalgebra K (Jet K c)) :
    IsClosed (T.comap (jetMap K c) : Set (PowerSeries K)) := by
  apply (T.comap (jetMap K c)).toSubring.toAddSubgroup.isClosed_of_isOpen
  apply AddSubgroup.isOpen_mono (H₁ := (tailIdeal K c).toAddSubgroup)
  · intro f hf
    change jetMap K c f ∈ T
    have hf0 : jetMap K c f = 0 :=
      (jetMap_eq_zero_iff c f).mpr ((mem_tailIdeal_iff c f).mp hf)
    rw [hf0]
    exact T.zero_mem
  · exact isOpen_tailIdeal c

omit [DiscreteTopology K] in
/-- Every closed subalgebra with the specified value semigroup contains the full
conductor tail, including arbitrary infinite tails. -/
theorem tailIdeal_le_of_gamma
    (S : Subalgebra K (PowerSeries K))
    (hclosed : IsClosed (S : Set (PowerSeries K)))
    (hvalues : ∀ n, HasValue S n ↔ Gamma n) :
    (tailIdeal K 60 : Set (PowerSeries K)) ⊆ S := by
  intro f hf
  exact tail_mem_of_isClosed S hclosed 60
    (fun n hn => (hvalues n).mpr (gamma_of_ge_sixty n hn)) f
    ((mem_tailIdeal_iff 60 f).mp hf)

/-- Complete embedded subalgebras with the full specified value semigroup. -/
def CompleteGammaSubalgebra :=
  {S : Subalgebra K (PowerSeries K) //
    IsClosed (S : Set (PowerSeries K)) ∧ ∀ n, HasValue S n ↔ Gamma n}

/-- Actual finite-jet subalgebras with the specified extended order set. -/
def GammaJetSubalgebra :=
  {T : Subalgebra K (Jet K 60) // ∀ n, JetHasValue T n ↔ Gamma n}

/-- Truncation of a complete embedded subalgebra. -/
def toGammaJet (S : CompleteGammaSubalgebra (K := K)) : GammaJetSubalgebra (K := K) := by
  refine ⟨S.val.map (jetMap K 60), ?_⟩
  intro n
  by_cases hn : n < 60
  · exact (jetHasValue_map_iff hn S.val).trans (S.property.2 n)
  · constructor
    · intro _
      exact gamma_of_ge_sixty n (by omega)
    · intro _
      exact Or.inl (by omega)

/-- Reconstruction of a complete embedded subalgebra as the inverse image of
its finite-jet algebra. -/
def fromGammaJet (T : GammaJetSubalgebra (K := K)) : CompleteGammaSubalgebra (K := K) := by
  refine ⟨T.val.comap (jetMap K 60), isClosed_comap_jetMap T.val, ?_⟩
  intro n
  by_cases hn : n < 60
  · exact (jetHasValue_comap_iff hn T.val).trans (T.property n)
  · constructor
    · intro _
      exact gamma_of_ge_sixty n (by omega)
    · intro _
      refine ⟨PowerSeries.X ^ n, ?_, ?_⟩
      · change jetMap K 60 (PowerSeries.X ^ n) ∈ T.val
        have hz : jetMap K 60 (PowerSeries.X ^ n) = 0 := by
          apply (jetMap_eq_zero_iff _ _).mpr
          intro i hi
          simp only [PowerSeries.coeff_X_pow]
          split_ifs with h
          · omega
          · rfl
        rw [hz]
        exact T.val.zero_mem
      · rw [hasOrder_iff_order]
        simp

/-- The complete-subalgebra/finite-jet equivalence for Γ = ⟨10,11,34,46,58⟩. -/
def completeGammaJetEquiv :
    CompleteGammaSubalgebra (K := K) ≃ GammaJetSubalgebra (K := K) where
  toFun := toGammaJet
  invFun := fromGammaJet
  left_inv S := by
    apply Subtype.ext
    change (S.val.map (jetMap K 60)).comap (jetMap K 60) = S.val
    apply Subalgebra.comap_map_eq_self
    intro f hf
    apply tailIdeal_le_of_gamma S.val S.property.1 S.property.2
    apply (mem_tailIdeal_iff 60 f).mpr
    exact (jetMap_eq_zero_iff 60 f).mp hf
  right_inv T := by
    apply Subtype.ext
    exact Subalgebra.map_comap_eq_self_of_surjective (jetMap_surjective 60) T.val

end Topology
end EmbeddingDimensionStrata
