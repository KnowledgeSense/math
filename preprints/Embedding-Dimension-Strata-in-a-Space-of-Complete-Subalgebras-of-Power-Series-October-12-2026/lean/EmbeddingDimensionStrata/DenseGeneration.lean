import EmbeddingDimensionStrata.NormalForms
import Mathlib.Topology.Algebra.Algebra

/-! # Generation in actual subalgebras from their full value semigroup -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

theorem HasValue.zero (S : Subalgebra K (PowerSeries K)) : HasValue S 0 := by
  refine ⟨1, S.one_mem, ?_⟩
  rw [hasOrder_iff_order]
  exact PowerSeries.order_one

theorem HasValue.add {S : Subalgebra K (PowerSeries K)} {m n : ℕ}
    (hm : HasValue S m) (hn : HasValue S n) : HasValue S (m + n) := by
  obtain ⟨f, hf, hfo⟩ := hm
  obtain ⟨g, hg, hgo⟩ := hn
  refine ⟨f * g, S.mul_mem hf hg, ?_⟩
  rw [hasOrder_iff_order, PowerSeries.order_mul,
    (hasOrder_iff_order f m).mp hfo, (hasOrder_iff_order g n).mp hgo]
  simp

theorem HasValue.mul_nat {S : Subalgebra K (PowerSeries K)} {n : ℕ}
    (hn : HasValue S n) (a : ℕ) : HasValue S (n * a) := by
  induction a with
  | zero => simpa using HasValue.zero S
  | succ a ih => simpa [Nat.mul_succ] using ih.add hn

theorem hasValue_of_gamma (S : Subalgebra K (PowerSeries K))
    (h10 : HasValue S 10) (h11 : HasValue S 11) (h34 : HasValue S 34)
    (h46 : HasValue S 46) (h58 : HasValue S 58)
    {n : ℕ} (hn : Gamma n) : HasValue S n := by
  obtain ⟨a, b, c, d, e, rfl⟩ := hn
  exact ((((h10.mul_nat a).add (h11.mul_nat b)).add
    (h34.mul_nat c)).add (h46.mul_nat d)).add (h58.mul_nat e)

/-- If a subalgebra realizes every order of a larger algebra, every element of
the larger algebra admits arbitrarily accurate polynomial approximations in it. -/
theorem exists_approximation_of_same_values
    (T S : Subalgebra K (PowerSeries K)) (hTS : T ≤ S)
    (hvalues : ∀ n, HasValue S n → HasValue T n)
    (f : PowerSeries K) (hf : f ∈ S) (N : ℕ) :
    ∃ g ∈ T, ∀ i < N, PowerSeries.coeff i g = PowerSeries.coeff i f := by
  induction N with
  | zero => exact ⟨0, T.zero_mem, fun i hi => by omega⟩
  | succ N ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    by_cases hz : PowerSeries.coeff N (f - g) = 0
    · refine ⟨g, hg, ?_⟩
      intro i hi
      by_cases hlt : i < N
      · exact hgf i hlt
      · have heq : i = N := by omega
        subst i
        exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm
    · have ho : HasOrder (f - g) N := by
        refine ⟨?_, hz⟩
        intro i hi
        simp only [map_sub, hgf i hi, sub_self]
      obtain ⟨w, hw, hwlow, hwlead⟩ :=
        hvalues N ⟨f - g, S.sub_mem hf (hTS hg), ho⟩
      let a : K := (PowerSeries.coeff N f - PowerSeries.coeff N g) /
        PowerSeries.coeff N w
      refine ⟨g + a • w, T.add_mem hg (T.smul_mem hw a), ?_⟩
      intro i hi
      by_cases hlt : i < N
      · simp only [map_add, map_smul, hwlow i hlt, smul_zero, add_zero]
        exact hgf i hlt
      · have heq : i = N := by omega
        subst i
        simp only [map_add, map_smul, smul_eq_mul, a]
        rw [div_mul_cancel₀ _ hwlead]
        exact add_sub_cancel _ _

open scoped PowerSeries.WithPiTopology in
/-- Equality of full order sets implies density for nested embedded subalgebras. -/
theorem le_closure_of_same_values
    [TopologicalSpace K]
    (T S : Subalgebra K (PowerSeries K)) (hTS : T ≤ S)
    (hvalues : ∀ n, HasValue S n → HasValue T n) :
    (S : Set (PowerSeries K)) ⊆ closure (T : Set (PowerSeries K)) := by
  intro f hf
  choose g hg hag using exists_approximation_of_same_values T S hTS hvalues f hf
  apply mem_closure_of_tendsto (f := g) (b := Filter.atTop)
  · rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    exact tendsto_atTop_of_eventually_const fun n (hn : d < n) => hag n d hn
  · exact Filter.Eventually.of_forall hg

/-- Density already gives algebraic generation after any finite truncation. -/
theorem map_jet_eq_of_same_values
    (T S : Subalgebra K (PowerSeries K)) (hTS : T ≤ S)
    (hvalues : ∀ n, HasValue S n → HasValue T n) (c : ℕ) :
    T.map (jetMap K c) = S.map (jetMap K c) := by
  apply le_antisymm (Subalgebra.map_mono hTS)
  intro q hq
  obtain ⟨f, hf, rfl⟩ := hq
  obtain ⟨g, hg, heq⟩ := exists_approximation_of_same_values T S hTS hvalues f hf c
  exact ⟨g, hg, (jetMap_eq_iff c g f).mpr heq⟩

end EmbeddingDimensionStrata
