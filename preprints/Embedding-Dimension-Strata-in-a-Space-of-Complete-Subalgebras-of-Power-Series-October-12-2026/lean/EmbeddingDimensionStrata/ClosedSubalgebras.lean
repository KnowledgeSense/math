import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# Closed subalgebras and the conductor tail

The topology used here is the coefficientwise topology. For a discrete coefficient
field this is the formal (t-adic) topology, not the analytic topology on coefficients.
No finite jet data are used to define the subalgebras in this file.
-/
namespace EmbeddingDimensionStrata
open scoped PowerSeries.WithPiTopology

variable {K : Type*} [Field K]

/-- The order of a nonzero power series, expressed by its actual coefficients. -/
def HasOrder (f : PowerSeries K) (n : ℕ) : Prop :=
  (∀ i < n, PowerSeries.coeff i f = 0) ∧ PowerSeries.coeff n f ≠ 0

theorem hasOrder_iff_order (f : PowerSeries K) (n : ℕ) :
    HasOrder f n ↔ f.order = n := by
  simpa [HasOrder, and_comm] using (PowerSeries.order_eq_nat (φ := f) (n := n)).symm

/-- The complete order set of an embedded subalgebra, without a truncation. -/
def HasValue (S : Subalgebra K (PowerSeries K)) (n : ℕ) : Prop :=
  ∃ f ∈ S, HasOrder f n

/-- Every series supported at and above `c` is in the conductor tail. -/
def InTail (c : ℕ) (f : PowerSeries K) : Prop :=
  ∀ i < c, PowerSeries.coeff i f = 0

/-- Successive elimination produces arbitrary-order approximations inside the
actual subalgebra when it realizes every order at or above `c`. -/
theorem exists_approximation_of_values
    (S : Subalgebra K (PowerSeries K)) (c : ℕ)
    (hvalues : ∀ n, c ≤ n → HasValue S n)
    (f : PowerSeries K) (hf : InTail c f) (N : ℕ) :
    ∃ g ∈ S, ∀ i < c + N, PowerSeries.coeff i g = PowerSeries.coeff i f := by
  induction N with
  | zero =>
    refine ⟨0, S.zero_mem, ?_⟩
    intro i hi
    simpa using (hf i (by omega)).symm
  | succ N ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    obtain ⟨w, hw, hlow, hlead⟩ := hvalues (c + N) (by omega)
    let a : K := (PowerSeries.coeff (c + N) f - PowerSeries.coeff (c + N) g) /
      PowerSeries.coeff (c + N) w
    refine ⟨g + a • w, S.add_mem hg (S.smul_mem hw a), ?_⟩
    intro i hi
    by_cases hlt : i < c + N
    · simp only [map_add, map_smul, hlow i hlt, smul_zero, add_zero]
      exact hgf i hlt
    · have heq : i = c + N := by omega
      subst i
      simp only [map_add, map_smul, smul_eq_mul, a]
      rw [div_mul_cancel₀ _ hlead]
      exact add_sub_cancel _ _

/-- The conductor containment theorem for actual closed power-series subalgebras. -/
theorem tail_mem_of_isClosed
    [TopologicalSpace K]
    (S : Subalgebra K (PowerSeries K)) (hclosed : IsClosed (S : Set (PowerSeries K)))
    (c : ℕ) (hvalues : ∀ n, c ≤ n → HasValue S n)
    (f : PowerSeries K) (hf : InTail c f) : f ∈ S := by
  choose g hg hag using exists_approximation_of_values S c hvalues f hf
  apply hclosed.mem_of_tendsto (f := g) (b := Filter.atTop)
  · rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    exact tendsto_atTop_of_eventually_const fun n (hn : d < n) =>
      hag n d (by omega)
  · exact Filter.Eventually.of_forall hg

end EmbeddingDimensionStrata
