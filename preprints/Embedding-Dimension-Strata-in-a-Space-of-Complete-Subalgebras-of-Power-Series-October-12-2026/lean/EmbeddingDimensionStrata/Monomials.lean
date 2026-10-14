import EmbeddingDimensionStrata.ParameterSpace
import EmbeddingDimensionStrata.JetCoefficients
import Mathlib.Tactic.FinCases

/-! # The actual monomials of weight below the conductor -/
noncomputable section
namespace EmbeddingDimensionStrata

abbrev Exponent := ℕ × ℕ × ℕ × ℕ × ℕ

def monomialWeight (a : Exponent) : ℕ :=
  10 * a.1 + 11 * a.2.1 + 34 * a.2.2.1 + 46 * a.2.2.2.1 + 58 * a.2.2.2.2

def monomialDegree (a : Exponent) : ℕ :=
  a.1 + a.2.1 + a.2.2.1 + a.2.2.2.1 + a.2.2.2.2

def smallExponents : Finset Exponent :=
  {(0,0,0,0,0), (1,0,0,0,0), (0,1,0,0,0),
   (2,0,0,0,0), (1,1,0,0,0), (0,2,0,0,0),
   (3,0,0,0,0), (2,1,0,0,0), (1,2,0,0,0), (0,3,0,0,0),
   (4,0,0,0,0), (3,1,0,0,0), (2,2,0,0,0), (1,3,0,0,0), (0,4,0,0,0),
   (5,0,0,0,0), (4,1,0,0,0), (3,2,0,0,0), (2,3,0,0,0), (1,4,0,0,0), (0,5,0,0,0),
   (0,0,1,0,0), (1,0,1,0,0), (0,1,1,0,0),
   (2,0,1,0,0), (1,1,1,0,0), (0,2,1,0,0),
   (0,0,0,1,0), (1,0,0,1,0), (0,1,0,1,0), (0,0,0,0,1)}

/-- The list is exhaustive over all nonnegative exponents, not just a bounded search. -/
theorem mem_smallExponents_iff (a : Exponent) :
    a ∈ smallExponents ↔ monomialWeight a < 60 := by
  constructor
  · intro ha
    have hall : ∀ b ∈ smallExponents, monomialWeight b < 60 := by decide
    exact hall a ha
  · rcases a with ⟨a,b,c,d,e⟩
    intro ha
    dsimp [monomialWeight] at ha
    have ha' : a ≤ 5 := by omega
    have hb : b ≤ 5 := by omega
    have hc : c ≤ 1 := by omega
    have hd : d ≤ 1 := by omega
    have he : e ≤ 1 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      interval_cases d <;> interval_cases e <;> first | omega | decide

theorem smallExponents_card : smallExponents.card = 31 := by decide

theorem smallExponents_decomposable_card :
    (smallExponents.filter fun a => 2 ≤ monomialDegree a).card = 25 := by decide

/-- The selected representative at each semigroup value, as in Definition 3.3. -/
def basisExponent (n : ℕ) : Exponent :=
  match n with
  | 10 => (1,0,0,0,0) | 11 => (0,1,0,0,0)
  | 20 => (2,0,0,0,0) | 21 => (1,1,0,0,0) | 22 => (0,2,0,0,0)
  | 30 => (3,0,0,0,0) | 31 => (2,1,0,0,0) | 32 => (1,2,0,0,0)
  | 33 => (0,3,0,0,0) | 34 => (0,0,1,0,0)
  | 40 => (4,0,0,0,0) | 41 => (3,1,0,0,0) | 42 => (2,2,0,0,0)
  | 43 => (1,3,0,0,0) | 44 => (1,0,1,0,0) | 45 => (0,1,1,0,0)
  | 46 => (0,0,0,1,0)
  | 50 => (5,0,0,0,0) | 51 => (4,1,0,0,0) | 52 => (3,2,0,0,0)
  | 53 => (2,3,0,0,0) | 54 => (2,0,1,0,0) | 55 => (1,1,1,0,0)
  | 56 => (1,0,0,1,0) | 57 => (0,1,0,1,0) | 58 => (0,0,0,0,1)
  | _ => (0,0,0,0,0)

theorem basisExponent_weight (n : ℕ) (hn : n ∈ valuesBelowConductor) :
    monomialWeight (basisExponent n) = n := by
  have hall : ∀ k ∈ valuesBelowConductor, monomialWeight (basisExponent k) = k := by decide
  exact hall n hn

theorem smallExponents_partition (a : Exponent) (ha : a ∈ smallExponents) :
    a = basisExponent (monomialWeight a) ∨
    a = (0,4,0,0,0) ∨ a = (1,4,0,0,0) ∨ a = (0,5,0,0,0) ∨ a = (0,2,1,0,0) := by
  have hall : ∀ a ∈ smallExponents,
    a = basisExponent (monomialWeight a) ∨
    a = (0,4,0,0,0) ∨ a = (1,4,0,0,0) ∨ a = (0,5,0,0,0) ∨ a = (0,2,1,0,0) := by decide
  exact hall a ha

section Universal
variable {A : Type*} [CommRing A]

/-- Monic of an exact order, meaningful even over the universal coefficient ring. -/
def MonicAt (f : PowerSeries A) (n : ℕ) : Prop :=
  (∀ i < n, PowerSeries.coeff i f = 0) ∧ PowerSeries.coeff n f = 1

theorem MonicAt.one : MonicAt (1 : PowerSeries A) 0 := by
  constructor
  · intro i hi; omega
  · simp

theorem MonicAt.mul {f g : PowerSeries A} {m n : ℕ}
    (hf : MonicAt f m) (hg : MonicAt g n) : MonicAt (f * g) (m+n) := by
  constructor
  · intro i hi
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ab hab
    have hh := Finset.mem_antidiagonal.mp hab
    by_cases h : ab.1 < m
    · rw [hf.1 _ h, zero_mul]
    · rw [hg.1 _ (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (m,n) (by simp)]
    · rw [hf.2, hg.2, mul_one]
    · intro ab hab hne
      have hh := Finset.mem_antidiagonal.mp hab
      by_cases h : ab.1 < m
      · rw [hf.1 _ h, zero_mul]
      · have hlt : ab.2 < n := by
          by_contra hnot
          apply hne
          apply Prod.ext <;> dsimp <;> omega
        rw [hg.1 _ hlt, mul_zero]

theorem MonicAt.pow {f : PowerSeries A} {m : ℕ} (hf : MonicAt f m) (n : ℕ) :
    MonicAt (f ^ n) (m*n) := by
  induction n with
  | zero => simpa using (MonicAt.one (A := A))
  | succ n ih => simpa [pow_succ, Nat.mul_succ] using ih.mul hf

theorem monicAt_normalSeries (p : NormalCoordinate → A) (i : Fin 5) :
    MonicAt (normalSeries p i) (generatorValue i) := by
  constructor
  · intro n hn
    rw [coeff_normalSeries, ite_eq_right (by omega : n ≠ generatorValue i)]
    rw [dite_eq_right (by omega : ¬ (n < 60 ∧ generatorValue i < n ∧ n ∉ valuesBelowConductor))]
  · rw [coeff_normalSeries, ite_eq_left rfl]

def seriesMonomial (p : NormalCoordinate → A) (a : Exponent) : PowerSeries A :=
  normalSeries p 0 ^ a.1 * normalSeries p 1 ^ a.2.1 *
  normalSeries p 2 ^ a.2.2.1 * normalSeries p 3 ^ a.2.2.2.1 *
  normalSeries p 4 ^ a.2.2.2.2

theorem seriesMonomial_monic (p : NormalCoordinate → A) (a : Exponent) :
    MonicAt (seriesMonomial p a) (monomialWeight a) :=
  ((((monicAt_normalSeries p 0).pow a.1).mul ((monicAt_normalSeries p 1).pow a.2.1)).mul
    ((monicAt_normalSeries p 2).pow a.2.2.1)).mul
    ((monicAt_normalSeries p 3).pow a.2.2.2.1) |>.mul
    ((monicAt_normalSeries p 4).pow a.2.2.2.2)

/-- The actual power-series monomials selected in the paper. -/
def basisSeries (p : NormalCoordinate → A) (n : ℕ) : PowerSeries A :=
  seriesMonomial p (basisExponent n)

theorem basisSeries_monic (p : NormalCoordinate → A) (n : ℕ)
    (hn : n ∈ valuesBelowConductor) : MonicAt (basisSeries p n) n := by
  simpa only [basisSeries, basisExponent_weight n hn] using seriesMonomial_monic p (basisExponent n)

end Universal
section Field
variable {K : Type*} [Field K]

def jetMonomial (p : NormalCoordinate → K) (a : Exponent) : Jet K 60 :=
  jetMap K 60 (seriesMonomial p a)

theorem jetMonomial_zero (p : NormalCoordinate → K) :
    jetMonomial p (0,0,0,0,0) = 1 := by
  simp [jetMonomial, seriesMonomial]

theorem jetMonomial_add (p : NormalCoordinate → K) (a b : Exponent) :
    jetMonomial p (a+b) = jetMonomial p a * jetMonomial p b := by
  simp only [jetMonomial, seriesMonomial, Prod.fst_add, Prod.snd_add, pow_add, map_mul]
  ring

theorem jetMonomial_eq_zero (p : NormalCoordinate → K) (a : Exponent)
    (ha : 60 ≤ monomialWeight a) : jetMonomial p a = 0 := by
  apply (jetMap_eq_zero_iff 60 _).mpr
  intro i hi
  exact (seriesMonomial_monic p a).1 i (by omega)

theorem jetMonomial_mem (p : NormalCoordinate → K) (a : Exponent) :
    jetMonomial p a ∈ parameterJetAlgebra p := by
  simp only [jetMonomial, seriesMonomial, map_mul, map_pow]
  apply Subalgebra.mul_mem
  · apply Subalgebra.mul_mem
    · apply Subalgebra.mul_mem
      · apply Subalgebra.mul_mem <;>
          exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self _)) _
      · exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self _)) _
    · exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self _)) _
  · exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self _)) _

/-- Every element of the multiplicative monoid generated by the five jets is
an actual monomial in them. -/
theorem closure_normalJets_monomial (p : NormalCoordinate → K)
    {x : Jet K 60}
    (hx : x ∈ Submonoid.closure (Set.range fun i : Fin 5 => jetMap K 60 (normalSeries p i))) :
    ∃ a : Exponent, x = jetMonomial p a := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    fin_cases i
    · exact ⟨(1,0,0,0,0), by simp [jetMonomial, seriesMonomial]⟩
    · exact ⟨(0,1,0,0,0), by simp [jetMonomial, seriesMonomial]⟩
    · exact ⟨(0,0,1,0,0), by simp [jetMonomial, seriesMonomial]⟩
    · exact ⟨(0,0,0,1,0), by simp [jetMonomial, seriesMonomial]⟩
    · exact ⟨(0,0,0,0,1), by simp [jetMonomial, seriesMonomial]⟩
  | one => exact ⟨(0,0,0,0,0), (jetMonomial_zero p).symm⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a,rfl⟩ := ihx
    obtain ⟨b,rfl⟩ := ihy
    exact ⟨a+b, (jetMonomial_add p a b).symm⟩

/-- The genuine generated quotient algebra is spanned by exactly the 31
listed monomials. The assertion applies to every coefficient point. -/
theorem parameterJetAlgebra_span (p : NormalCoordinate → K) :
    (parameterJetAlgebra p).toSubmodule =
      Submodule.span K (jetMonomial p '' (smallExponents : Set Exponent)) := by
  apply le_antisymm
  · rw [parameterJetAlgebra, Algebra.adjoin_eq_span]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a,rfl⟩ := closure_normalJets_monomial p hx
    by_cases ha : a ∈ smallExponents
    · exact Submodule.subset_span ⟨a,ha,rfl⟩
    · rw [jetMonomial_eq_zero p a (by
        have hh := (mem_smallExponents_iff a).not.mp ha
        omega)]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨a,_,rfl⟩
    exact jetMonomial_mem p a

end Field
end EmbeddingDimensionStrata
