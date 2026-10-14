import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Polynomial-open obstructions for punctured affine space

These statements concern ordinary polynomial evaluation over an algebraically
closed field. The lower bound is proved by an explicit prime-ideal chain and
Krull's height theorem, connected to pointwise vanishing by Nullstellensatz.
-/
noncomputable section
namespace EmbeddingDimensionStrata
namespace GeometryObstructions
open MvPolynomial

variable {K : Type*} [Field K]

/-- Set the first `k` coordinates to zero. -/
def coordinateProjection (n k : ℕ) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun i => if i.val < k then 0 else X i

/-- The prime ideal of the coordinate linear subspace with the first `k`
coordinates zero. -/
def coordinateIdeal (n k : ℕ) : Ideal (MvPolynomial (Fin n) K) :=
  RingHom.ker (coordinateProjection (K := K) n k).toRingHom

instance coordinateIdeal_isPrime (n k : ℕ) :
    (coordinateIdeal (K := K) n k).IsPrime :=
  RingHom.ker_isPrime _

lemma coordinateProjection_comp (n k l : ℕ) (h : k ≤ l) :
    (coordinateProjection (K := K) n l).comp (coordinateProjection n k) =
      coordinateProjection n l := by
  ext i : 1
  simp only [AlgHom.comp_apply, coordinateProjection, aeval_X]
  split_ifs with hk hl
  · simp
  · omega
  · simp_all
  · simp_all

lemma coordinateIdeal_mono (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    coordinateIdeal (K := K) n k ≤ coordinateIdeal n l := by
  intro p hp
  change coordinateProjection n l p = 0
  rw [← coordinateProjection_comp n k l h, AlgHom.comp_apply]
  change coordinateProjection n k p = 0 at hp
  rw [hp, map_zero]

lemma coordinateIdeal_lt (n k : ℕ) (h : k < n) :
    coordinateIdeal (K := K) n k < coordinateIdeal n (k + 1) := by
  refine lt_of_le_of_ne (coordinateIdeal_mono n (Nat.le_succ k)) ?_
  intro he
  have hx : X (⟨k, h⟩ : Fin n) ∈ coordinateIdeal (K := K) n (k + 1) := by
    change coordinateProjection n (k + 1) (X (⟨k, h⟩ : Fin n)) = 0
    simp [coordinateProjection]
  rw [← he] at hx
  change coordinateProjection n k (X (⟨k, h⟩ : Fin n)) = 0 at hx
  simp [coordinateProjection] at hx

lemma coordinateIdeal_height (n k : ℕ) (h : k ≤ n) :
    (k : ℕ∞) ≤ (coordinateIdeal (K := K) n k).height := by
  induction k with
  | zero => exact bot_le
  | succ k ih =>
    have hk : k < n := by omega
    have hh := Ideal.height_add_one_le_of_lt_of_isPrime
      (coordinateIdeal_lt (K := K) n k hk)
    have hi := add_le_add_right (ih (by omega)) (1 : ℕ∞)
    have hi' : ((k + 1 : ℕ) : ℕ∞) ≤ (coordinateIdeal (K := K) n k).height + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hi
    exact hi'.trans hh

lemma coordinateIdeal_top_eq_origin (n : ℕ) :
    coordinateIdeal (K := K) n n = vanishingIdeal K {(0 : Fin n → K)} := by
  have he : coordinateProjection (K := K) n n =
      (Algebra.ofId K (MvPolynomial (Fin n) K)).comp (aeval (0 : Fin n → K)) := by
    ext i : 1
    simp [coordinateProjection]
  ext p
  simp only [coordinateIdeal, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, he, AlgHom.comp_apply, mem_vanishingIdeal_singleton_iff]
  simp

/-- The origin ideal in affine `n`-space has height at least `n`. -/
theorem origin_height_lower_bound (n : ℕ) :
    (n : ℕ∞) ≤ (vanishingIdeal K {(0 : Fin n → K)}).height := by
  rw [← coordinateIdeal_top_eq_origin]
  exact coordinateIdeal_height n n le_rfl

/-- Over an algebraically closed field, at least `n` equations are required
for a set-theoretic definition of the origin in affine `n`-space. -/
theorem equations_at_origin_lower_bound [IsAlgClosed K] (n r : ℕ)
    (f : Fin r → MvPolynomial (Fin n) K)
    (hf : ∀ x : Fin n → K, (∀ i, aeval x (f i) = 0) ↔ x = 0) : n ≤ r := by
  classical
  let I : Ideal (MvPolynomial (Fin n) K) := Ideal.span (Set.range f)
  let P : Ideal (MvPolynomial (Fin n) K) := vanishingIdeal K {(0 : Fin n → K)}
  have hz : zeroLocus K I = {(0 : Fin n → K)} := by
    ext x
    simpa [I, zeroLocus_span] using hf x
  have hr : I.radical = P := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hz]
  have hp : P ∈ I.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hr]
    simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
  have hb := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (s := Finset.univ.image f) (p := P) (by simpa [I] using hp)
  have hc : (Finset.univ.image f).card ≤ r :=
    (Finset.card_image_le).trans (by simp)
  have hnr : (n : ℕ∞) ≤ r := (origin_height_lower_bound (K := K) n).trans
    (hb.trans (by exact_mod_cast hc))
  exact_mod_cast hnr

/-- Ordinary polynomial principal open, as a set of rational points. -/
def polynomialPrincipalOpen {ι : Type*} (f : MvPolynomial ι K) : Set (ι → K) :=
  {x | aeval x f ≠ 0}

/-- The classical affine-coordinate set `A^m × (A^3 \ {0})`. -/
def puncturedProduct (m : ℕ) : Set ((Fin m ⊕ Fin 3) → K) :=
  {x | ∃ i : Fin 3, x (Sum.inr i) ≠ 0}

/-- Restrict a polynomial to the three-dimensional coordinate plane `q = 0`. -/
def restrictToTriple (m : ℕ) :
    MvPolynomial (Fin m ⊕ Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval (Sum.elim (fun _ => 0) X)

lemma eval_restrictToTriple (m : ℕ) (x : Fin 3 → K)
    (f : MvPolynomial (Fin m ⊕ Fin 3) K) :
    aeval x (restrictToTriple m f) = aeval (Sum.elim (fun _ => 0) x) f := by
  have he : (aeval x).comp (restrictToTriple (K := K) m) =
      aeval (Sum.elim (fun _ : Fin m => 0) x) := by
    ext i : 1
    cases i <;> simp [restrictToTriple]
  exact congrArg (fun g => g f) he

/-- Any cover of `A^m × (A^3 \ {0})` by polynomial principal opens
requires at least three opens. This quantifies over arbitrary polynomials. -/
theorem puncturedProduct_principal_cover_lower_bound [IsAlgClosed K] (m r : ℕ)
    (f : Fin r → MvPolynomial (Fin m ⊕ Fin 3) K)
    (hf : puncturedProduct (K := K) m = ⋃ i, polynomialPrincipalOpen (f i)) :
    3 ≤ r := by
  apply equations_at_origin_lower_bound (K := K) 3 r (fun i => restrictToTriple m (f i))
  intro x
  have hx := Set.ext_iff.mp hf (Sum.elim (fun _ => 0) x)
  simp only [puncturedProduct, Set.mem_ofPred_eq, Sum.elim_inr, Set.mem_iUnion,
    polynomialPrincipalOpen] at hx
  simp only [eval_restrictToTriple]
  constructor
  · intro he
    have hn : ¬ ∃ j, x j ≠ 0 := by
      intro hj
      obtain ⟨i, hi⟩ := hx.mp hj
      exact hi (he i)
    push Not at hn
    exact funext hn
  · rintro rfl i
    by_contra hi
    have hj := hx.mpr ⟨i, hi⟩
    simp at hj

/-- The three distinguished coordinate principal opens cover the puncture. -/
theorem puncturedProduct_three_principal_opens (m : ℕ) :
    puncturedProduct (K := K) m =
      ⋃ i : Fin 3, polynomialPrincipalOpen (X (Sum.inr i)) := by
  ext x
  simp [puncturedProduct, polynomialPrincipalOpen]

theorem puncturedProduct_not_two_principal_opens [IsAlgClosed K] (m : ℕ)
    (f g : MvPolynomial (Fin m ⊕ Fin 3) K) :
    puncturedProduct (K := K) m ≠ polynomialPrincipalOpen f ∪ polynomialPrincipalOpen g := by
  intro h
  have hh : puncturedProduct (K := K) m =
      ⋃ i : Fin 2, polynomialPrincipalOpen (![f, g] i) := by
    rw [h]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hx | hx)
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
  have hb := puncturedProduct_principal_cover_lower_bound m 2 ![f, g] hh
  omega

theorem puncturedProduct_not_principal_open [IsAlgClosed K] (m : ℕ)
    (f : MvPolynomial (Fin m ⊕ Fin 3) K) :
    puncturedProduct (K := K) m ≠ polynomialPrincipalOpen f := by
  intro h
  apply puncturedProduct_not_two_principal_opens m f f
  simpa only [Set.union_self] using h

/-- Exactly three polynomial principal opens are necessary and sufficient. -/
theorem puncturedProduct_minimal_principal_cover [IsAlgClosed K] (m : ℕ) :
    IsLeast {r : ℕ | ∃ f : Fin r → MvPolynomial (Fin m ⊕ Fin 3) K,
      puncturedProduct (K := K) m = ⋃ i, polynomialPrincipalOpen (f i)} 3 := by
  constructor
  · exact ⟨fun i => X (Sum.inr i), puncturedProduct_three_principal_opens m⟩
  · rintro r ⟨f, hf⟩
    exact puncturedProduct_principal_cover_lower_bound m r f hf

end GeometryObstructions
end EmbeddingDimensionStrata
