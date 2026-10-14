import EmbeddingDimensionStrata.MonomialIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Algebra generators and the actual cotangent module of an augmented algebra -/
noncomputable section
namespace EmbeddingDimensionStrata
namespace NilpotentGenerators
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The elementary nilpotent form of the algebraic Nakayama argument. -/
theorem ideal_le_subalgebra_of_square (I : Ideal A) (S : Subalgebra K A)
    (h : I.restrictScalars K ≤ S.toSubmodule ⊔ (I ^ 2).restrictScalars K)
    (hnil : ∃ n : ℕ, I ^ n = ⊥) : I.restrictScalars K ≤ S.toSubmodule := by
  have step : ∀ n : ℕ, (I ^ (n+1)).restrictScalars K ≤
      S.toSubmodule ⊔ (I ^ (n+2)).restrictScalars K := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      rw [show n + 1 + 1 = (n+1)+1 from rfl, pow_succ, Ideal.restrictScalars_mul]
      apply Submodule.mul_le.mpr
      intro x hx y hy
      obtain ⟨s, hs, r, hr, hsr⟩ := Submodule.mem_sup.mp (ih hx)
      obtain ⟨t, ht, q, hq, htq⟩ := Submodule.mem_sup.mp (h hy)
      have hsI : s ∈ I ^ (n+1) := by
        have hrI : r ∈ I ^ (n+1) := Ideal.pow_le_pow_right (by omega) hr
        have := (I ^ (n+1)).sub_mem hx hrI
        simpa only [← hsr, add_sub_cancel_right] using this
      have hsq : s*q ∈ I ^ (n+1+2) := by
        rw [pow_add]
        exact Ideal.mul_mem_mul hsI hq
      have hry : r*y ∈ I ^ (n+2+1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul hr hy
      refine Submodule.mem_sup.mpr ⟨s*t, S.mul_mem hs ht, s*q+r*y, ?_, ?_⟩
      · exact (I ^ (n+1+2)).add_mem hsq hry
      · rw [← hsr, ← htq]
        ring
  have approx : ∀ n : ℕ, I.restrictScalars K ≤ S.toSubmodule ⊔
      (I ^ (n+1)).restrictScalars K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => exact ih.trans ((sup_le le_sup_left (step n)).trans_eq (by simp))
  obtain ⟨n, hn⟩ := hnil
  have hz : I ^ (n+1) = ⊥ := by rw [pow_succ, hn, Ideal.bot_mul]
  simpa [hz] using approx n


variable (ε : A →ₐ[K] K)

abbrev augmentation : Ideal A := RingHom.ker ε.toRingHom

/-- Subtract the scalar constant, landing in the actual augmentation ideal. -/
def center : A →ₗ[K] augmentation ε :=
  (LinearMap.id - ε.toLinearMap.smulRight 1).codRestrict ((augmentation ε).restrictScalars K)
    (by
      intro x
      change ε (x - ε x • (1 : A)) = 0
      simp)

@[simp] theorem center_val (x : A) : (center ε x : A) = x - ε x • (1 : A) := rfl

/-- The actual class of the zero-constant part modulo the square of the ideal. -/
def cotangentClass : A →ₗ[K] (augmentation ε).Cotangent :=
  ((augmentation ε).toCotangent.restrictScalars K).comp (center ε)

@[simp] theorem cotangentClass_ideal (x : augmentation ε) :
    cotangentClass ε x = (augmentation ε).toCotangent x := by
  apply congrArg (augmentation ε).toCotangent
  apply Subtype.ext
  change (x : A) - ε x • (1 : A) = x
  rw [show ε x = 0 from x.property, zero_smul, sub_zero]

@[simp] theorem cotangentClass_algebraMap (a : K) :
    cotangentClass ε (algebraMap K A a) = 0 := by
  have hz : center ε (algebraMap K A a) = 0 := by
    apply Subtype.ext
    simp [Algebra.smul_def]
  change (augmentation ε).toCotangent (center ε _) = 0
  rw [hz, map_zero]

 theorem cotangentClass_mul (x y : A) :
    cotangentClass ε (x*y) = ε x • cotangentClass ε y + ε y • cotangentClass ε x := by
  change ((augmentation ε).toCotangent.restrictScalars K) (center ε (x*y)) =
    ε x • ((augmentation ε).toCotangent.restrictScalars K) (center ε y) +
      ε y • ((augmentation ε).toCotangent.restrictScalars K) (center ε x)
  rw [← ((augmentation ε).toCotangent.restrictScalars K).map_smul,
    ← ((augmentation ε).toCotangent.restrictScalars K).map_smul,
    ← ((augmentation ε).toCotangent.restrictScalars K).map_add]
  apply (Ideal.toCotangent_eq _).mpr
  have hm := Ideal.mul_mem_mul (center ε x).property (center ε y).property
  rw [← pow_two] at hm
  convert hm using 1
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, center_val, map_mul, Algebra.smul_def,
    map_mul, mul_one]
  ring


/-- Generating the algebra always implies spanning its true cotangent module. -/
theorem cotangent_span_of_adjoin_eq_top {ι : Type*} (g : ι → A)
    (hg : Algebra.adjoin K (Set.range g) = ⊤) :
    Submodule.span K (Set.range fun i => cotangentClass ε (g i)) = ⊤ := by
  let V := Submodule.span K (Set.range fun i => cotangentClass ε (g i))
  have hmem : ∀ x : A, cotangentClass ε x ∈ V := by
    intro x
    have hx : x ∈ Algebra.adjoin K (Set.range g) := by rw [hg]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span (Set.mem_range_self i)
    | algebraMap a => rw [cotangentClass_algebraMap]; exact V.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact V.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [cotangentClass_mul]
      exact V.add_mem (V.smul_mem _ hy) (V.smul_mem _ hx)
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := (augmentation ε).toCotangent_surjective x
  simpa using hmem y

/-- The converse is the genuine nilpotent algebraic Nakayama theorem. -/
theorem adjoin_eq_top_of_cotangent_span {ι : Type*} (g : ι → A)
    (hnil : ∃ n : ℕ, augmentation ε ^ n = ⊥)
    (hg : Submodule.span K (Set.range fun i => cotangentClass ε (g i)) = ⊤) :
    Algebra.adjoin K (Set.range g) = ⊤ := by
  let S := Algebra.adjoin K (Set.range g)
  let M := Submodule.span K (Set.range fun i => center ε (g i))
  have hM : M.map ((augmentation ε).toCotangent.restrictScalars K) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact hg
  have hMS : ∀ x ∈ M, (x : A) ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      change g i - ε (g i) • (1 : A) ∈ S
      exact S.sub_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (S.smul_mem S.one_mem _)
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx => exact S.smul_mem hx a
  have hI : (augmentation ε).restrictScalars K ≤ S.toSubmodule := by
    apply ideal_le_subalgebra_of_square (augmentation ε) S _ hnil
    intro x hx
    have hc : (augmentation ε).toCotangent ⟨x,hx⟩ ∈
        M.map ((augmentation ε).toCotangent.restrictScalars K) := by rw [hM]; trivial
    obtain ⟨y, hy, heq⟩ := hc
    have hdiff : x - (y : A) ∈ augmentation ε ^ 2 :=
      (Ideal.toCotangent_eq _).mp heq.symm
    exact Submodule.mem_sup.mpr ⟨y, hMS y hy, x-y, hdiff, add_sub_cancel _ _⟩
  apply top_unique
  intro x _
  have hx := hI (center ε x).property
  have hc : ε x • (1 : A) ∈ S := S.smul_mem S.one_mem _
  have := S.add_mem hx hc
  simpa using this

/-- No cardinality or dimension is assumed in the generator criterion. -/
theorem adjoin_eq_top_iff_cotangent_span {ι : Type*} (g : ι → A)
    (hnil : ∃ n : ℕ, augmentation ε ^ n = ⊥) :
    Algebra.adjoin K (Set.range g) = ⊤ ↔
      Submodule.span K (Set.range fun i => cotangentClass ε (g i)) = ⊤ :=
  ⟨cotangent_span_of_adjoin_eq_top ε g, adjoin_eq_top_of_cotangent_span ε g hnil⟩


instance cotangent_finite [Module.Finite K A] : Module.Finite K (augmentation ε).Cotangent :=
  Module.Finite.of_surjective ((augmentation ε).toCotangent.restrictScalars K)
    (augmentation ε).toCotangent_surjective

/-- An arbitrary finite family of genuine algebra generators has at least the
cotangent dimension. Generators need not have zero constant coefficient. -/
theorem cotangent_finrank_le_generators {n : ℕ} (g : Fin n → A)
    (hg : Algebra.adjoin K (Set.range g) = ⊤) :
    Module.finrank K (augmentation ε).Cotangent ≤ n := by
  simpa using finrank_le_of_span_eq_top (cotangent_span_of_adjoin_eq_top ε g hg)

/-- A basis of the actual cotangent module lifts to genuine algebra generators. -/
theorem exists_generators_finrank [Module.Finite K A]
    (hnil : ∃ n : ℕ, augmentation ε ^ n = ⊥) :
    ∃ g : Fin (Module.finrank K (augmentation ε).Cotangent) → A,
      Algebra.adjoin K (Set.range g) = ⊤ := by
  let b := Module.finBasis K (augmentation ε).Cotangent
  choose g hg using fun i => (augmentation ε).toCotangent_surjective (b i)
  refine ⟨fun i => g i, adjoin_eq_top_of_cotangent_span ε _ hnil ?_⟩
  have heq : (fun i => cotangentClass ε (g i)) = b := by
    funext i
    rw [cotangentClass_ideal, hg]
  rw [heq]
  exact b.span_eq

/-- The set of actual finite algebra-generator cardinalities. -/
def generatorNumbers : Set ℕ :=
  {n | ∃ g : Fin n → A, Algebra.adjoin K (Set.range g) = ⊤}

/-- The minimum is proved to equal cotangent dimension, rather than defined to. -/
theorem isLeast_generatorNumbers [Module.Finite K A]
    (hnil : ∃ n : ℕ, augmentation ε ^ n = ⊥) :
    IsLeast (generatorNumbers (K := K) (A := A))
      (Module.finrank K (augmentation ε).Cotangent) := by
  refine ⟨exists_generators_finrank ε hnil, ?_⟩
  rintro n ⟨g, hg⟩
  exact cotangent_finrank_le_generators ε g hg


/-- Padding a genuine generating family by zeros preserves generation. -/
theorem generatorNumbers_upward {m n : ℕ} (hmn : m ≤ n)
    (hm : m ∈ generatorNumbers (K := K) (A := A)) :
    n ∈ generatorNumbers (K := K) (A := A) := by
  obtain ⟨g,hg⟩ := hm
  let f : Fin n → A := fun i => if hi : i.val < m then g ⟨i.val,hi⟩ else 0
  refine ⟨f, top_unique ?_⟩
  rw [← hg]
  apply Algebra.adjoin_mono
  rintro x ⟨i,rfl⟩
  refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hmn⟩, ?_⟩
  simp only [f, dite_eq_left i.isLt]

/-- Generation by n elements, allowing redundant generators, is equivalent to
the genuine cotangent dimension being at most n. -/
theorem mem_generatorNumbers_iff [Module.Finite K A]
    (hnil : ∃ n : ℕ, augmentation ε ^ n = ⊥) (n : ℕ) :
    n ∈ generatorNumbers (K := K) (A := A) ↔
      Module.finrank K (augmentation ε).Cotangent ≤ n := by
  constructor
  · rintro ⟨g,hg⟩
    exact cotangent_finrank_le_generators ε g hg
  · intro hn
    exact generatorNumbers_upward hn (exists_generators_finrank ε hnil)

end NilpotentGenerators
end EmbeddingDimensionStrata
