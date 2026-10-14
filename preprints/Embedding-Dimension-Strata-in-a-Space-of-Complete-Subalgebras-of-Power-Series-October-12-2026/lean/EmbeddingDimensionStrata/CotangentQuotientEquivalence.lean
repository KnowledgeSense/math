import EmbeddingDimensionStrata.NilpotentGenerators

/-! # Cotangent invariance under a quotient with kernel in the ideal square -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- The natural cotangent map is bijective when the surjection's kernel is in I². -/
theorem mapCotangent_bijective_of_ker_le_square (f : A →ₐ[K] B)
    (hf : Function.Surjective f) (I : Ideal A) (J : Ideal B)
    (hcomap : J.comap f = I) (hker : RingHom.ker f.toRingHom ≤ I ^ 2) :
    Function.Bijective (Ideal.mapCotangent I J f hcomap.ge) := by
  have hmap : I.map f = J := by rw [← hcomap, Ideal.map_comap_of_surjective f hf]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective x
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at hx
    change f (y : A) ∈ J ^ 2 at hx
    rw [← hmap, ← Ideal.map_pow] at hx
    obtain ⟨z,hz,hzy⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    have hdiff : (y : A) - z ∈ RingHom.ker f.toRingHom := by
      change f ((y : A)-z) = 0
      rw [map_sub, hzy, sub_self]
    have hm := (I ^ 2).add_mem (hker hdiff) hz
    apply (I.toCotangent_eq_zero y).mpr
    simpa only [sub_add_cancel] using hm
  · intro x
    obtain ⟨y,rfl⟩ := J.toCotangent_surjective x
    obtain ⟨z,hz⟩ := hf y
    have hzI : z ∈ I := by rw [← hcomap]; change f z ∈ J; rw [hz]; exact y.property
    refine ⟨I.toCotangent ⟨z,hzI⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    apply congrArg J.toCotangent
    exact Subtype.ext hz

/-- A linear equivalence of the actual ideal quotient modules. -/
def cotangentEquivOfKerLeSquare (f : A →ₐ[K] B)
    (hf : Function.Surjective f) (I : Ideal A) (J : Ideal B)
    (hcomap : J.comap f = I) (hker : RingHom.ker f.toRingHom ≤ I ^ 2) :
    I.Cotangent ≃ₗ[K] J.Cotangent :=
  LinearEquiv.ofBijective (Ideal.mapCotangent I J f hcomap.ge)
    (mapCotangent_bijective_of_ker_le_square f hf I J hcomap hker)

end EmbeddingDimensionStrata
