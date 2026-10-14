import Dowling.JointCorrectionTerms

noncomputable section
namespace Dowling
open Finset Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {X : Set (Fin n)}

/-- A genuine sum reindexing from actual admissible flats to literal zero sets. -/
theorem configuration_singleton_sum (i : Fin n) (hiX : i∈X)
    (A : Finset (Finset (Fin n))) (hA : ∀ Z∈A,i∈Z) (f : Finset (Fin n)→Polynomial ℤ) :
    (∑ p : Configuration G X, if (∀ r : Fin n,(p.val.fiber (some r)).card≤1) ∧
      p.val.fiber none∈A then f (p.val.fiber none) else 0)=∑ Z∈A,f Z := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun p _ => p.val.fiber none)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.2
  · intro p hp q hq he
    apply Subtype.ext
    rw [eq_zeroSetPartition_of_singletons p.val (Finset.mem_filter.mp hp).2.1,
      eq_zeroSetPartition_of_singletons q.val (Finset.mem_filter.mp hq).2.1,he]
  · intro Z hZ
    let p : Configuration G X := ⟨zeroSetPartition Z,zeroSetPartition_admissible_mark Z X ⟨i,hA Z hZ,hiX⟩⟩
    refine ⟨p,?_,zeroSetPartition_zero_fiber Z⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,zeroSetPartition_singletons Z,
      by simpa only [p,zeroSetPartition_zero_fiber] using hZ⟩
  · intro p hp
    rfl

/-- Summing by the actual zero-set cardinality introduces the exact binomial
multiplicity, with no EGF or unlabeled-partition convention. -/
theorem jointZeroSets_sum {R : Type*} [CommSemiring R] (i : Fin n) (f : ℕ→R) :
    (∑ Z∈univ.powerset.filter (i∈·),f Z.card)=
      ∑ r∈range (n+1),(jointZeroSets i r).card*f r := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun Z _ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ Z)))]
  simp only [Fintype.card_fin] 
  apply Finset.sum_congr rfl
  intro r hr
  have he : {Z∈univ.powerset.filter (i∈·) | Z.card=r}=jointZeroSets i r := by
    ext Z
    simp [jointZeroSets,and_comm]
  rw [he]
  have ht : ∀ Z∈jointZeroSets i r,f Z.card=f r := fun Z hZ =>
    congrArg f ((jointZeroSets_mem i r Z).mp hZ).1
  rw [Finset.sum_congr rfl ht,Finset.sum_const,nsmul_eq_mul]

end Dowling
