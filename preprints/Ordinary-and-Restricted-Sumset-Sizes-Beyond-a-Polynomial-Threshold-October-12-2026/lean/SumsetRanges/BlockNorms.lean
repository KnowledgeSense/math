import SumsetRanges.CoordinateSums

open Finset Polynomial
namespace SumsetRanges

def coordinateNorm {ι : Type*} [Fintype ι] (v : ι→ℤ) : ℕ := ∑i,(v i).natAbs

@[simp] theorem coordinateNorm_zero {ι : Type*} [Fintype ι] : coordinateNorm (0 : ι→ℤ)=0 := by
  simp [coordinateNorm]

theorem coordinateNorm_join {ι κ : Type*} [Fintype ι] [Fintype κ] (v : (ι→ℤ)×(κ→ℤ)) :
    coordinateNorm (joinCoordinates ι κ v)=coordinateNorm v.1+coordinateNorm v.2 := by
  simp [coordinateNorm,joinCoordinates,Fintype.sum_sum_type]

theorem coordinateNorm_uncurried {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι→κ→ℤ) :
    coordinateNorm (uncurriedCoordinates ι κ v)=∑i,coordinateNorm (v i) := by
  simp [coordinateNorm,uncurriedCoordinates,Fintype.sum_prod_type]

theorem copied_size_bound {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (N : α → ℕ) (hN : N 0=0) (M r : ℕ) (hA : ∀a∈A,N a≤M) :
    ∀v∈independentCopies A r,(∑i,N (v i))≤M := by
  induction r with
  | zero => simp [independentCopies]
  | succ r ih =>
      intro v hv
      obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp hv
      rcases (mem_separatedUnion A (independentCopies A r) (a,b)).mp hp with ⟨ha,rfl⟩ | ⟨rfl,hb⟩
      · simpa [prependHom,Fin.sum_univ_succ,hN] using hA a ha
      · simpa [prependHom,Fin.sum_univ_succ,hN] using ih b hb

theorem linearPoint_norm (m : ℕ) (hm : 1≤m) (a : LinearIndex m) :
    coordinateNorm (linearPoint a)≤2*m-1 := by
  rcases a with i | (_ | j)
  · simp [coordinateNorm,linearPoint,apply_ite]; omega
  · simp [coordinateNorm,linearPoint,Fintype.sum_sum_type]; omega
  · simp [coordinateNorm,linearPoint,apply_ite]; omega

theorem linearBlock_norm (m : ℕ) (hm : 1≤m) :
    ∀v∈linearBlock m,coordinateNorm v≤2*m-1 := by
  intro v hv
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
  exact linearPoint_norm m hm a

theorem sharedPoint_norm (m u : ℕ) (hm : 1≤m) (a : SharedIndex m u) :
    coordinateNorm (sharedPoint a)≤m := by
  rcases a with ⟨i,_ | j⟩
  · simp only [coordinateNorm,Fintype.sum_option,sharedPoint]
    rw [Fintype.sum_prod_type]
    simp [apply_ite]
    omega
  · simp [coordinateNorm,sharedPoint,apply_ite]
    omega

theorem sharedAtomBlock_norm (m u : ℕ) (hm : 1≤m) :
    ∀v∈sharedAtomBlock m u,coordinateNorm v≤m := by
  intro v hv
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
  exact sharedPoint_norm m u hm a

def sharedDegreeHom (m u : ℕ) : SharedLattice m u →+ ℤ where
  toFun := sharedDegree
  map_zero' := by simp [sharedDegree]
  map_add' v w := by simp [sharedDegree,Finset.sum_add_distrib,mul_add]; ring

theorem sharedDegreeHom_points (m u : ℕ) (hm : 2≤m) :
    ∀v∈sharedAtomBlock m u,sharedDegreeHom m u v=1 := by
  intro v hv
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
  exact sharedDegree_point hm a

end SumsetRanges
