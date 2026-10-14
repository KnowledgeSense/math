import Dowling.BraidBlockDefinitions
import Mathlib.Tactic

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

 theorem mem_fromBlockRoots_solution (R : Fin n → Fin n) (hR : ∀ i, R (R i)=R i)
    (hmin : ∀ i, R i ≤ i) (u : Fin n → G) (x : Fin n → Option G) :
    x ∈ (fromBlockRoots R hR hmin u).solutionSet ↔
      ∀ i, x i=gainAct G (x (R i)) ((u (R i))⁻¹*u i) := by
  rw [mem_solutionSet]
  constructor
  · intro hx i
    exact hx.2 i (R i) ((u (R i))⁻¹*u i) rfl
  · intro hx
    constructor
    · intro i hi
      cases hi
    · intro i j g hij
      have he : (R i,(u (R i))⁻¹*u i)=(j,g) := Option.some.inj hij
      cases he
      exact hx i

 theorem fromBlockRoots_le_iff (R S : Fin n → Fin n)
    (hR : ∀ i, R (R i)=R i) (hS : ∀ i, S (S i)=S i)
    (hRm : ∀ i, R i ≤ i) (hSm : ∀ i, S i ≤ i) (u : Fin n → G) :
    fromBlockRoots R hR hRm u ≤ fromBlockRoots S hS hSm u ↔
      ∀ i, S (R i)=S i := by
  constructor
  · intro h i
    have hrel : ∀ x ∈ (fromBlockRoots S hS hSm u).solutionSet,
        x i=gainAct G (x (R i)) ((u (R i))⁻¹*u i) := by
      intro x hx
      exact (mem_fromBlockRoots_solution R hR hRm u x).mp (h hx) i
    have he := ((fromBlockRoots S hS hSm u).solution_link_iff (R i) i
      ((u (R i))⁻¹*u i)).mp hrel
    rcases he with ⟨hz,_⟩ | ⟨r,a,b,hr,hi,_⟩
    · cases hz
    · have h1 := congrArg Prod.fst (Option.some.inj hr)
      have h2 := congrArg Prod.fst (Option.some.inj hi)
      exact h1.trans h2.symm
  · intro h x hx
    apply (mem_fromBlockRoots_solution R hR hRm u x).mpr
    have he := (mem_fromBlockRoots_solution S hS hSm u x).mp hx
    intro i
    rw [he i,he (R i),gainAct_mul,h i]
    congr 1
    group

 theorem braidLift_le_braidTop (p : GainPartition Unit n) (u : Fin (n+1) → G) :
    p.braidLift u ≤ braidTop u := by
  apply (fromBlockRoots_le_iff _ _ _ _ _ _ _).mpr
  intro _
  rfl

end Dowling.GainPartition
