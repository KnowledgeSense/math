import HankelAutomaticity.BlockElimination

noncomputable section
namespace HankelAutomaticity
open Matrix
variable {R : Type*} [CommRing R]
variable {a : Type*} [Fintype a] [DecidableEq a]

def bordered (C : Matrix a a R) (b c : R) : Matrix (a ⊕ Unit) (a ⊕ Unit) R :=
  fromBlocks C (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => b) (Matrix.of fun _ _ => c)

 theorem det_bordered (C : Matrix a a R) (b c : R) :
    (bordered C b c).det = b*(bordered C 1 0).det+c*C.det := by
  let M := bordered C 1 0
  let v : a ⊕ Unit → R := fun j => if j=Sum.inr () then 1 else 0
  have he : bordered C b c = updateRow M (Sum.inr ()) (b • M (Sum.inr ()) + c • v) := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
      simp [Matrix.fromBlocks, bordered, M, v, updateRow_apply, Pi.smul_apply]
  have hv : updateRow M (Sum.inr ()) v =
      fromBlocks C (Matrix.of fun (_ : a) (_ : Unit) => (1 : R)) 0 1 := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
      simp [Matrix.fromBlocks, bordered, M, v, updateRow_apply]
  rw [he, det_updateRow_add, det_updateRow_smul, det_updateRow_smul,
    updateRow_eq_self, hv, det_fromBlocks_zero₂₁, det_one, mul_one]

/-- Rank-one perturbation identity, with no invertibility hypothesis on `C`. -/
 theorem det_constant_add (C : Matrix a a R) (z : R) :
    (C+(Matrix.of fun (_ : a) (_ : a) => z)).det=C.det-z*(bordered C 1 0).det := by
  have he : bordered C (-z) 1=
      fromBlocks C (Matrix.of fun (_ : a) (_ : Unit) => (1 : R))
        (Matrix.of fun (_ : Unit) (_ : a) => -z) 1 := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> simp [Matrix.fromBlocks, bordered]
  have hd := det_bordered C (-z) 1
  rw [he, det_fromBlocks_one₂₂] at hd
  have hm : C-(Matrix.of fun (_ : a) (_ : Unit) => (1 : R))*
      (Matrix.of fun (_ : Unit) (_ : a) => -z)=C+(Matrix.of fun (_ : a) (_ : a) => z) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hm] at hd
  rw [hd]
  ring

 theorem bordered_constant_add (C : Matrix a a R) (z : R) :
    (bordered (C+(Matrix.of fun (_ : a) (_ : a) => z)) 1 0).det=(bordered C 1 0).det := by
  have h1 := det_constant_add (C+(Matrix.of fun (_ : a) (_ : a) => z)) (1 : R)
  have h2 := det_constant_add C (z+1)
  have h3 := det_constant_add C z
  have he : C+(Matrix.of fun (_ : a) (_ : a) => z)+(Matrix.of fun (_ : a) (_ : a) => (1 : R))=C+(Matrix.of fun (_ : a) (_ : a) => z+1) := by
    ext i j
    simp [add_assoc]
  rw [he, h2, h3] at h1
  linear_combination h1

end HankelAutomaticity
