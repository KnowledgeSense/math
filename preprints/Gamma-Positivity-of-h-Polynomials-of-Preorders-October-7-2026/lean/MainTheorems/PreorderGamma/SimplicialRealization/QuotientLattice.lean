import MainTheorems.PreorderGamma.SimplicialRealization.CanonicalHall
import MainTheorems.PreorderGamma.RootLattice

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators Pointwise

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

omit [DecidableEq E] [Preorder E] in
theorem canonicalMargin_projection (z : E → ℤ) (t : ℕ) :
    rootProjection ((fun a => ((canonicalLeftMargin z t a : ℤ) : ℝ)),
      fun b => ((canonicalRightMargin z t b : ℤ) : ℝ)) = fun i => (z i : ℝ) := by
  funext i
  change (((z i).toNat : ℤ) : ℝ) - (((-z i).toNat : ℤ) : ℝ) = (z i : ℝ)
  have h : ((z i).toNat : ℤ) - ((-z i).toNat : ℤ) = z i := by omega
  exact_mod_cast h

theorem isCanonicalDegree_quotientIntegerPoint {t : ℕ} {z : E → ℤ}
    (hz : IsCanonicalDegree z t) : QuotientIntegerPoint t z := by
  obtain ⟨p⟩ := hz.2.2
  have hroot := transport_rootIntegerPoints (canonicalLeftMargin z t)
    (canonicalRightMargin z t) (canonicalLeftMargin_total z hz.1)
    (canonicalRightMargin_total z hz.2.1) p
  obtain ⟨x, hx, heq⟩ := Set.mem_smul_set.mp hroot
  apply Set.mem_smul_set.mpr
  refine ⟨rootProjection x, ?_, ?_⟩
  · rw [← rootProjection_polytope]
    exact ⟨x, hx, rfl⟩
  · have h := congrArg rootProjection heq
    rw [rootProjection.map_smul] at h
    exact h.trans (canonicalMargin_projection z t)

theorem quotientIntegerPoint_iff_isCanonicalDegree (t : ℕ) (z : E → ℤ) :
    QuotientIntegerPoint t z ↔ IsCanonicalDegree z t :=
  ⟨quotientIntegerPoint_isCanonicalDegree, isCanonicalDegree_quotientIntegerPoint⟩

theorem quotientIntegerPoint_iff_degree (t : ℕ) (z : E → ℤ) :
    QuotientIntegerPoint t z ↔ quotientLatticeDegree z ≤ t := by
  rw [quotientIntegerPoint_iff_isCanonicalDegree, isCanonicalDegree_iff]

@[simp] theorem quotientIntegerPoint_zero_iff (z : E → ℤ) :
    QuotientIntegerPoint 0 z ↔ z = 0 := by
  rw [quotientIntegerPoint_iff_degree, Nat.le_zero, quotientLatticeDegree_eq_zero_iff]

theorem quotientIntegerPoint_coordinate_bounds {t : ℕ} {z : E → ℤ}
    (hz : QuotientIntegerPoint t z) (i : E) : -(t : ℤ) ≤ z i ∧ z i ≤ t := by
  obtain ⟨hp, hn⟩ := quotientIntegerPoint_mass_bounds hz
  have hpi : (z i).toNat ≤ positiveMass z :=
    Finset.single_le_sum (f := fun j : E => (z j).toNat)
      (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  have hni : (-z i).toNat ≤ negativeMass z :=
    Finset.single_le_sum (f := fun j : E => (-z j).toNat)
      (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  constructor <;> omega

noncomputable instance finiteQuotientIntegerPoints (t : ℕ) :
    Finite {z : E → ℤ // QuotientIntegerPoint t z} := by
  let f : {z : E → ℤ // QuotientIntegerPoint t z} → E → Fin (2 * t + 1) :=
    fun z i => ⟨(z.val i + t).toNat, by
      have h := quotientIntegerPoint_coordinate_bounds z.property i
      omega⟩
  apply Finite.of_injective f
  intro z w h
  apply Subtype.ext
  funext i
  have heq := congrArg (fun q => (q i).val) h
  change (z.val i + t).toNat = (w.val i + t).toNat at heq
  have hz := quotientIntegerPoint_coordinate_bounds z.property i
  have hw := quotientIntegerPoint_coordinate_bounds w.property i
  omega

noncomputable def quotientLatticeCount (t : ℕ) : ℕ :=
  Nat.card {z : E → ℤ // QuotientIntegerPoint t z}

@[simp] theorem quotientLatticeCount_zero : quotientLatticeCount (E := E) 0 = 1 := by
  classical
  let e : {z : E → ℤ // QuotientIntegerPoint 0 z} ≃ Unit :=
    { toFun := fun _ => Unit.unit
      invFun := fun _ => ⟨0, (quotientIntegerPoint_zero_iff 0).mpr rfl⟩
      left_inv := fun z => by
        apply Subtype.ext
        exact ((quotientIntegerPoint_zero_iff z.val).mp z.property).symm
      right_inv := fun z => by cases z; rfl }
  exact (Nat.card_congr e).trans (by simp)

end ResearchMain.PreorderGamma.SimplicialRealization
