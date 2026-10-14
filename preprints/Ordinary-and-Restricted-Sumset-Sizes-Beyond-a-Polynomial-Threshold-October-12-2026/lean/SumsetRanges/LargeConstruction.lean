import SumsetRanges.SparseSet
import SumsetRanges.DenseRestricted
import SumsetRanges.RestrictedIntegerModel

open Finset Polynomial
namespace SumsetRanges

noncomputable def largeValue (h c b : ℕ) (r u : ℕ → ℕ) (x : ℕ) : ℤ :=
  (sparsePolynomial h c r u * restrictedPolynomial (denseSet (b-1) x)).coeff h

def denseIntegers (n x : ℕ) : Finset ℤ :=
  (denseSet n x).image (Nat.castAddMonoidHom ℤ)

theorem restrictedPolynomial_denseIntegers (n x : ℕ) :
    restrictedPolynomial (denseIntegers n x)=restrictedPolynomial (denseSet n x) := by
  exact restrictedPolynomial_image_injective _ (Nat.castAddMonoidHom ℤ) (by
    intro a b he
    change (a:ℤ)=(b:ℤ) at he
    exact_mod_cast he)

theorem card_denseIntegers (n x : ℕ) (hx : n≤x) : (denseIntegers n x).card=n+1 := by
  rw [denseIntegers,Finset.card_image_of_injective]
  · exact card_denseSet n x hx
  · intro a b he
    change (a:ℤ)=(b:ℤ) at he
    exact_mod_cast he

theorem denseIntegers_bounds (n x : ℕ) (hx : n≤x) :
    ∀a∈denseIntegers n x,0≤a ∧ a≤x := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  rcases Finset.mem_insert.mp hb with rfl | hb
  · simp
  · have hh := Finset.mem_range.mp hb
    exact ⟨by simp,by change (b:ℤ)≤x; exact_mod_cast (show b≤x by omega)⟩

def sparseDenseEmbedding {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    ((ι→ℤ)×ℤ) →+ ModelSpace n 0 where
  toFun v := (reindexCoordinates e v.1,v.2,0)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sparseDenseEmbedding_injective {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    Function.Injective (sparseDenseEmbedding e) := by
  intro v w he
  apply Prod.ext
  · exact reindexCoordinates_injective e (congrArg Prod.fst he)
  · exact congrArg (fun x => x.2.1) he

theorem latticeNorm_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n) (v : ι→ℤ) :
    latticeNorm (reindexCoordinates e v)=coordinateNorm v := by
  exact e.symm.sum_comp (fun i => (v i).natAbs)

/-- Every admissible large-range parameter yields an actual bounded integer set with the computed value. -/
theorem largeValue_realized (h c b x : ℕ) (r u : ℕ → ℕ) (hh : 2≤h) (hb : 2≤b)
    (hfree : nonfreeSize h r u≤c) (hu : ∀m∈Icc 2 h,1≤u m)
    (hx : b-1≤x) (hxb : x≤h*(b-2)+1) :
    ∃B : Finset ℤ,B.card=c+b ∧ (∀a∈B,0≤a ∧ a≤((c+b)^(restrictedExponent h):ℕ)) ∧
      ((restrictedSums B h).card:ℤ)=largeValue h c b r u x := by
  classical
  let ι := SparseAtom h c r u
  let A := separatedUnion (sparseSet h c r u) (denseIntegers (b-1) x)
  let n := Fintype.card ι
  let e := Fintype.equivFin ι
  let φ := sparseDenseEmbedding e
  let A' := A.image φ
  have hAc : A.card=c+b := by
    rw [card_separatedUnion _ _ (sparseDegree h c r u) (sparseDegree_points _ _ _ _),
      card_sparseSet h c r u (by omega) hfree,card_denseIntegers _ _ hx]
    omega
  have hA'c : A'.card=c+b := by
    rw [Finset.card_image_of_injective _ (sparseDenseEmbedding_injective e)]
    exact hAc
  have hn : n≤c+b := (sparseAtom_card_le h c r u (by omega) hfree hu).trans (by omega)
  have hxn : x≤h*(c+b) := by
    have he : b-2+2=b := Nat.sub_add_cancel hb
    nlinarith
  have hA' : ∀a∈A',latticeNorm a.1≤2*h-1 ∧ 0≤a.2.1 ∧ a.2.1≤(h*(c+b):ℕ) ∧
      ∀i,0≤a.2.2 i ∧ a.2.2 i≤1 := by
    intro a ha
    obtain ⟨⟨v,w⟩,hp,rfl⟩ := Finset.mem_image.mp ha
    change latticeNorm (reindexCoordinates e v)≤2*h-1 ∧ 0≤w ∧ w≤(h*(c+b):ℕ) ∧ _
    rw [latticeNorm_reindex]
    rcases (mem_separatedUnion _ _ (v,w)).mp hp with ⟨hv,rfl⟩ | ⟨rfl,hw⟩
    · refine ⟨sparseSet_norm h c r u (by omega) v hv,by omega,by positivity,?_⟩
      intro i; exact Fin.elim0 i
    · have hw' := denseIntegers_bounds (b-1) x hx w hw
      refine ⟨by simp,hw'.1,hw'.2.trans (by exact_mod_cast hxn),?_⟩
      intro i; exact Fin.elim0 i
  obtain ⟨B,hBc,hBb,hBs⟩ := restricted_integer_model h (c+b) n 0 hh (by omega) hn (by omega) A' hA'c hA'
  refine ⟨B,hBc,hBb,?_⟩
  rw [hBs h le_rfl]
  have him := card_restrictedSums_image A φ (sparseDenseEmbedding_injective e).injOn h
    (sparseDenseEmbedding_injective e).injOn
  rw [him]
  rw [←coeff_restrictedPolynomial]
  have hp : restrictedPolynomial A=sparsePolynomial h c r u*restrictedPolynomial (denseSet (b-1) x) := by
    rw [restrictedPolynomial_separatedUnion _ _ (sparseDegree h c r u) (sparseDegree_points _ _ _ _),
      restrictedPolynomial_sparseSet h c r u (by omega),restrictedPolynomial_denseIntegers]
  rw [hp]
  rfl

end SumsetRanges
