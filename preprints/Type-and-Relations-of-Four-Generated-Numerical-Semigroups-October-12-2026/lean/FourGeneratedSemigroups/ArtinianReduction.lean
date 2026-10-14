import Mathlib.LinearAlgebra.Dimension.Finite
import FourGeneratedSemigroups.BinomialKernel
import FourGeneratedSemigroups.StaircaseCorners

noncomputable section
namespace FourGeneratedSemigroups

variable (K : Type*) [Field K] {S : NumericalSemigroup} (G : FourGenerated S)

/-- The defining ideal after the parameter corresponding to the first generator is killed. -/
def reductionIdeal : Ideal (MvPolynomial (Fin 4) K) :=
  definingIdeal K G.generators ⊔ Ideal.span {MvPolynomial.X 0}

lemma reduction_monomial_eq_of_weight (a b : Factorization)
    (h : factorizationMap G.generators a=factorizationMap G.generators b) :
    Ideal.Quotient.mk (reductionIdeal K G) (MvPolynomial.monomial a 1)=
      Ideal.Quotient.mk (reductionIdeal K G) (MvPolynomial.monomial b 1) := by
  apply Ideal.Quotient.eq.mpr
  exact (show definingIdeal K G.generators≤reductionIdeal K G from le_sup_left) ((binomial_mem_definingIdeal_iff K G.generators a b).mpr h)

/-- Every monomial whose degree is outside the Apéry set vanishes in the actual reduction. -/
theorem reduction_monomial_zero_of_not_apery (a : Factorization)
    (ha : (factorizationMap G.generators a : ℤ)∉S.apery (G.generators 0)) :
    Ideal.Quotient.mk (reductionIdeal K G) (MvPolynomial.monomial a 1)=0 := by
  have hm : S.memInt ((factorizationMap G.generators a : ℤ)-(G.generators 0 : ℤ)) := by
    by_contra hn
    exact ha ⟨(NumericalSemigroup.memInt_natCast S _).mpr (G.factorization_mem a),hn⟩
  obtain ⟨n,hn,hnS⟩ := hm
  obtain ⟨b,hb⟩ := (G.generates n).mp hnS
  have he : factorizationMap G.generators a=
      factorizationMap G.generators (Finsupp.single 0 1+b) := by
    simp only [map_add,factorizationMap_single,one_mul,hb]
    omega
  rw [reduction_monomial_eq_of_weight K G a _ he]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hx : MvPolynomial.X 0∈reductionIdeal K G :=
    (show Ideal.span {MvPolynomial.X 0}≤reductionIdeal K G from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _))
  have hh := (reductionIdeal K G).mul_mem_right (MvPolynomial.monomial b 1) hx
  simpa only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul] using hh

/-- Natural-number indexing of the actual Apéry degrees. -/
abbrev AperyDegree := {n : ℕ // (n : ℤ)∈S.apery (G.generators 0)}

/-- Group polynomial coefficients by their semigroup degree and retain Apéry degrees. -/
noncomputable def aperyCoefficientMap :
    MvPolynomial (Fin 4) K →ₗ[K] (AperyDegree G →₀ K) :=
  (Finsupp.lcomapDomain Subtype.val Subtype.val_injective).comp
    ((Polynomial.basisMonomials K).repr.toLinearMap.comp (curveMap K G.generators).toLinearMap)

@[simp] lemma aperyCoefficientMap_apply (f : MvPolynomial (Fin 4) K) (n : AperyDegree G) :
    aperyCoefficientMap K G f n=(curveMap K G.generators f).coeff n.val := rfl

lemma aperyCoefficientMap_monomial (a : Factorization) (n : AperyDegree G) :
    aperyCoefficientMap K G (MvPolynomial.monomial a 1) n =
      if factorizationMap G.generators a=n.val then 1 else 0 := by
  simp [curveMap_monomial,Polynomial.coeff_X_pow,eq_comm]


lemma aperyCoefficientMap_monomial_scalar (a : Factorization) (r : K) (n : AperyDegree G) :
    aperyCoefficientMap K G (MvPolynomial.monomial a r) n =
      if factorizationMap G.generators a=n.val then r else 0 := by
  classical
  have he : MvPolynomial.monomial a r=r • MvPolynomial.monomial a (1:K) := by
    simp [MvPolynomial.smul_monomial]
  rw [he,map_smul,Finsupp.smul_apply,aperyCoefficientMap_monomial]
  split_ifs <;> simp

lemma aperyCoefficientMap_monomial_zero (a : Factorization) (r : K)
    (ha : (factorizationMap G.generators a : ℤ)∉S.apery (G.generators 0)) :
    aperyCoefficientMap K G (MvPolynomial.monomial a r)=0 := by
  ext n
  rw [aperyCoefficientMap_monomial_scalar]
  have hn : factorizationMap G.generators a≠n.val := by
    intro he; exact ha (he.symm ▸ n.property)
  simp [hn]

lemma aperyCoefficientMap_mul_X_zero (f : MvPolynomial (Fin 4) K) :
    aperyCoefficientMap K G (f*MvPolynomial.X 0)=0 := by
  induction f using MvPolynomial.induction_on' with
  | monomial a r =>
    rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,mul_one]
    apply aperyCoefficientMap_monomial_zero
    intro h
    apply h.2
    refine ⟨factorizationMap G.generators a,?_,G.factorization_mem a⟩
    simp
  | add f g hf hg => simp [add_mul,map_add,hf,hg]

/-- Apéry coefficient extraction annihilates the actual reduction ideal. -/
theorem reductionIdeal_le_aperyCoefficientMap_ker :
    (reductionIdeal K G).restrictScalars K≤LinearMap.ker (aperyCoefficientMap K G) := by
  intro f hf
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨c,rfl⟩ := Ideal.mem_span_singleton'.mp hb
  change aperyCoefficientMap K G (a+c*MvPolynomial.X 0)=0
  rw [map_add,aperyCoefficientMap_mul_X_zero,add_zero]
  ext n
  simp only [aperyCoefficientMap_apply]
  have ha0 : curveMap K G.generators a=0 := ha
  simp [ha0]


/-- Coefficient extraction descends to the actual Artinian reduction. -/
noncomputable def reductionCoefficientMap :
    (MvPolynomial (Fin 4) K ⧸ reductionIdeal K G) →ₗ[K] (AperyDegree G →₀ K) :=
  (reductionIdeal K G).restrictScalars K |>.liftQ (aperyCoefficientMap K G)
    (reductionIdeal_le_aperyCoefficientMap_ker K G)

@[simp] lemma reductionCoefficientMap_mk (f : MvPolynomial (Fin 4) K) :
    reductionCoefficientMap K G (Ideal.Quotient.mk _ f)=aperyCoefficientMap K G f := rfl

noncomputable def aperyRepresentative (n : AperyDegree G) : Factorization :=
  Classical.choose (apery_has_bounded_factorization G (n.val : ℤ) n.property)

lemma aperyRepresentative_weight (n : AperyDegree G) :
    factorizationMap G.generators (aperyRepresentative G n)=n.val := by
  exact Int.ofNat_inj.mp
    (Classical.choose_spec (apery_has_bounded_factorization G (n.val : ℤ) n.property)).1

lemma aperyRepresentative_mem (n : AperyDegree G) : aperyRepresentative G n∈staircase G := by
  have hh := Classical.choose_spec (apery_has_bounded_factorization G (n.val : ℤ) n.property)
  exact ⟨hh.2.1,hh.2.2,by simpa only [aperyRepresentative_weight] using n.property⟩

noncomputable def reductionNormalForm :
    (AperyDegree G →₀ K) →ₗ[K] (MvPolynomial (Fin 4) K ⧸ reductionIdeal K G) :=
  (Finsupp.basisSingleOne : Module.Basis (AperyDegree G) K (AperyDegree G →₀ K)).constr K
    (fun n => Ideal.Quotient.mk _ (MvPolynomial.monomial (aperyRepresentative G n) 1))

@[simp] lemma reductionNormalForm_single (n : AperyDegree G) :
    reductionNormalForm K G (Finsupp.single n 1)=
      Ideal.Quotient.mk _ (MvPolynomial.monomial (aperyRepresentative G n) 1) := by
  exact Module.Basis.constr_basis _ _ _ n

lemma aperyCoefficientMap_monomial_single (a : Factorization)
    (ha : (factorizationMap G.generators a : ℤ)∈S.apery (G.generators 0)) :
    aperyCoefficientMap K G (MvPolynomial.monomial a 1)=
      Finsupp.single ⟨factorizationMap G.generators a,ha⟩ 1 := by
  classical
  ext n
  simp [Finsupp.single_apply,Subtype.ext_iff,eq_comm]

lemma reductionNormalForm_aperyCoefficientMap :
    (reductionNormalForm K G).comp (aperyCoefficientMap K G)=
      (Ideal.Quotient.mkₐ K (reductionIdeal K G)).toLinearMap := by
  apply (MvPolynomial.basisMonomials (Fin 4) K).ext
  intro a
  simp only [LinearMap.comp_apply,MvPolynomial.coe_basisMonomials,AlgHom.toLinearMap_apply]
  by_cases ha : (factorizationMap G.generators a : ℤ)∈S.apery (G.generators 0)
  · rw [aperyCoefficientMap_monomial_single K G a ha,reductionNormalForm_single]
    exact reduction_monomial_eq_of_weight K G _ _ (aperyRepresentative_weight G _)
  · rw [aperyCoefficientMap_monomial_zero K G a 1 ha,map_zero]
    exact (reduction_monomial_zero_of_not_apery K G a ha).symm

lemma reductionCoefficientMap_normalForm :
    (reductionCoefficientMap K G).comp (reductionNormalForm K G)=LinearMap.id := by
  apply (Finsupp.basisSingleOne : Module.Basis (AperyDegree G) K (AperyDegree G →₀ K)).ext
  intro n
  simp only [LinearMap.comp_apply,Finsupp.coe_basisSingleOne,reductionNormalForm_single,
    reductionCoefficientMap_mk,LinearMap.id_apply]
  ext m
  simp [aperyRepresentative_weight,
    Finsupp.single_apply,Subtype.ext_iff,eq_comm]

/-- Apéry monomials provide an explicit vector-space model of the actual reduction. -/
noncomputable def reductionEquivApery :
    (MvPolynomial (Fin 4) K ⧸ reductionIdeal K G) ≃ₗ[K] (AperyDegree G →₀ K) :=
  LinearEquiv.ofLinearMap (reductionCoefficientMap K G) (reductionNormalForm K G)
    (reductionCoefficientMap_normalForm K G) (by
      apply LinearMap.ext
      intro q
      obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective q
      exact LinearMap.congr_fun (reductionNormalForm_aperyCoefficientMap K G) f)


/-- The actual reduction has an Apéry-indexed monomial basis over every field. -/
noncomputable def reductionAperyBasis :
    Module.Basis (AperyDegree G) K (MvPolynomial (Fin 4) K ⧸ reductionIdeal K G) :=
  (Finsupp.basisSingleOne : Module.Basis (AperyDegree G) K (AperyDegree G →₀ K)).map
    (reductionEquivApery K G).symm

@[simp] lemma reductionAperyBasis_apply (n : AperyDegree G) :
    reductionAperyBasis K G n=
      Ideal.Quotient.mk _ (MvPolynomial.monomial (aperyRepresentative G n) 1) := by
  exact reductionNormalForm_single K G n

noncomputable def aperyDegreeEquiv : AperyDegree G ≃ S.apery (G.generators 0) :=
  Equiv.ofBijective (fun n => ⟨(n.val : ℤ),n.property⟩) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact Int.ofNat_inj.mp (congrArg Subtype.val hab)
    · intro w
      obtain ⟨n,hn,hnS⟩ := w.property.1
      refine ⟨⟨n,hn ▸ w.property⟩,?_⟩
      exact Subtype.ext hn.symm)

theorem finite_aperyDegree : Finite (AperyDegree G) := by
  let := (S.finite_apery (G.generators 0)).to_subtype
  exact Finite.of_equiv _ (aperyDegreeEquiv G).symm

theorem finrank_reduction_eq_card_apery :
    Module.finrank K (MvPolynomial (Fin 4) K ⧸ reductionIdeal K G)=
      Nat.card (S.apery (G.generators 0)) := by
  let := finite_aperyDegree G
  let := Fintype.ofFinite (AperyDegree G)
  rw [Module.finrank_eq_card_basis (reductionAperyBasis K G)]
  exact (Nat.card_eq_fintype_card).symm.trans (Nat.card_congr (aperyDegreeEquiv G))

end FourGeneratedSemigroups
