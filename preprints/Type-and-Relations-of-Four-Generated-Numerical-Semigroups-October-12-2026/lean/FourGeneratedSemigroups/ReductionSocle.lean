import FourGeneratedSemigroups.ArtinianReduction
import FourGeneratedSemigroups.AperyMaximal

noncomputable section
namespace FourGeneratedSemigroups
variable (K : Type*) [Field K] {S : NumericalSemigroup} (G : FourGenerated S)

def reductionSocle : Submodule K (MvPolynomial (Fin 4) K ⧸ reductionIdeal K G) where
  carrier := {q | ∀ i : Fin 4,q*Ideal.Quotient.mk _ (MvPolynomial.X i)=0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i; simp [add_mul,ha i,hb i]
  smul_mem' := by intro a b hb i; simp [smul_mul_assoc,hb i]

abbrev MaximalAperyDegree := {n : ℕ // (n : ℤ)∈S.maximalApery (G.generators 0)}

lemma reductionCoefficientMap_mul_X
    (q : MvPolynomial (Fin 4) K ⧸ reductionIdeal K G) (n : AperyDegree G)
    (i : Fin 4) (hi : ((n.val+G.generators i : ℕ) : ℤ)∈S.apery (G.generators 0)) :
    reductionCoefficientMap K G (q*Ideal.Quotient.mk _ (MvPolynomial.X i))
      ⟨n.val+G.generators i,hi⟩ = reductionCoefficientMap K G q n := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective q
  change (curveMap K G.generators (f*MvPolynomial.X i)).coeff (n.val+G.generators i)=
    (curveMap K G.generators f).coeff n.val
  rw [map_mul]
  simp [curveMap,Polynomial.coeff_mul_X_pow]

/-- A nonzero Apéry coefficient of a socle vector has maximal Apéry degree. -/
lemma maximal_of_socle_coefficient (q : reductionSocle K G) (n : AperyDegree G)
    (hn : reductionCoefficientMap K G q.val n≠0) :
    (n.val : ℤ)∈S.maximalApery (G.generators 0) := by
  apply (maximalApery_iff_generator_tests G _).mpr
  refine ⟨n.property,?_⟩
  intro i hi
  have hh := reductionCoefficientMap_mul_X K G q.val n i (by simpa using hi)
  rw [q.property i,map_zero] at hh
  exact hn hh.symm

lemma reduction_basis_mem_socle (n : MaximalAperyDegree G) :
    reductionAperyBasis K G ⟨n.val,n.property.1⟩∈reductionSocle K G := by
  intro i
  rw [reductionAperyBasis_apply,←map_mul]
  change Ideal.Quotient.mk _ (MvPolynomial.monomial _ 1 * MvPolynomial.X i)=0
  rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  apply reduction_monomial_zero_of_not_apery
  simpa [aperyRepresentative_weight] using
    (maximalApery_iff_generator_tests G _).mp n.property |>.2 i

noncomputable def reductionSocleVector (n : MaximalAperyDegree G) : reductionSocle K G :=
  ⟨reductionAperyBasis K G ⟨n.val,n.property.1⟩,reduction_basis_mem_socle K G n⟩

lemma reductionSocleVector_linearIndependent :
    LinearIndependent K (reductionSocleVector K G) := by
  let e : MaximalAperyDegree G → AperyDegree G := fun n => ⟨n.val,n.property.1⟩
  have he : Function.Injective e := by
    intro a b hab
    exact Subtype.ext (congrArg (fun n : AperyDegree G => n.val) hab)
  have hli := (reductionAperyBasis K G).linearIndependent.comp e he
  apply LinearIndependent.of_comp (reductionSocle K G).subtype
  exact hli


lemma reductionAperyBasis_repr
    (q : MvPolynomial (Fin 4) K ⧸ reductionIdeal K G) :
    (reductionAperyBasis K G).repr q=reductionCoefficientMap K G q := rfl

theorem reductionSocleVector_spans :
    ⊤≤Submodule.span K (Set.range (reductionSocleVector K G)) := by
  classical
  let := finite_aperyDegree G
  let := Fintype.ofFinite (AperyDegree G)
  intro q _
  let z : reductionSocle K G := ∑ n : AperyDegree G,
    if h : (n.val : ℤ)∈S.maximalApery (G.generators 0) then
      reductionCoefficientMap K G q.val n • reductionSocleVector K G ⟨n.val,h⟩ else 0
  have hz : z∈Submodule.span K (Set.range (reductionSocleVector K G)) := by
    apply Submodule.sum_mem
    intro n hn
    by_cases h : (n.val : ℤ)∈S.maximalApery (G.generators 0)
    · simp only [dite_eq_left h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n.val,h⟩,rfl⟩)
    · simp [h]
  have hzq : z=q := by
    apply Subtype.ext
    change (∑ n : AperyDegree G, if h : (n.val : ℤ)∈S.maximalApery (G.generators 0) then
      reductionCoefficientMap K G q.val n • reductionSocleVector K G ⟨n.val,h⟩ else 0).val=q.val
    rw [Submodule.coe_sum]
    calc
      _ = ∑ n : AperyDegree G,
          (reductionAperyBasis K G).repr q.val n • reductionAperyBasis K G n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [reductionAperyBasis_repr]
        by_cases h : (n.val : ℤ)∈S.maximalApery (G.generators 0)
        · simp only [dite_eq_left h,Submodule.coe_smul,reductionSocleVector]
        · have hz : reductionCoefficientMap K G q.val n=0 := by
            by_contra hh
            exact h (maximal_of_socle_coefficient K G q n hh)
          simp [h,hz]
      _ = q.val := (reductionAperyBasis K G).sum_repr q.val
  rwa [hzq] at hz

/-- The actual Artinian reduction's socle has the maximal Apéry monomial basis. -/
noncomputable def reductionSocleBasis :
    Module.Basis (MaximalAperyDegree G) K (reductionSocle K G) :=
  Module.Basis.mk (reductionSocleVector_linearIndependent K G) (reductionSocleVector_spans K G)


noncomputable def maximalAperyDegreeEquiv :
    MaximalAperyDegree G ≃ S.maximalApery (G.generators 0) :=
  Equiv.ofBijective (fun n => ⟨(n.val : ℤ),n.property⟩) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact Int.ofNat_inj.mp (congrArg Subtype.val hab)
    · intro w
      obtain ⟨n,hn,hnS⟩ := w.property.1.1
      refine ⟨⟨n,hn ▸ w.property⟩,?_⟩
      exact Subtype.ext hn.symm)

/-- Pseudo-Frobenius type equals the socle dimension of the actual Artinian reduction. -/
theorem type_eq_finrank_reductionSocle :
    S.type=Module.finrank K (reductionSocle K G) := by
  let := (S.finite_maximalApery (G.generators 0)).to_subtype
  let : Finite (MaximalAperyDegree G) :=
    Finite.of_equiv _ (maximalAperyDegreeEquiv G).symm
  let := Fintype.ofFinite (MaximalAperyDegree G)
  rw [Module.finrank_eq_card_basis (reductionSocleBasis K G),
    S.type_eq_card_maximalApery _ (G.generator_mem 0) (Nat.ne_of_gt (G.positive 0))]
  exact (Nat.card_congr (maximalAperyDegreeEquiv G)).symm.trans Nat.card_eq_fintype_card

end FourGeneratedSemigroups
