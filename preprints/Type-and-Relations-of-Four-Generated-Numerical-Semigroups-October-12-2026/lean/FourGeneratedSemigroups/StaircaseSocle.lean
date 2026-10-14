import FourGeneratedSemigroups.StaircaseAlgebra

noncomputable section
namespace FourGeneratedSemigroups

variable (K : Type*) [Field K] {S : NumericalSemigroup} (G : FourGenerated S)

/-- The socle of the actual Artinian monomial quotient, annihilated by all variables. -/
def staircaseSocle : Submodule K (MvPolynomial (Fin 4) K ⧸ staircaseIdeal K G) where
  carrier := {q | ∀ i : Fin 4, q*Ideal.Quotient.mk _ (MvPolynomial.X i)=0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i; simp [add_mul,ha i,hb i]
  smul_mem' := by intro a b hb i; simp [smul_mul_assoc,hb i]

lemma monomial_mem_staircaseIdeal_iff (a : Factorization) :
    MvPolynomial.monomial a (1:K)∈staircaseIdeal K G ↔ a∉staircase G := by
  classical
  simp [mem_staircaseIdeal_iff,MvPolynomial.support_monomial]

lemma mul_X_mem_staircaseIdeal_iff (f : MvPolynomial (Fin 4) K) (i : Fin 4) :
    f*MvPolynomial.X i∈staircaseIdeal K G ↔
      ∀ a∈f.support,a+Finsupp.single i 1∉staircase G := by
  classical
  simp [mem_staircaseIdeal_iff,MvPolynomial.support_mul_X]

lemma monomial_mem_staircaseSocle_iff (a : Factorization) (ha : a∈staircase G) :
    Ideal.Quotient.mk (staircaseIdeal K G) (MvPolynomial.monomial a (1:K))∈
      staircaseSocle K G ↔ a∈staircaseCorners G := by
  classical
  change (∀ i : Fin 4, _=0) ↔ _
  simp only [←map_mul,Ideal.Quotient.eq_zero_iff_mem]
  simp only [mul_X_mem_staircaseIdeal_iff,MvPolynomial.support_monomial,
    one_ne_zero,ite_false,Finset.mem_singleton,forall_eq]
  constructor
  · intro h; exact ⟨ha,fun i _ => h i⟩
  · intro h i
    by_cases hi : i=0
    · subst i
      intro hh
      have hz := hh.1
      simp [ha.1] at hz
    · exact h.2 i hi

/-- Every actual staircase corner gives a genuine socle monomial. -/
noncomputable def staircaseCornerVector (a : staircaseCorners G) : staircaseSocle K G :=
  ⟨Ideal.Quotient.mk _ (MvPolynomial.monomial a.val 1),
    (monomial_mem_staircaseSocle_iff K G a.val a.property.1).mpr a.property⟩


/-- Distinct staircase corners remain linearly independent in the actual socle. -/
theorem staircaseCornerVector_linearIndependent :
    LinearIndependent K (staircaseCornerVector K G) := by
  let e : staircaseCorners G → ↥((staircase G)ᶜ)ᶜ :=
    fun a => ⟨a.val,by simpa using a.property.1⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : ↥((staircase G)ᶜ)ᶜ => x.val) hab
  have hli := (standardMonomialBasis (staircaseIdeal K G) (staircase G)ᶜ
    (mem_staircaseIdeal_iff K G)).linearIndependent.comp e he
  apply LinearIndependent.of_comp (staircaseSocle K G).subtype
  simpa only [Function.comp_def,standardMonomialBasis_apply,staircaseCornerVector,
    Submodule.subtype_apply,e] using hli


/-- No extra, nonmonomial socle vectors occur: the corner monomials span. -/
theorem staircaseCornerVector_spans :
    ⊤ ≤ Submodule.span K (Set.range (staircaseCornerVector K G)) := by
  classical
  intro q _
  obtain ⟨f,hf⟩ := Ideal.Quotient.mk_surjective q.val
  have hcorner : ∀ a∈f.support,a∈staircase G → a∈staircaseCorners G := by
    intro a ha haT
    refine ⟨haT,?_⟩
    intro i hi
    have hh := q.property i
    rw [←hf,←map_mul] at hh
    exact (mul_X_mem_staircaseIdeal_iff K G f i).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hh) a ha
  let z : staircaseSocle K G := ∑ a∈f.support,
    if h : a∈staircaseCorners G then f.coeff a • staircaseCornerVector K G ⟨a,h⟩ else 0
  have hz : z∈Submodule.span K (Set.range (staircaseCornerVector K G)) := by
    apply Submodule.sum_mem
    intro a ha
    by_cases h : a∈staircaseCorners G
    · simp only [dite_eq_left h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a,h⟩,rfl⟩)
    · simp [h]
  have hzq : z=q := by
    apply Subtype.ext
    change (∑ a∈f.support, if h : a∈staircaseCorners G then
      f.coeff a • staircaseCornerVector K G ⟨a,h⟩ else 0).val=q.val
    rw [Submodule.coe_sum]
    calc
      _ = ∑ a∈f.support, Ideal.Quotient.mk (staircaseIdeal K G)
          (MvPolynomial.monomial a (f.coeff a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : a∈staircaseCorners G
        · simp only [dite_eq_left h,Submodule.coe_smul,staircaseCornerVector]
          change (Ideal.Quotient.mkₐ K (staircaseIdeal K G)) _ =
            (Ideal.Quotient.mkₐ K (staircaseIdeal K G)) _
          congr 1
          simp [MvPolynomial.smul_monomial]
        · simp only [dite_eq_right h,Submodule.coe_zero]
          symm
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          apply (mem_staircaseIdeal_iff K G _).mpr
          intro b hb
          have hba : b=a := by
            exact Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
          subst b
          exact fun haT => h (hcorner a ha haT)
      _ = q.val := by rw [←map_sum,MvPolynomial.support_sum_monomial_coeff,hf]
  rwa [hzq] at hz

/-- The actual socle basis is indexed by the staircase corners. -/
noncomputable def staircaseSocleBasis :
    Module.Basis (staircaseCorners G) K (staircaseSocle K G) :=
  Module.Basis.mk (staircaseCornerVector_linearIndependent K G)
    (staircaseCornerVector_spans K G)


/-- The monomial quotient's socle dimension is the number of actual corners. -/
theorem finrank_staircaseSocle (hfinite : (staircase G).Finite) :
    Module.finrank K (staircaseSocle K G)=Nat.card (staircaseCorners G) := by
  have hf : (staircaseCorners G).Finite := hfinite.subset (fun _ h => h.1)
  let := hf.fintype
  simpa using Module.finrank_eq_card_basis (staircaseSocleBasis K G)

/-- The original semigroup type is bounded by the actual monomial degeneration's socle. -/
theorem type_le_finrank_staircaseSocle (hfinite : (staircase G).Finite) :
    S.type≤Module.finrank K (staircaseSocle K G) := by
  rw [finrank_staircaseSocle K G hfinite]
  exact type_le_staircaseCorners G hfinite

end FourGeneratedSemigroups
