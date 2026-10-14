import HonestEmbeddingDimension.SubalgebraJets

namespace HonestEmbeddingDimension

noncomputable def parameterCombination {q : ℕ} (m : ℕ) (hm : m ≠ 0)
    (B : Fin q → PowerSeries ℂ) (u : Fin q → PowerSeries ℂ) : PowerSeries ℂ :=
  ∑ i, PowerSeries.expand m hm (u i) * B i

def InParameterJetSpan {q : ℕ} (m : ℕ) (hm : m ≠ 0)
    (B : Fin q → PowerSeries ℂ) (N : ℕ) (f : PowerSeries ℂ) : Prop :=
  ∃ u, formalJet N f = formalJet N (parameterCombination m hm B u)

theorem InParameterJetSpan.congr {q m N : ℕ} {hm : m ≠ 0} {B : Fin q → PowerSeries ℂ}
    {f g : PowerSeries ℂ} (hf : InParameterJetSpan m hm B N f)
    (h : formalJet N g = formalJet N f) : InParameterJetSpan m hm B N g := by
  obtain ⟨u,hu⟩ := hf
  exact ⟨u,h.trans hu⟩

theorem parameterJetSpan_basis {q m N : ℕ} (hm : m ≠ 0) (B : Fin q → PowerSeries ℂ)
    (i : Fin q) : InParameterJetSpan m hm B N (B i) := by
  classical
  refine ⟨Pi.single i 1,?_⟩
  simp [parameterCombination,Pi.single_apply,apply_ite]

theorem parameterJetSpan_zero {q m N : ℕ} (hm : m ≠ 0) (B : Fin q → PowerSeries ℂ) :
    InParameterJetSpan m hm B N 0 := by
  refine ⟨0,?_⟩
  simp [parameterCombination]

theorem InParameterJetSpan.add {q m N : ℕ} {hm : m ≠ 0} {B : Fin q → PowerSeries ℂ}
    {f g : PowerSeries ℂ} (hf : InParameterJetSpan m hm B N f)
    (hg : InParameterJetSpan m hm B N g) : InParameterJetSpan m hm B N (f+g) := by
  obtain ⟨u,hu⟩ := hf
  obtain ⟨v,hv⟩ := hg
  refine ⟨u+v,?_⟩
  ext j
  have h1 := congrFun hu j
  have h2 := congrFun hv j
  simp only [formalJet,map_add] at h1 h2 ⊢
  rw [h1,h2]
  simp [parameterCombination,Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]

theorem parameterJetSpan_sum {q m N : ℕ} {hm : m ≠ 0} {B : Fin q → PowerSeries ℂ}
    {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, InParameterJetSpan m hm B N (f i)) :
    InParameterJetSpan m hm B N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using parameterJetSpan_zero hm B
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih (by
      intro i hi; exact hf i (Finset.mem_insert_of_mem hi)))

theorem InParameterJetSpan.parameter_mul {q m N : ℕ} {hm : m ≠ 0} {B : Fin q → PowerSeries ℂ}
    {f : PowerSeries ℂ} (hf : InParameterJetSpan m hm B N f) (u : PowerSeries ℂ) :
    InParameterJetSpan m hm B N (PowerSeries.expand m hm u * f) := by
  obtain ⟨v,hv⟩ := hf
  refine ⟨fun i => u*v i,?_⟩
  have he := formalJet_mul (f := PowerSeries.expand m hm u) rfl hv
  apply he.trans
  congr 1
  simp [parameterCombination,Finset.mul_sum,map_mul,mul_assoc]

/-- Closure under a coordinate follows from its checked products with the basis elements. -/
theorem InParameterJetSpan.mul_of_basis {q m N : ℕ} {hm : m ≠ 0} {B : Fin q → PowerSeries ℂ}
    {f g : PowerSeries ℂ} (hf : InParameterJetSpan m hm B N f)
    (hg : ∀ i, InParameterJetSpan m hm B N (B i*g)) :
    InParameterJetSpan m hm B N (f*g) := by
  obtain ⟨u,hu⟩ := hf
  have he := formalJet_mul hu (g := g) rfl
  apply InParameterJetSpan.congr _ he
  have hs := parameterJetSpan_sum Finset.univ
    (fun i => PowerSeries.expand m hm (u i) * (B i*g))
    (by intro i _; exact (hg i).parameter_mul (u i))
  simpa [parameterCombination,Finset.sum_mul,mul_assoc] using hs

/-- A finite multiplication certificate controls every actual polynomial jet. -/
theorem polynomial_jet_of_parameter_basis {d q m N : ℕ} (hm : m ≠ 0)
    (f : Fin d → PowerSeries ℂ) (B : Fin q → PowerSeries ℂ)
    (e : Fin q) (he : B e = 1)
    (hmul : ∀ i j, InParameterJetSpan m hm B N (B j*f i))
    (P : MvPolynomial (Fin d) ℂ) :
    InParameterJetSpan m hm B N (MvPolynomial.aeval f P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h := (parameterJetSpan_basis (N := N) hm B e).parameter_mul (PowerSeries.C c)
    simpa [he,PowerSeries.expand_C] using h
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP => simpa using hP.mul_of_basis (hmul i)

theorem parameterJetSpan_of_order_ge {q m N : ℕ} (hm : m ≠ 0) (B : Fin q → PowerSeries ℂ)
    (f : PowerSeries ℂ) (hf : (N : ℕ∞) ≤ f.order) : InParameterJetSpan m hm B N f :=
  (parameterJetSpan_zero hm B).congr ((formalJet_eq_zero_iff f).mpr hf)

end HonestEmbeddingDimension
