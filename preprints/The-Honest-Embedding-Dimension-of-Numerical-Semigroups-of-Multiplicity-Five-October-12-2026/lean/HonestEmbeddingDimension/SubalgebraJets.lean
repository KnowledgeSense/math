import HonestEmbeddingDimension.PlaneNormalForm

namespace HonestEmbeddingDimension

theorem formalJet_mul {N : ℕ} {f f' g g' : PowerSeries ℂ}
    (hf : formalJet N f = formalJet N f') (hg : formalJet N g = formalJet N g') :
    formalJet N (f*g) = formalJet N (f'*g') := by
  ext j
  simp only [formalJet, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hsum : kl.1+kl.2=j.val := Finset.mem_antidiagonal.mp hkl
  have hk : kl.1 < N := by omega
  have hl : kl.2 < N := by omega
  rw [show PowerSeries.coeff kl.1 f=PowerSeries.coeff kl.1 f' from congrFun hf ⟨kl.1,hk⟩,
    show PowerSeries.coeff kl.2 g=PowerSeries.coeff kl.2 g' from congrFun hg ⟨kl.2,hl⟩]

theorem formalJet_eq_zero_iff {N : ℕ} (f : PowerSeries ℂ) :
    formalJet N f = formalJet N 0 ↔ (N : ℕ∞) ≤ f.order := by
  constructor
  · intro h
    apply PowerSeries.nat_le_order
    intro j hj
    simpa [formalJet] using congrFun h ⟨j,hj⟩
  · intro h
    ext j
    have hz := PowerSeries.coeff_of_lt_order (φ := f) j
      (lt_of_lt_of_le (by exact_mod_cast j.isLt) h)
    simpa [formalJet] using hz

/-- Finite polynomial substitution respects actual subalgebra-valued coordinate jets. -/
theorem polynomial_jet_mod_subalgebra {d : ℕ} (B : Subalgebra ℂ (PowerSeries ℂ))
    (f : Fin d → PowerSeries ℂ) (N : ℕ)
    (hf : ∀ i, ∃ g ∈ B, formalJet N (f i) = formalJet N g)
    (P : MvPolynomial (Fin d) ℂ) :
    ∃ g ∈ B, formalJet N (MvPolynomial.aeval f P) = formalJet N g := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨PowerSeries.C c,B.algebraMap_mem c,by simp⟩
  | add P Q hP hQ =>
    obtain ⟨g,hg,he⟩ := hP
    obtain ⟨h,hh,hhj⟩ := hQ
    refine ⟨g+h,B.add_mem hg hh,?_⟩
    ext j
    have h1 := congrFun he j
    have h2 := congrFun hhj j
    simpa only [formalJet,map_add] using congrArg₂ (fun x y : ℂ => x+y) h1 h2
  | mul_X P i hP =>
    obtain ⟨g,hg,he⟩ := hP
    obtain ⟨h,hh,hhj⟩ := hf i
    refine ⟨g*h,B.mul_mem hg hh,?_⟩
    simpa only [map_mul,MvPolynomial.aeval_X] using formalJet_mul he hhj

/-- Every low value belongs to the subalgebra when all coordinate jets do. -/
theorem low_value_mem_subalgebra {d : ℕ} (B : Subalgebra ℂ (PowerSeries ℂ))
    (f : Fin d → PowerSeries ℂ) (N n : ℕ) (hn : n < N)
    (hf : ∀ i, ∃ g ∈ B, formalJet N (f i) = formalJet N g)
    (hv : n ∈ polynomialValues f) : n ∈ subalgebraValues B := by
  obtain ⟨P,hP⟩ := hv
  obtain ⟨g,hg,he⟩ := polynomial_jet_mod_subalgebra B f N hf P
  exact ⟨g,hg,(order_eq_of_jet_eq he hn).mp hP⟩

end HonestEmbeddingDimension
