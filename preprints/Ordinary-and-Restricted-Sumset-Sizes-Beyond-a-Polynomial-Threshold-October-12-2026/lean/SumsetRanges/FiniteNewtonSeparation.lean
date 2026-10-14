import SumsetRanges.NewtonSeparation

open Finset
namespace SumsetRanges

theorem finite_elementary_symmetric_eq_of_power_sums {σ τ : Type*} [Fintype σ] [Fintype τ] (N : ℕ) (f : σ → ℤ) (g : τ → ℤ)
    (hp : ∀j≤N,∑i,f i^j=∑i,g i^j) :
    ∀j≤N,MvPolynomial.aeval f (MvPolynomial.esymm σ ℤ j)=
      MvPolynomial.aeval g (MvPolynomial.esymm τ ℤ j) := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      by_cases hz : j=0
      · subst j; simp
      have hf := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℤ j)
      have hg := congrArg (MvPolynomial.aeval g) (MvPolynomial.mul_esymm_eq_sum τ ℤ j)
      simp only [map_mul,map_natCast,map_pow,map_neg,map_one,map_sum] at hf hg
      have hs : (∑a∈(Finset.antidiagonal j).filter (fun a => a.1<j),
          (-1:ℤ)^a.1*MvPolynomial.aeval f (MvPolynomial.esymm σ ℤ a.1)*
            MvPolynomial.aeval f (MvPolynomial.psum σ ℤ a.2))=
          ∑a∈(Finset.antidiagonal j).filter (fun a => a.1<j),
          (-1:ℤ)^a.1*MvPolynomial.aeval g (MvPolynomial.esymm τ ℤ a.1)*
            MvPolynomial.aeval g (MvPolynomial.psum τ ℤ a.2) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hab := (Finset.mem_filter.mp ha)
        have hsum := Finset.mem_antidiagonal.mp hab.1
        rw [ih a.1 hab.2 (by omega)]
        have hpow : MvPolynomial.aeval f (MvPolynomial.psum σ ℤ a.2)=
            MvPolynomial.aeval g (MvPolynomial.psum τ ℤ a.2) := by
          simpa [MvPolynomial.psum] using hp a.2 (by omega)
        rw [hpow]
      have he : (j:ℤ)*MvPolynomial.aeval f (MvPolynomial.esymm σ ℤ j)=
          (j:ℤ)*MvPolynomial.aeval g (MvPolynomial.esymm τ ℤ j) := by
        rw [hf,hg,hs]
      exact mul_left_cancel₀ (by exact_mod_cast hz : (j:ℤ)≠0) he

theorem finite_multiset_eq_of_power_sums {σ τ : Type*} [Fintype σ] [Fintype τ] (N : ℕ) (f : σ → ℤ) (g : τ → ℤ)
    (hσ : Fintype.card σ=N) (hτ : Fintype.card τ=N)
    (hp : ∀j≤N,∑i,f i^j=∑i,g i^j) :
    Finset.univ.val.map f=Finset.univ.val.map g := by
  classical
  have he := finite_elementary_symmetric_eq_of_power_sums N f g hp
  have hs : ∀j≤N,(Finset.univ.val.map f).esymm j=(Finset.univ.val.map g).esymm j := by
    intro j hj
    simpa only [MvPolynomial.aeval_esymm_eq_multiset_esymm] using he j hj
  have hprod : ((Finset.univ.val.map f).map fun a => Polynomial.X-Polynomial.C a).prod=
      ((Finset.univ.val.map g).map fun a => Polynomial.X-Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map,Finset.card_val,Finset.card_univ,hσ,hτ]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j (by have := Finset.mem_range.mp hj; omega)]
  have hr := congrArg Polynomial.roots hprod
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using hr

end SumsetRanges
