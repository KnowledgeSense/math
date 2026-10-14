import FourGeneratedSemigroups.Definitions
import Mathlib.Data.Fintype.Card

namespace FourGeneratedSemigroups
namespace NumericalSemigroup

@[simp] theorem memInt_natCast (S : NumericalSemigroup) (n : ℕ) :
    S.memInt (n : ℤ) ↔ n ∈ S.monoid := by
  constructor
  · rintro ⟨m,h,hm⟩
    have : n=m := by omega
    simpa [this] using hm
  · intro h
    exact ⟨n,rfl,h⟩

@[simp] theorem memInt_zero (S : NumericalSemigroup) : S.memInt 0 :=
  ⟨0,rfl,S.monoid.zero_mem⟩

theorem memInt_nonneg {S : NumericalSemigroup} {z : ℤ} (h : S.memInt z) : 0 ≤ z := by
  obtain ⟨n,rfl,_⟩ := h
  omega

theorem memInt_add {S : NumericalSemigroup} {x y : ℤ}
    (hx : S.memInt x) (hy : S.memInt y) : S.memInt (x+y) := by
  obtain ⟨a,rfl,ha⟩ := hx
  obtain ⟨b,rfl,hb⟩ := hy
  exact ⟨a+b,by omega,S.monoid.add_mem ha hb⟩

/-- Cofiniteness provides a conductor bound; no generating-set assumptions are needed. -/
theorem exists_conductor (S : NumericalSemigroup) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → n ∈ S.monoid := by
  obtain ⟨b,hb⟩ := S.finite_complement.bddAbove
  refine ⟨b+1,?_⟩
  intro n hn
  by_contra h
  have hnb := hb h
  omega

/-- The Apéry set is finite for each positive semigroup member. -/
theorem finite_apery (S : NumericalSemigroup) (d : ℕ) : (S.apery d).Finite := by
  obtain ⟨c,hc⟩ := S.exists_conductor
  apply (Set.finite_Ico (0 : ℤ) (c+d : ℕ)).subset
  intro w hw
  obtain ⟨⟨n,rfl,hn⟩,hgap⟩ := hw
  constructor
  · omega
  · by_contra h
    have hcd : c+d ≤ n := by omega
    apply hgap
    exact ⟨n-d,by omega,hc (n-d) (by omega)⟩

/-- Translating by `d` identifies pseudo-Frobenius numbers with maximal Apéry elements. -/
theorem pseudoFrobenius_iff_maximalApery (S : NumericalSemigroup)
    (d : ℕ) (hd : d ∈ S.monoid) (hpos : d ≠ 0) (f : ℤ) :
    f ∈ S.pseudoFrobenius ↔ f+(d : ℤ) ∈ S.maximalApery d := by
  constructor
  · rintro ⟨hgap,hf⟩
    refine ⟨⟨hf d hd hpos,by simpa using hgap⟩,?_⟩
    intro n hn hn0 hw
    have hfn := hf n hn hn0
    apply hw.2
    have heq : (f+(d:ℤ))+(n:ℤ)-(d:ℤ)=f+(n:ℤ) := by omega
    rwa [heq]
  · rintro ⟨⟨hfd,hgap⟩,hmax⟩
    refine ⟨by simpa using hgap,?_⟩
    intro n hn hn0
    have hsum : S.memInt ((f+(d : ℤ))+(n : ℤ)) :=
      memInt_add hfd ((memInt_natCast S n).mpr hn)
    have hh := hmax n hn hn0
    by_contra hnot
    apply hh
    refine ⟨hsum,?_⟩
    have heq : (f+(d:ℤ))+(n:ℤ)-(d:ℤ)=f+(n:ℤ) := by omega
    rwa [heq]

/-- An explicit equivalence, rather than an assumed equality of the two counts. -/
noncomputable def pseudoFrobeniusEquivMaximalApery (S : NumericalSemigroup)
    (d : ℕ) (hd : d ∈ S.monoid) (hpos : d ≠ 0) :
    S.pseudoFrobenius ≃ S.maximalApery d where
  toFun f := ⟨f.val+(d : ℤ),(pseudoFrobenius_iff_maximalApery S d hd hpos f.val).mp f.property⟩
  invFun w := ⟨w.val-(d : ℤ),by
    apply (pseudoFrobenius_iff_maximalApery S d hd hpos _).mpr
    simp [w.property]⟩
  left_inv f := by ext; simp
  right_inv w := by ext; simp

theorem finite_maximalApery (S : NumericalSemigroup) (d : ℕ) :
    (S.maximalApery d).Finite :=
  (S.finite_apery d).subset (fun _ h => h.1)

theorem type_eq_card_maximalApery (S : NumericalSemigroup)
    (d : ℕ) (hd : d ∈ S.monoid) (hpos : d ≠ 0) :
    S.type = Nat.card (S.maximalApery d) :=
  Nat.card_congr (S.pseudoFrobeniusEquivMaximalApery d hd hpos)

/-- The pseudo-Frobenius set is genuinely finite, so `type` is an ordinary finite count. -/
theorem finite_pseudoFrobenius (S : NumericalSemigroup) : S.pseudoFrobenius.Finite := by
  obtain ⟨c,hc⟩ := S.exists_conductor
  let d := c+1
  have hd : d ∈ S.monoid := hc d (by dsimp [d]; omega)
  have hd0 : d ≠ 0 := by dsimp [d]; omega
  apply (S.finite_maximalApery d).of_injOn
    (f := fun f : ℤ => f+(d : ℤ))
  · intro f hf
    exact (S.pseudoFrobenius_iff_maximalApery d hd hd0 f).mp hf
  · intro f _ g _ hfg
    exact add_right_cancel hfg

end NumericalSemigroup
end FourGeneratedSemigroups
