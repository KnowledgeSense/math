import FourGeneratedSemigroups.CriticalRelations
import Mathlib.Data.Finset.Finsupp

noncomputable section
namespace FourGeneratedSemigroups

/-- The actual finite fiber of the factorization map. -/
def Factorizations (d : Fin 4 → ℕ) (n : ℕ) :=
  {c : Factorization // factorizationMap d c=n}

/-- Adjacency of factorizations means that their supports intersect. -/
def supportOverlap (a b : Factorization) : Prop := ∃ i,0<a i ∧ 0<b i

/-- The R-classes used to define Betti elements. -/
def FactorizationClasses (d : Fin 4 → ℕ) (n : ℕ) :=
  Quotient (Relation.EqvGen.setoid
    (fun a b : Factorizations d n => supportOverlap a.val b.val))

noncomputable def relationClassCount (d : Fin 4 → ℕ) (n : ℕ) : ℕ :=
  Nat.card (FactorizationClasses d n)

def IsBetti (d : Fin 4 → ℕ) (n : ℕ) : Prop := 2 ≤ relationClassCount d n

lemma finite_factorizations (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (n : ℕ) :
    Finite (Factorizations d n) := by
  classical
  let box := (Finset.univ : Finset (Fin 4)).finsupp (fun _ => Finset.range (n+1))
  have hs : {c : Factorization | factorizationMap d c=n} ⊆ (box : Set Factorization) := by
    intro c hc
    simp only [box,Finset.mem_coe,Finset.mem_finsupp_iff]
    refine ⟨Finset.subset_univ _,?_⟩
    intro i _
    have hi : c i*d i ≤ factorizationMap d c :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (c j*d j)) (Finset.mem_univ i)
    have hdi := hd i
    simp only [Finset.mem_range]
    change factorizationMap d c=n at hc
    nlinarith
  exact (box.finite_toSet.subset hs).to_subtype

lemma critical_supportOverlap_iff (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4)
    (c : Factorization) (hc : factorizationMap d c=criticalExponent d hd i*d i) :
    supportOverlap (Finsupp.single i (criticalExponent d hd i)) c ↔
      c=Finsupp.single i (criticalExponent d hd i) := by
  classical
  constructor
  · rintro ⟨j,hj,hcj⟩
    have hji : j=i := by
      by_contra h
      simp [Ne.symm h] at hj
    subst j
    exact (critical_factorization_dichotomy d hd i c hc).resolve_right (by omega)
  · rintro rfl
    exact ⟨i,by simpa using (criticalExponent_spec d hd i).1,
      by simpa using (criticalExponent_spec d hd i).1⟩

/-- The least pure-power relation degree is a genuine Betti element. -/
theorem criticalDegree_isBetti (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4) :
    IsBetti d (criticalExponent d hd i*d i) := by
  let n := criticalExponent d hd i*d i
  let u : Factorizations d n := ⟨Finsupp.single i (criticalExponent d hd i),by simp [n]⟩
  obtain ⟨c,hci,hc⟩ := (criticalExponent_spec d hd i).2
  let v : Factorizations d n := ⟨c,hc⟩
  have hneq : u ≠ v := by
    intro huv
    have h := congrArg (fun a : Factorizations d n => a.val i) huv
    have hp := (criticalExponent_spec d hd i).1
    simp [u,v,hci] at h
    omega
  have heqv : ¬ Relation.EqvGen
      (fun a b : Factorizations d n => supportOverlap a.val b.val) u v := by
    intro h
    have hg : ∀ a b : Factorizations d n,
        Relation.EqvGen (fun a b : Factorizations d n => supportOverlap a.val b.val) a b →
        (a=u ↔ b=u) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
        constructor
        · rintro rfl
          apply Subtype.ext
          exact (critical_supportOverlap_iff d hd i b.val b.property).mp hab
        · rintro rfl
          apply Subtype.ext
          apply (critical_supportOverlap_iff d hd i a.val a.property).mp
          obtain ⟨j,hj,hj'⟩ := hab
          exact ⟨j,hj',hj⟩
      | refl a => rfl
      | symm a b h ih => exact ih.symm
      | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2
    exact hneq ((hg u v h).mp rfl).symm
  let x : FactorizationClasses d n := Quotient.mk _ u
  let y : FactorizationClasses d n := Quotient.mk _ v
  have hxy : x ≠ y := fun h => heqv (Quotient.exact h)
  let : Finite (Factorizations d n) := finite_factorizations d hd n
  let : Finite (FactorizationClasses d n) := Quotient.finite _
  let : Nontrivial (FactorizationClasses d n) := ⟨⟨x,y,hxy⟩⟩
  change 2 ≤ Nat.card (FactorizationClasses d n)
  have hp : 0 < Nat.card (FactorizationClasses d n) := Nat.card_pos
  by_contra hh
  have he : Nat.card (FactorizationClasses d n)=1 := by omega
  have hs := (Nat.card_eq_one_iff_unique.mp he).1
  exact hxy (hs.elim x y)

end FourGeneratedSemigroups
