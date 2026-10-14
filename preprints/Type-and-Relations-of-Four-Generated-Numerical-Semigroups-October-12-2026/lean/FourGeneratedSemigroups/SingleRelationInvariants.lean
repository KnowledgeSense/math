import FourGeneratedSemigroups.BoundaryArithmetic
import FourGeneratedSemigroups.PresentationIdeal

noncomputable section
namespace FourGeneratedSemigroups

/-- The additive congruence of the distinguished pure-power binomial. -/
def topRelation (A : ℕ) (p : Factorization) : AddCon Factorization :=
  addConGen (fun a b => a=Finsupp.single 3 A ∧ b=p)

lemma topRelation_zero {A : ℕ} {p a b : Factorization} (hp : p 0=0)
    (h : topRelation A p a b) : a 0=b 0 := by
  change AddConGen.Rel _ a b at h
  induction h with
  | of x y h => rcases h with ⟨rfl,rfl⟩; simp [hp]
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | add _ _ ih ih' => simp only [Finsupp.add_apply,ih,ih']

lemma topRelation_third_mod {A : ℕ} {p a b : Factorization} (hp : p 3=0)
    (h : topRelation A p a b) : a 3%A=b 3%A := by
  change AddConGen.Rel _ a b at h
  induction h with
  | of x y h => rcases h with ⟨rfl,rfl⟩; simp [hp]
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | add _ _ ih ih' =>
    simp only [Finsupp.add_apply]
    rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    rw [ih,ih']

lemma topRelation_balance {A : ℕ} {p a b : Factorization} (hp : p 3=0)
    (h : topRelation A p a b) (i : Fin 4) (hi : i≠3) :
    A*a i+p i*a 3=A*b i+p i*b 3 := by
  change AddConGen.Rel _ a b at h
  induction h with
  | of x y h => rcases h with ⟨rfl,rfl⟩; simp [hp,Ne.symm hi,Nat.mul_comm]
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | add _ _ ih ih' => simp only [Finsupp.add_apply,Nat.mul_add]; omega

/-- A relation class meeting the zero-height plane has an integral number of
pure-power substitutions; both horizontal coordinates record that number. -/
lemma topRelation_plane {A : ℕ} (hA : 0<A) {p a b : Factorization}
    (hp : p 3=0) (ha : a 3=0) (h : topRelation A p a b) :
    ∃k : ℕ, b 3=k*A ∧ ∀i : Fin 4, i≠3 → a i=b i+k*p i := by
  have hm := topRelation_third_mod hp h
  rw [ha,Nat.zero_mod] at hm
  have hd : A∣b 3 := Nat.dvd_of_mod_eq_zero hm.symm
  obtain ⟨k,hk⟩ := hd
  refine ⟨k,by simpa [Nat.mul_comm] using hk,?_⟩
  intro i hi
  have hb := topRelation_balance hp h i hi
  rw [ha,Nat.mul_zero,Nat.add_zero,hk] at hb
  have he : A*a i=A*(b i+k*p i) := by nlinarith [hb]
  exact Nat.eq_of_mul_eq_mul_left hA he

lemma topRelation_cut_injective {A : ℕ} (hA : 0<A) {p a b : Factorization}
    (hp : p 3=0) (ha : a 3<A) (hb : b 3<A) (h : topRelation A p a b) : a=b := by
  have he3 : a 3=b 3 := by
    have hh := topRelation_third_mod hp h
    simpa [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using hh
  ext i
  by_cases hi : i=3
  · simpa [hi] using he3
  · have hh := topRelation_balance hp h i hi
    rw [he3] at hh
    exact Nat.eq_of_mul_eq_mul_left hA (Nat.add_right_cancel hh)

end FourGeneratedSemigroups
