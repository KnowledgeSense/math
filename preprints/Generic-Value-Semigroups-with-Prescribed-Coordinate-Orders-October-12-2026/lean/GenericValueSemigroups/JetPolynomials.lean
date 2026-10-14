import GenericValueSemigroups.ExponentialWitness

namespace GenericValueSemigroups
open Finset

/-- Equality of all coefficients below the jet bound. -/
def SameJet {R : Type*} [Semiring R] (N : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < N, PowerSeries.coeff n f = PowerSeries.coeff n g

theorem SameJet.mul {R : Type*} [Semiring R] {N : ℕ} {f g f' g' : PowerSeries R}
    (hf : SameJet N f f') (hg : SameJet N g g') : SameJet N (f*g) (f'*g') := by
  intro n hn
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_antidiagonal.mp ha
  rw [hf a.1 (by omega), hg a.2 (by omega)]

theorem SameJet.pow {R : Type*} [Semiring R] {N : ℕ} {f g : PowerSeries R}
    (h : SameJet N f g) (k : ℕ) : SameJet N (f^k) (g^k) := by
  induction k with
  | zero => intro n hn; simp
  | succ k ih => simpa only [pow_succ] using ih.mul h

theorem SameJet.prod {R ι : Type*} [CommSemiring R] {N : ℕ}
    (S : Finset ι) (f g : ι → PowerSeries R) (h : ∀ i ∈ S, SameJet N (f i) (g i)) :
    SameJet N (∏ i ∈ S, f i) (∏ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro n hn; simp
  | @insert i S hi ih =>
    simpa only [Finset.prod_insert hi] using
      (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Variables represent precisely the higher coefficients with indices 1,...,N−1. -/
abbrev JetVariable (d N : ℕ) := Fin d × Fin (N-1)

noncomputable def universalCoordinate {d : ℕ} (r : Fin d → ℕ) (N : ℕ) (i : Fin d) :
    PowerSeries (MvPolynomial (JetVariable d N) ℤ) :=
  PowerSeries.mk fun n => if h : r i < n ∧ n-r i < N then
    MvPolynomial.X (i, ⟨n-r i-1, by omega⟩) else if n=r i then 1 else 0

noncomputable def universalMonomial {d : ℕ} (r : Fin d → ℕ) (N : ℕ) (α : Fin d → ℕ) :
    PowerSeries (MvPolynomial (JetVariable d N) ℤ) :=
  ∏ i, universalCoordinate r N i ^ α i

noncomputable def jetAssignment {R : Type*} [CommRing R] {d : ℕ}
    (f : Fin d → PowerSeries R) (r : Fin d → ℕ) (N : ℕ) : JetVariable d N → R :=
  fun v => PowerSeries.coeff (r v.1 + v.2.val + 1) (f v.1)

noncomputable def jetEvaluation {R : Type*} [CommRing R] {d N : ℕ}
    (a : JetVariable d N → R) : MvPolynomial (JetVariable d N) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) a

theorem universalCoordinate_jet {R : Type*} [CommRing R] {d : ℕ}
    (f : Fin d → PowerSeries R) (r : Fin d → ℕ) (N : ℕ)
    (hzero : ∀ i n, n < r i → PowerSeries.coeff n (f i) = 0)
    (hlead : ∀ i, PowerSeries.coeff (r i) (f i) = 1) (i : Fin d) :
    SameJet N (PowerSeries.map (jetEvaluation (jetAssignment f r N))
      (universalCoordinate r N i)) (f i) := by
  intro n hn
  simp only [PowerSeries.coeff_map, universalCoordinate, PowerSeries.coeff_mk]
  by_cases h : r i < n
  · have hbound : n-r i < N := by omega
    simp only [dite_eq_left (show r i < n ∧ n-r i < N from ⟨h,hbound⟩), jetEvaluation, MvPolynomial.eval₂Hom_X', jetAssignment]
    rw [show r i + (n-r i-1)+1 = n by omega]
  · rw [dite_eq_right (by tauto)]
    by_cases he : n=r i
    · simp [he, hlead]
    · have hlt : n < r i := by omega
      simp [he, hzero i n hlt]

theorem universalMonomial_jet {R : Type*} [CommRing R] {d : ℕ}
    (f : Fin d → PowerSeries R) (r : Fin d → ℕ) (N : ℕ)
    (hzero : ∀ i n, n < r i → PowerSeries.coeff n (f i) = 0)
    (hlead : ∀ i, PowerSeries.coeff (r i) (f i) = 1) (α : Fin d → ℕ) :
    SameJet N (PowerSeries.map (jetEvaluation (jetAssignment f r N))
      (universalMonomial r N α)) (∏ i, f i ^ α i) := by
  simp only [universalMonomial, map_prod, map_pow]
  exact SameJet.prod Finset.univ _ _ (fun i _ => (universalCoordinate_jet f r N hzero hlead i).pow (α i))

/-- The actual integer-coefficient polynomial in a row of a monomial jet. -/
noncomputable def jetCoefficientPolynomial {d : ℕ} (r : Fin d → ℕ) (N : ℕ)
    (α : Fin d → ℕ) (u : ℕ) : MvPolynomial (JetVariable d N) ℤ :=
  PowerSeries.coeff u (universalMonomial r N α)

theorem jetCoefficientPolynomial_eval {R : Type*} [CommRing R] {d : ℕ}
    (f : Fin d → PowerSeries R) (r : Fin d → ℕ) (N : ℕ)
    (hzero : ∀ i n, n < r i → PowerSeries.coeff n (f i) = 0)
    (hlead : ∀ i, PowerSeries.coeff (r i) (f i) = 1)
    (α : Fin d → ℕ) (u : ℕ) (hu : u < N) :
    jetEvaluation (jetAssignment f r N) (jetCoefficientPolynomial r N α u) =
      PowerSeries.coeff u (∏ i, f i ^ α i) := by
  exact (universalMonomial_jet f r N hzero hlead α u hu)

noncomputable def jetMinorPolynomial {d q : ℕ} (r : Fin d → ℕ) (N : ℕ)
    (α : Fin q → Fin d → ℕ) (rows : Fin q → Fin N) :
    MvPolynomial (JetVariable d N) ℤ :=
  (Matrix.of fun i j => jetCoefficientPolynomial r N (α j) (rows i).val).det

theorem jetMinorPolynomial_eval {R : Type*} [CommRing R] {d q : ℕ}
    (f : Fin d → PowerSeries R) (r : Fin d → ℕ) (N : ℕ)
    (hzero : ∀ i n, n < r i → PowerSeries.coeff n (f i) = 0)
    (hlead : ∀ i, PowerSeries.coeff (r i) (f i) = 1)
    (α : Fin q → Fin d → ℕ) (rows : Fin q → Fin N) :
    jetEvaluation (jetAssignment f r N) (jetMinorPolynomial r N α rows) =
      (Matrix.of fun i j => PowerSeries.coeff (rows i).val (∏ k, f k ^ α j k)).det := by
  rw [jetMinorPolynomial, RingHom.map_det]
  congr 1
  ext i j
  exact jetCoefficientPolynomial_eval f r N hzero hlead (α j) (rows i).val (rows i).isLt

theorem jetMinorPolynomial_exponential_eval {d q N : ℕ} (r : Fin d → ℕ)
    (node : Fin d → ℝ) (α : Fin q → Fin d → ℕ)
    (shifts rows : Fin q → Fin N) (hw : ∀ j, ∑ i, α j i*r i = (shifts j).val) :
    jetEvaluation (jetAssignment (fun i => exponentialCoordinate (r i) (node i)) r N)
      (jetMinorPolynomial r N α rows) =
      ((exponentialColumns shifts (fun j => ∑ i, (α j i : ℝ)*node i)).submatrix rows id).det := by
  rw [jetMinorPolynomial_eval _ r N
    (fun i n hn => coeff_exponentialCoordinate_below (r i) (node i) n hn)
    (fun i => coeff_exponentialCoordinate_leading (r i) (node i))]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, exponentialColumns,
    exponentialCoordinate_monomial, hw, coeff_exponentialCoordinate_real, exponentialMatrix]
  rfl

theorem jetMinorPolynomial_ne_zero {d q N : ℕ} (r : Fin d → ℕ)
    (node : Fin d → ℝ) (α : Fin (q+1) → Fin d → ℕ)
    (shifts rows : Fin (q+1) → Fin N) (hw : ∀ j, ∑ i, α j i*r i = (shifts j).val)
    (ha : Monotone shifts) (hnode : StrictMono (fun j => ∑ i, (α j i : ℝ)*node i))
    (hzero : ∑ i, (α 0 i : ℝ)*node i = 0) (hr : StrictMono rows)
    (hfirst : rows 0 = shifts 0) (hle : ∀ j, shifts j ≤ rows j) :
    jetMinorPolynomial r N α rows ≠ 0 := by
  have hp := exponentialColumns_minor_zero_first shifts
    (fun j => ∑ i, (α j i : ℝ)*node i) ha hnode hzero rows hr hfirst hle
  rw [← jetMinorPolynomial_exponential_eval r node α shifts rows hw] at hp
  intro he
  rw [he, map_zero] at hp
  exact (lt_irrefl 0) hp

noncomputable def familyFromJet {R : Type*} [CommRing R] {d N : ℕ}
    (r : Fin d → ℕ) (a : JetVariable d N → R) (i : Fin d) : PowerSeries R :=
  PowerSeries.map (jetEvaluation a) (universalCoordinate r N i)

theorem familyFromJet_below {R : Type*} [CommRing R] {d N : ℕ}
    (r : Fin d → ℕ) (a : JetVariable d N → R) (i : Fin d) (n : ℕ) (hn : n < r i) :
    PowerSeries.coeff n (familyFromJet r a i) = 0 := by
  simp [familyFromJet, PowerSeries.coeff_map, universalCoordinate, PowerSeries.coeff_mk,
    show ¬r i < n from Nat.not_lt.mpr (Nat.le_of_lt hn), ne_of_lt hn]

@[simp] theorem familyFromJet_leading {R : Type*} [CommRing R] {d N : ℕ}
    (r : Fin d → ℕ) (a : JetVariable d N → R) (i : Fin d) :
    PowerSeries.coeff (r i) (familyFromJet r a i) = 1 := by
  simp [familyFromJet, PowerSeries.coeff_map, universalCoordinate, PowerSeries.coeff_mk]

theorem familyFromJet_order {R : Type*} [CommRing R] [Nontrivial R] {d N : ℕ}
    (r : Fin d → ℕ) (a : JetVariable d N → R) (i : Fin d) :
    PowerSeries.order (familyFromJet r a i) = r i := by
  apply PowerSeries.order_eq_nat.mpr
  exact ⟨by simp, fun n hn => familyFromJet_below r a i n hn⟩

@[simp] theorem jetAssignment_familyFromJet {R : Type*} [CommRing R] {d N : ℕ}
    (r : Fin d → ℕ) (a : JetVariable d N → R) :
    jetAssignment (familyFromJet r a) r N = a := by
  funext v
  rcases v with ⟨i,k⟩
  have h : r i < r i+k.val+1 ∧ r i+k.val+1-r i < N := by have := k.isLt; omega
  simp only [jetAssignment, familyFromJet, PowerSeries.coeff_map, universalCoordinate,
    PowerSeries.coeff_mk, dite_eq_left h, jetEvaluation, MvPolynomial.eval₂Hom_X']
  congr 2
  apply Fin.ext
  change r i+k.val+1-r i-1 = k.val
  omega

end GenericValueSemigroups
