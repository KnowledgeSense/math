import EmbeddingDimensionStrata.TriangularEquations

/-! # The genuine parameter variety is a polynomial graph over 57 coordinates -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata
section Ring
variable {A : Type*} [CommRing A]

def evaluateCoordinatePolynomial (p : NormalCoordinate → A) : CoordinatePolynomial →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) p

def initialFreePoint (q : FreeCoordinate → A) (j : NormalCoordinate) : A :=
  if h : j ∉ eliminatedCoordinates then q ⟨j,h⟩ else 0

/-- Successive substitution of the five proved triangular equations. -/
def solveFreePoint (q : FreeCoordinate → A) : ℕ → NormalCoordinate → A
  | 0 => initialFreePoint q
  | n+1 => if hn : n < 5 then
      Function.update (solveFreePoint q n) (solvedCoordinate ⟨n,hn⟩)
        (evaluateCoordinatePolynomial (solveFreePoint q n) (solutionRemainder ⟨n,hn⟩))
    else solveFreePoint q n

theorem evaluate_remainder_update (p : NormalCoordinate → A) (i j : Fin 5)
    (hij : i ≤ j) (a : A) :
    evaluateCoordinatePolynomial (Function.update p (solvedCoordinate j) a) (solutionRemainder i) =
      evaluateCoordinatePolynomial p (solutionRemainder i) := by
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro k hk _
  apply Function.update_of_ne
  intro h
  subst k
  exact solutionRemainder_not_mem_later i j hij hk

theorem solveFreePoint_free (q : FreeCoordinate → A) (N : ℕ) (j : FreeCoordinate) :
    solveFreePoint q N j.val = q j := by
  induction N with
  | zero => exact dite_eq_left j.property
  | succ n ih =>
    rw [solveFreePoint]
    split_ifs with hn
    · rw [Function.update_of_ne]
      · exact ih
      · intro h
        apply j.property
        exact (mem_eliminatedCoordinates_iff j.val).mpr ⟨⟨n,hn⟩,h.symm⟩
    · exact ih

/-- Already solved equations remain solved throughout the substitution. -/
theorem solveFreePoint_equations (q : FreeCoordinate → A) (N : ℕ) (i : Fin 5)
    (hiN : i.val < N) :
    solveFreePoint q N (solvedCoordinate i) =
      evaluateCoordinatePolynomial (solveFreePoint q N) (solutionRemainder i) := by
  induction N with
  | zero => omega
  | succ n ih =>
    rw [solveFreePoint]
    split_ifs with hn
    · have hin : i ≤ (⟨n,hn⟩ : Fin 5) := by change i.val ≤ n; omega
      rw [evaluate_remainder_update _ i ⟨n,hn⟩ hin]
      by_cases heq : i = (⟨n,hn⟩ : Fin 5)
      · subst i
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne (fun h => heq (solvedCoordinate_injective h))]
        apply ih
        have hv : i.val ≠ n := by intro h; exact heq (Fin.ext h)
        omega
    · apply ih
      omega

/-- Agreement on free coordinates and already solved coordinates suffices
for evaluating the next triangular polynomial. -/
theorem evaluate_remainder_eq_of_earlier (p r : NormalCoordinate → A) (i : Fin 5)
    (hfree : ∀ j : FreeCoordinate, p j.val = r j.val)
    (hearlier : ∀ j : Fin 5, j < i → p (solvedCoordinate j) = r (solvedCoordinate j)) :
    evaluateCoordinatePolynomial p (solutionRemainder i) =
      evaluateCoordinatePolynomial r (solutionRemainder i) := by
  classical
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro k hk _
  by_cases hfreeK : k ∉ eliminatedCoordinates
  · exact hfree ⟨k,hfreeK⟩
  · obtain ⟨j,rfl⟩ := (mem_eliminatedCoordinates_iff k).mp (by simpa using hfreeK)
    apply hearlier j
    by_contra hji
    exact solutionRemainder_not_mem_later i j (le_of_not_gt hji) hk

/-- The triangular solution is the unique solution with the specified free
coordinates. -/
theorem solveFreePoint_unique (p : NormalCoordinate → A)
    (hp : ∀ i : Fin 5, p (solvedCoordinate i) =
      evaluateCoordinatePolynomial p (solutionRemainder i)) :
    solveFreePoint (fun j : FreeCoordinate => p j.val) 5 = p := by
  have hagree : ∀ N : ℕ, ∀ i : Fin 5, i.val < N →
      solveFreePoint (fun j : FreeCoordinate => p j.val) N (solvedCoordinate i) = p (solvedCoordinate i) := by
    intro N
    induction N with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hin
      rw [solveFreePoint]
      split_ifs with hn
      · by_cases heq : i = (⟨n,hn⟩ : Fin 5)
        · subst i
          rw [Function.update_self, hp]
          apply evaluate_remainder_eq_of_earlier
          · intro j
            exact solveFreePoint_free _ n j
          · intro j hj
            exact ih j hj
        · rw [Function.update_of_ne (fun h => heq (solvedCoordinate_injective h))]
          apply ih
          have hv : i.val ≠ n := by intro h; exact heq (Fin.ext h)
          omega
      · apply ih
        omega
  funext j
  by_cases hj : j ∉ eliminatedCoordinates
  · exact solveFreePoint_free _ 5 ⟨j,hj⟩
  · obtain ⟨i,rfl⟩ := (mem_eliminatedCoordinates_iff j).mp (by simpa using hj)
    exact hagree 5 i i.isLt

theorem definingEquations_iff_fixed (p : NormalCoordinate → A) :
    (∀ i : Fin 5, definingEquation p i = 0) ↔
      ∀ i : Fin 5, p (solvedCoordinate i) =
        evaluateCoordinatePolynomial p (solutionRemainder i) := by
  have heq (i : Fin 5) : definingEquation p (solvingOrder i) =
      -p (solvedCoordinate i) + evaluateCoordinatePolynomial p (solutionRemainder i) := by
    rw [← eval_definingPolynomial]
    change evaluateCoordinatePolynomial p (solvedPolynomial i) = _
    rw [solvedPolynomial_eq, map_add, map_neg]
    simp only [evaluateCoordinatePolynomial, MvPolynomial.eval₂Hom_X']
  constructor
  · intro hp i
    have hh := hp (solvingOrder i)
    rw [heq, neg_add_eq_zero] at hh
    exact hh
  · intro hp i
    obtain ⟨j,rfl⟩ := solvingOrder.surjective i
    rw [heq, ← hp j, neg_add_cancel]

/-- Integer-coefficient evaluation commutes with every coefficient-ring map. -/
theorem map_evaluateCoordinatePolynomial {B : Type*} [CommRing B] (φ : A →+* B)
    (p : NormalCoordinate → A) (Q : CoordinatePolynomial) :
    φ (evaluateCoordinatePolynomial p Q) =
      evaluateCoordinatePolynomial (fun j => φ (p j)) Q := by
  have hh := MvPolynomial.map_eval₂Hom (Int.castRingHom A) p φ Q
  have hc : φ.comp (Int.castRingHom A) = Int.castRingHom B := by
    ext z
    simp
  rw [hc] at hh
  exact hh

/-- The entire solved graph commutes with specialization, since each step
uses only polynomial operations. -/
theorem map_solveFreePoint {B : Type*} [CommRing B] (φ : A →+* B)
    (q : FreeCoordinate → A) (N : ℕ) :
    (fun j => φ (solveFreePoint q N j)) = solveFreePoint (fun j => φ (q j)) N := by
  induction N with
  | zero =>
    funext j
    change φ (initialFreePoint q j) = initialFreePoint (fun k => φ (q k)) j
    simp only [initialFreePoint]
    split_ifs <;> simp only [map_zero]
  | succ n ih =>
    funext j
    simp only [solveFreePoint]
    split_ifs with hn
    · by_cases hj : j = solvedCoordinate ⟨n,hn⟩
      · subst j
        rw [Function.update_self, Function.update_self, map_evaluateCoordinatePolynomial]
        rw [ih]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        exact congrFun ih j
    · exact congrFun ih j

/-- These 62 integral polynomials give the inverse affine coordinate map. -/
def freeParameterPolynomial (j : NormalCoordinate) : MvPolynomial FreeCoordinate ℤ :=
  solveFreePoint MvPolynomial.X 5 j

theorem eval_freeParameterPolynomial (q : FreeCoordinate → A) (j : NormalCoordinate) :
    MvPolynomial.eval₂ (Int.castRingHom A) q (freeParameterPolynomial j) =
      solveFreePoint q 5 j := by
  have h := map_solveFreePoint (MvPolynomial.eval₂Hom (Int.castRingHom A) q)
    (MvPolynomial.X : FreeCoordinate → MvPolynomial FreeCoordinate ℤ) 5
  have hx : (fun k : FreeCoordinate => MvPolynomial.eval₂Hom (Int.castRingHom A) q
      (MvPolynomial.X k)) = q := by
    funext k
    exact MvPolynomial.eval₂_X _ _ k
  rw [hx] at h
  exact congrFun h j

end Ring
section Field
variable {K : Type*} [Field K]

/-- The actual normal-form locus reconstructed from arbitrary free coordinates. -/
def parameterFromFree (q : FreeCoordinate → K) : ParameterSpace (K := K) := by
  refine ⟨solveFreePoint q 5, (parameter_condition_iff_equations _).mpr ?_⟩
  apply (definingEquations_iff_fixed _).mpr
  intro i
  exact solveFreePoint_equations q 5 i i.isLt

/-- Projection to exactly the 57 normal-form coefficients retained in the paper. -/
def parameterFreeProjection (p : ParameterSpace (K := K)) : FreeCoordinate → K :=
  fun j => p.val j.val

/-- A proved equivalence between the genuine parameter locus and the 57 free
coordinates, with no choice of extraneous subalgebra data. Polynomiality is
established below by universal specialization. -/
def parameterFreeEquiv : ParameterSpace (K := K) ≃ (FreeCoordinate → K) where
  toFun := parameterFreeProjection
  invFun := parameterFromFree
  left_inv p := by
    apply Subtype.ext
    exact solveFreePoint_unique p.val
      ((definingEquations_iff_fixed p.val).mp (parameterSpace_definingEquations p))
  right_inv q := by
    funext j
    exact solveFreePoint_free q 5 j

/-- The inverse of the genuine parameter-space equivalence is polynomial
in each of its 62 normal-form coordinates. -/
theorem parameterFreeEquiv_inverse_polynomial (q : FreeCoordinate → K) (j : NormalCoordinate) :
    ((parameterFreeEquiv (K := K)).symm q).val j =
      MvPolynomial.eval₂ (Int.castRingHom K) q (freeParameterPolynomial j) :=
  (eval_freeParameterPolynomial q j).symm

open scoped PowerSeries.WithPiTopology
variable [TopologicalSpace K] [DiscreteTopology K]

/-- The free affine coordinates classify actual complete embedded subalgebras.
Their inverse is the proved polynomial graph followed by the actual jet
inverse-image construction. -/
def completeGammaFreeEquiv : CompleteGammaSubalgebra (K := K) ≃ (FreeCoordinate → K) :=
  completeGammaParameterEquiv.trans parameterFreeEquiv

end Field
end EmbeddingDimensionStrata
