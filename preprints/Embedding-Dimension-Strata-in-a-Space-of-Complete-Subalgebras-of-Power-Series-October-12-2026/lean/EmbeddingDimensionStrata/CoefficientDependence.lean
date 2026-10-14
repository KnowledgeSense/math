import EmbeddingDimensionStrata.WeightedGraph

/-! # Finite coefficient dependence of universal monomial division -/
noncomputable section
namespace EmbeddingDimensionStrata
section Ring
variable {A : Type*} [CommRing A]

def AgreeBelow (N : ℕ) (f g : PowerSeries A) : Prop :=
  ∀ n < N, PowerSeries.coeff n f = PowerSeries.coeff n g

theorem AgreeBelow.refl (N : ℕ) (f : PowerSeries A) : AgreeBelow N f f := by intro n _; rfl

theorem AgreeBelow.sub {N : ℕ} {f f' g g' : PowerSeries A}
    (hf : AgreeBelow N f f') (hg : AgreeBelow N g g') : AgreeBelow N (f-g) (f'-g') := by
  intro n hn
  simp only [map_sub,hf n hn,hg n hn]

theorem AgreeBelow.smul {N : ℕ} {f g : PowerSeries A} (hf : AgreeBelow N f g) (a : A) :
    AgreeBelow N (a • f) (a • g) := by
  intro n hn
  simp only [map_smul,hf n hn]

theorem AgreeBelow.mul {N : ℕ} {f f' g g' : PowerSeries A}
    (hf : AgreeBelow N f f') (hg : AgreeBelow N g g') : AgreeBelow N (f*g) (f'*g') := by
  intro n hn
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega),hg ij.2 (by omega)]

theorem AgreeBelow.pow {N : ℕ} {f g : PowerSeries A} (hf : AgreeBelow N f g) (n : ℕ) :
    AgreeBelow N (f^n) (g^n) := by
  induction n with
  | zero => exact AgreeBelow.refl _ _
  | succ n ih => rw [pow_succ,pow_succ]; exact ih.mul hf

theorem basisSeries_agreeBelow {N : ℕ} {p q : NormalCoordinate → A}
    (hpq : ∀ i : Fin 5, AgreeBelow N (normalSeries p i) (normalSeries q i)) (n : ℕ) :
    AgreeBelow N (basisSeries p n) (basisSeries q n) := by
  exact ((((hpq 0).pow _).mul ((hpq 1).pow _)).mul ((hpq 2).pow _)).mul
    ((hpq 3).pow _) |>.mul ((hpq 4).pow _)

theorem reduceSeries_agreeBelow {N : ℕ} {p q : NormalCoordinate → A}
    (hpq : ∀ i : Fin 5, AgreeBelow N (normalSeries p i) (normalSeries q i))
    {f g : PowerSeries A} (hfg : AgreeBelow N f g) (M : ℕ) :
    AgreeBelow N (reduceSeries p M f) (reduceSeries q M g) := by
  induction M with
  | zero => exact hfg
  | succ m ih =>
    by_cases hm : m < N
    · rw [reduceSeries_succ,reduceSeries_succ]
      split_ifs with hmem
      · rw [ih m hm]
        exact ih.sub ((basisSeries_agreeBelow hpq m).smul _)
      · exact ih
    · intro n hn
      change PowerSeries.coeff n (reductionStep p m (reduceSeries p m f)) =
        PowerSeries.coeff n (reductionStep q m (reduceSeries q m g))
      rw [coeff_reductionStep_of_lt p _ (by omega),coeff_reductionStep_of_lt q _ (by omega)]
      exact ih n hn

/-- Changing a normal coefficient of exponent≥N cannot affect any generator
coefficient below N, regardless of its order weight. -/
theorem normalSeries_update_agreeBelow (p : NormalCoordinate → A) (j : NormalCoordinate)
    (a : A) (N : ℕ) (hj : N ≤ j.val.2.val) (i : Fin 5) :
    AgreeBelow N (normalSeries p i) (normalSeries (Function.update p j a) i) := by
  classical
  intro n hn
  rw [coeff_normalSeries,coeff_normalSeries]
  split_ifs with hlead hgap
  · rfl
  · rw [Function.update_of_ne]
    intro he
    have heq := congrArg (fun k : NormalCoordinate => k.val.2.val) he
    change n = j.val.2.val at heq
    omega
  · rfl

end Ring

/-- The r48 equation cannot involve w49: changing that coefficient leaves
all normal forms, products, and reduction coefficients through order48 fixed. -/
theorem secondPolynomial_W_update_invariant (p : NormalCoordinate → CoordinatePolynomial)
    (a : CoordinatePolynomial) :
    definingEquation (Function.update p (eliminatedCoordinate 2) a) 1 = definingEquation p 1 := by
  have hpq := normalSeries_update_agreeBelow p (eliminatedCoordinate 2) a 49 (by decide)
  have hF : AgreeBelow 49 (relationF p) (relationF (Function.update p (eliminatedCoordinate 2) a)) :=
    ((hpq 1).pow 4).sub ((hpq 0).mul (hpq 2))
  exact (reduceSeries_agreeBelow hpq hF 60 48 (by omega)).symm

end EmbeddingDimensionStrata
