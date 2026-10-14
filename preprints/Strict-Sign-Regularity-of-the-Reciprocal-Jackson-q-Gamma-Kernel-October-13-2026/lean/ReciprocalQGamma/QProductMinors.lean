import ReciprocalQGamma.NestedMinors
import ReciprocalQGamma.Products

noncomputable section
open scoped BigOperators
namespace ReciprocalQGamma

def qShift (q : ℝ) (j : ℕ) : ℝ := 1 / q ^ j - 1
def leadingFactor (q : ℝ) (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, q ^ j

theorem qShift_nonneg (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (j : ℕ) :
    0 ≤ qShift q j := by
  have hp : 0 < q ^ j := pow_pos hq0 _
  have hle : q ^ j ≤ 1 := pow_le_one₀ hq0.le hq1
  unfold qShift
  have hd : 1 ≤ 1 / q ^ j := (le_div_iff₀ hp).mpr (by simpa using hle)
  linarith

theorem leadingFactor_pos (q : ℝ) (hq : 0 < q) (k : ℕ) : 0 < leadingFactor q k :=
  Finset.prod_pos (fun j _ => pow_pos hq j)

theorem qProduct_polynomial (q : ℝ) (hq : 0 < q) (s : ℝ) (k : ℕ) :
    qProduct q (1 - s) k = leadingFactor q k * (nestedPolynomial (qShift q) k).eval s := by
  unfold qProduct leadingFactor nestedPolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  unfold qShift
  have hp : q ^ j ≠ 0 := ne_of_gt (pow_pos hq j)
  field_simp
  ring

theorem qProduct_minors_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    {r m : ℕ} (s : Fin r → ℝ) (hs : StrictMono s) (hpos : ∀ i, 0 < s i)
    (k : Fin r → Fin m) (hk : StrictMono k) :
    0 < Matrix.det (fun i j => qProduct q (1 - s i) (k j).val) := by
  have he : (fun i j => qProduct q (1 - s i) (k j).val) =
      (fun i j => leadingFactor q (k j).val * (nestedPolynomial (qShift q) (k j).val).eval (s i)) := by
    ext i j
    exact qProduct_polynomial q hq0 (s i) (k j).val
  rw [he]
  change 0 < (Matrix.of (fun i j : Fin r => leadingFactor q (k j).val *
    (nestedPolynomial (qShift q) (k j).val).eval (s i))).det
  rw [Matrix.det_mul_row (fun j : Fin r => leadingFactor q (k j).val)
    (fun i j : Fin r => (nestedPolynomial (qShift q) (k j).val).eval (s i))]
  exact mul_pos (Finset.prod_pos (fun j _ => leadingFactor_pos q hq0 (k j).val))
    (nestedPolynomial_minors_pos (qShift q) (qShift_nonneg q hq0 hq1.le) s hs hpos k hk)

end ReciprocalQGamma
