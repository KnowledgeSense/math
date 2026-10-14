import ReciprocalQGamma.QProductMinors

noncomputable section
open scoped BigOperators
namespace ReciprocalQGamma

def partialKernel (q s t : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, qProduct q (1 - s) k / qProduct q q k * t ^ k

def firstMinor (q : ℝ) {r : ℕ} (s t : Fin r → ℝ) : ℝ :=
  Matrix.det (fun i j : Fin r => qProduct q (1 - s i) j.val) *
    Matrix.det (fun i j : Fin r => t j ^ i.val / qProduct q q i.val)

theorem monomial_quotient_minor_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    {r m : ℕ} (t : Fin r → ℝ) (ht : StrictMono t) (ht0 : ∀ i, 0 < t i)
    (k : Fin r → Fin m) (hk : StrictMono k) :
    0 < Matrix.det (fun i j : Fin r => t j ^ (k i).val / qProduct q q (k i).val) := by
  change 0 < (Matrix.of (fun i j : Fin r => t j ^ (k i).val / qProduct q q (k i).val)).det
  rw [← Matrix.det_transpose (Matrix.of (fun i j : Fin r => t j ^ (k i).val / qProduct q q (k i).val))]
  have he : (fun i j : Fin r => t i ^ (k j).val / qProduct q q (k j).val) =
      (fun i j : Fin r => (1 / qProduct q q (k j).val) * t i ^ (k j).val) := by
    ext i j; ring
  change 0 < Matrix.det (fun i j : Fin r => t i ^ (k j).val / qProduct q q (k j).val)
  rw [he]
  change 0 < (Matrix.of (fun i j : Fin r => (1 / qProduct q q (k j).val) * t i ^ (k j).val)).det
  rw [Matrix.det_mul_row (fun j : Fin r => 1 / qProduct q q (k j).val)
    (fun i j : Fin r => t i ^ (k j).val)]
  apply mul_pos
  · apply Finset.prod_pos
    intro j _
    exact one_div_pos.mpr (qProduct_pos q q hq0.le hq1.le hq0.le hq1 _)
  · exact generalizedVandermonde_pos t (fun i => (k i).val) ht ht0 (fun _ _ h => hk h)

theorem firstMinor_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    {r : ℕ} (s t : Fin r → ℝ) (hs : StrictMono s) (ht : StrictMono t)
    (hs0 : ∀ i, 0 < s i) (ht0 : ∀ i, 0 < t i) : 0 < firstMinor q s t := by
  exact mul_pos (qProduct_minors_pos q hq0 hq1 s hs hs0 id strictMono_id)
    (monomial_quotient_minor_pos q hq0 hq1 t ht ht0 id strictMono_id)

/-- A single fixed positive degree set bounds every sufficiently large truncated kernel. -/
theorem partialKernel_det_lower_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    {r : ℕ} (s t : Fin r → ℝ) (hs : StrictMono s) (ht : StrictMono t)
    (hs0 : ∀ i, 0 < s i) (ht0 : ∀ i, 0 < t i) (N : ℕ) :
    firstMinor q s t ≤ (r.factorial : ℝ) *
      Matrix.det (fun i j => partialKernel q (s i) (t j) (r + N)) := by
  let A : Matrix (Fin r) (Fin (r + N)) ℝ := fun i k => qProduct q (1 - s i) k.val
  let B : Matrix (Fin (r + N)) (Fin r) ℝ := fun k j => t j ^ k.val / qProduct q q k.val
  have he : (fun i j => partialKernel q (s i) (t j) (r + N)) = A * B := by
    ext i j
    unfold partialKernel
    rw [Matrix.mul_apply, Fin.sum_univ_eq_sum_range
      (fun k => qProduct q (1 - s i) k * (t j ^ k / qProduct q q k)) (r + N)]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [he, cauchyBinet_unordered]
  have ha : ∀ g : Fin r → Fin (r + N), StrictMono g → 0 ≤ (A.submatrix id g).det := by
    intro g hg
    exact (qProduct_minors_pos q hq0 hq1 s hs hs0 g hg).le
  have hb : ∀ g : Fin r → Fin (r + N), StrictMono g → 0 ≤ (B.submatrix g id).det := by
    intro g hg
    exact (monomial_quotient_minor_pos q hq0 hq1 t ht ht0 g hg).le
  have h := Finset.single_le_sum (fun f _ => minor_product_nonneg A B ha hb f)
    (Finset.mem_univ (Fin.castAdd N : Fin r → Fin (r + N)))
  exact h

end ReciprocalQGamma
