import MainTheorems.AHOConstants.PairWords
import MainTheorems.AHOConstants.PositivePowers
import MainTheorems.AHOConstants.Circulation

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder

def carryPairs (r : ℝ) : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | (a, b) :: xs => (r + a, a + b) :: carryPairs b xs

def carryLast (r : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => r
  | (_, b) :: xs => carryLast b xs

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def pairProduct (A B : Matrix I I ℂ) (xs : List (ℝ × ℝ)) : Matrix I I ℂ :=
  (xs.map (fun pq => spectralPower A pq.1 * spectralPower B pq.2)).prod

noncomputable def blockProduct (A B : Matrix I I ℂ) (xs : List (ℝ × ℝ)) : Matrix I I ℂ :=
  (xs.map (fun ab => spectralPower A ab.1 * spectralPower B (ab.1 + ab.2) *
    spectralPower A ab.2)).prod

noncomputable def flowProduct (A B : Matrix I I ℂ) (xs : List (ℝ × ℝ)) : Matrix I I ℂ :=
  (xs.map (fun ab => (spectralPower A ab.1 * spectralPower B ab.1) *
    (spectralPower B ab.2 * spectralPower A ab.2))).prod

theorem pairProduct_eq_matrixWord (A B : Matrix I I ℂ) (xs : List (ℝ × ℝ)) :
    pairProduct A B xs = matrixWord A B (pairWord xs) := by
  induction xs with
  | nil => rfl
  | cons pq xs ih =>
    rw [pairWord_cons, matrixWord_append]
    change (spectralPower A pq.1 * spectralPower B pq.2) * pairProduct A B xs =
      (spectralPower A pq.1 * (spectralPower B pq.2 * 1)) * matrixWord A B (pairWord xs)
    rw [Matrix.mul_one, ih]

theorem flowProduct_eq_blockProduct {A B : Matrix I I ℂ} (hB : B.PosDef)
    (xs : List (ℝ × ℝ)) : flowProduct A B xs = blockProduct A B xs := by
  unfold flowProduct blockProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro ab hab
  calc
    (spectralPower A ab.1 * spectralPower B ab.1) *
        (spectralPower B ab.2 * spectralPower A ab.2) =
        spectralPower A ab.1 * (spectralPower B ab.1 * spectralPower B ab.2) *
          spectralPower A ab.2 := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← spectralPower_add_real hB]

theorem carry_matrix_identity {A B : Matrix I I ℂ} (hA : A.PosDef)
    (r : ℝ) (xs : List (ℝ × ℝ)) :
    spectralPower A r * blockProduct A B xs =
      pairProduct A B (carryPairs r xs) * spectralPower A (carryLast r xs) := by
  induction xs generalizing r with
  | nil => simp [blockProduct, pairProduct, carryPairs, carryLast]
  | cons ab xs ih =>
    rcases ab with ⟨a, b⟩
    change spectralPower A r * ((spectralPower A a * spectralPower B (a + b) *
      spectralPower A b) * blockProduct A B xs) =
      ((spectralPower A (r + a) * spectralPower B (a + b)) *
        pairProduct A B (carryPairs b xs)) * spectralPower A (carryLast b xs)
    calc
      _ = (spectralPower A r * spectralPower A a) * spectralPower B (a + b) *
          (spectralPower A b * blockProduct A B xs) := by simp only [Matrix.mul_assoc]
      _ = (spectralPower A (r + a) * spectralPower B (a + b)) *
          (pairProduct A B (carryPairs b xs) * spectralPower A (carryLast b xs)) := by
        rw [← spectralPower_add_real hA, ih b]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem carryLast_independent {xs : List (ℝ × ℝ)} (hne : xs ≠ []) (r s : ℝ) :
    carryLast r xs = carryLast s xs := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons ab xs => rfl

theorem cyclic_flow_factorization {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (xs : List (ℝ × ℝ)) (r : ℝ) (hr : carryLast r xs = r) :
    Matrix.trace (flowProduct A B xs) = Matrix.trace (pairProduct A B (carryPairs r xs)) := by
  rw [flowProduct_eq_blockProduct hB]
  have hc := carry_matrix_identity (B := B) hA r xs
  rw [hr] at hc
  calc
    Matrix.trace (blockProduct A B xs) = Matrix.trace
        (spectralPower A (-r) * (spectralPower A r * blockProduct A B xs)) := by
      rw [← Matrix.mul_assoc, spectralPower_inverse_left hA, Matrix.one_mul]
    _ = Matrix.trace (spectralPower A (-r) *
        (pairProduct A B (carryPairs r xs) * spectralPower A r)) := by rw [hc]
    _ = Matrix.trace ((spectralPower A r * spectralPower A (-r)) *
        pairProduct A B (carryPairs r xs)) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    _ = _ := by rw [spectralPower_inverse_right hA, Matrix.one_mul]

theorem carryPairs_length (r : ℝ) (xs : List (ℝ × ℝ)) :
    (carryPairs r xs).length = xs.length := by
  induction xs generalizing r with
  | nil => rfl
  | cons ab xs ih => simpa only [carryPairs, List.length_cons] using congrArg Nat.succ (ih ab.2)

theorem carryPairs_zip (r : ℝ) (xs : List (ℝ × ℝ)) :
    carryPairs r xs = List.zipWith (fun c ab => (c + ab.1, ab.1 + ab.2))
      (r :: xs.map Prod.snd) xs := by
  induction xs generalizing r with
  | nil => rfl
  | cons ab xs ih =>
    simpa only [carryPairs, List.map_cons, List.zipWith_cons_cons] using
      congrArg (List.cons (r + ab.1, ab.1 + ab.2)) (ih ab.2)

theorem carryLast_ofFn {m : ℕ} (f : Fin (m + 1) → ℝ × ℝ) (r : ℝ) :
    carryLast r (List.ofFn f) = (f (Fin.last m)).2 := by
  induction m generalizing r with
  | zero => simp [List.ofFn_succ, carryLast, Fin.last_zero]
  | succ m ih =>
    rw [List.ofFn_succ]
    change carryLast (f 0).2 (List.ofFn (fun i : Fin (m + 1) => f i.succ)) = _
    simpa only [Fin.succ_last] using ih (fun i => f i.succ) (f 0).2

theorem previous_zero (m : ℕ) :
    (finRotate (m + 1)).symm (0 : Fin (m + 1)) = Fin.last m := by
  apply (finRotate (m + 1)).injective
  simp only [Equiv.apply_symm_apply, finRotate_last]

theorem carryPairs_circulation {m : ℕ} {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) :
    carryPairs (b (Fin.last m)) (List.ofFn (fun i => (a i, b i))) =
      List.ofFn (fun i => (p i, q i)) := by
  rw [carryPairs_zip]
  apply List.ext_getElem
  · simp only [List.length_zipWith, List.length_cons, List.length_map, List.length_ofFn]
    omega
  · intro i hi₁ hi₂
    cases i with
    | zero =>
      simp only [List.getElem_zipWith, List.getElem_cons_zero, List.getElem_ofFn]
      apply Prod.ext
      · have hp := h.previous (0 : Fin (m + 1))
        rw [previous_zero] at hp
        change b (Fin.last m) + a 0 = p 0
        linarith
      · exact h.2.1 0
    | succ i =>
      have hj : i + 1 < m + 1 := by
        simpa only [List.length_ofFn] using hi₂
      have hk : i < m + 1 := by omega
      let j : Fin (m + 1) := ⟨i + 1, hj⟩
      let k : Fin (m + 1) := ⟨i, hk⟩
      have hj₀ : j ≠ 0 := by intro he; have := congrArg Fin.val he; dsimp [j] at this; omega
      have hprev : (finRotate (m + 1)).symm j = k := by
        apply Fin.ext
        rw [coe_finRotate_symm_of_ne_zero hj₀]
        dsimp [j, k]
      simp only [List.getElem_zipWith, List.getElem_cons_succ, List.getElem_map,
        List.getElem_ofFn]
      change (b k + a j, a j + b j) = (p j, q j)
      apply Prod.ext
      · have hp := h.previous j
        rw [hprev] at hp
        linarith
      · exact h.2.1 j

theorem circulation_trace_factorization {m : ℕ} {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    wordTrace A B (pairWord (List.ofFn (fun i => (p i, q i)))) =
      Matrix.trace (flowProduct A B (List.ofFn (fun i => (a i, b i)))) := by
  rw [cyclic_flow_factorization hA hB _ (b (Fin.last m))
    (carryLast_ofFn (fun i => (a i, b i)) _), carryPairs_circulation h,
    pairProduct_eq_matrixWord]
  rfl

end ResearchMain.AHOConstants
