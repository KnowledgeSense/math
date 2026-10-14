import MainTheorems.EulerianPencil.ResidueSigns

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def quadraticLift (m : ℕ) (f : ℝ[X]) : ℝ[X] :=
  MvPolynomial.eval₂ C ![X ^ 2 + 1, X] (f.homogenize m)

@[simp] theorem quadraticLift_zero (m : ℕ) : quadraticLift m 0 = 0 := by simp [quadraticLift]

@[simp] theorem quadraticLift_add (m : ℕ) (f g : ℝ[X]) :
    quadraticLift m (f + g) = quadraticLift m f + quadraticLift m g := by simp [quadraticLift]

@[simp] theorem quadraticLift_C_mul (m : ℕ) (a : ℝ) (f : ℝ[X]) :
    quadraticLift m (C a * f) = C a * quadraticLift m f := by simp [quadraticLift]

theorem quadraticLift_X_pow {j m : ℕ} (hj : j ≤ m) :
    quadraticLift m (X ^ j) = (X ^ 2 + 1) ^ j * X ^ (m - j) := by
  simp [quadraticLift, homogenize_X_pow hj]

theorem quadraticLift_mul {a b : ℕ} {f g : ℝ[X]} (hf : f.natDegree ≤ a)
    (hg : g.natDegree ≤ b) :
    quadraticLift (a + b) (f * g) = quadraticLift a f * quadraticLift b g := by
  simp [quadraticLift, homogenize_mul f g hf hg]

theorem quadraticLift_raise {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) (j : ℕ) :
    quadraticLift (m + j) f = X ^ j * quadraticLift m f := by
  apply Polynomial.induction_with_natDegree_le
    (fun f => quadraticLift (m + j) f = X ^ j * quadraticLift m f) m
  · simp
  · intro k a _ hk
    rw [quadraticLift_C_mul, quadraticLift_C_mul, quadraticLift_X_pow (by omega : k ≤ m + j),
      quadraticLift_X_pow hk, show m + j - k = (m - k) + j by omega, pow_add]
    ring
  · intro f g _ _ ihf ihg
    rw [quadraticLift_add, quadraticLift_add, ihf, ihg, mul_add]
  · exact hf

theorem quadraticLift_X_sub_C (a : ℝ) :
    quadraticLift 1 (X - C a) = X ^ 2 - C a * X + 1 := by
  simp [quadraticLift, homogenize_sub, homogenize_X (by decide : 1 ≠ 0)]
  ring

theorem quadraticLift_shifted_pow (j : ℕ) :
    quadraticLift j ((X - C 2) ^ j) = (1 - X) ^ (2 * j) := by
  induction j with
  | zero => simp [quadraticLift]
  | succ j ih =>
    rw [pow_succ, quadraticLift_mul (by simp : ((X - C 2 : ℝ[X]) ^ j).natDegree ≤ j)
      (by simp : (X - C 2 : ℝ[X]).natDegree ≤ 1), ih, quadraticLift_X_sub_C]
    have h : (X ^ 2 - C 2 * X + 1 : ℝ[X]) = (1 - X) ^ 2 := by
      simp only [map_ofNat]
      ring
    rw [h, ← pow_add]
    congr 1

theorem quadraticLift_reduction {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) :
    quadraticLift m (reduction m f) = lift m f := by
  apply Polynomial.induction_with_natDegree_le
    (fun f => quadraticLift m (reduction m f) = lift m f) m
  · simp
  · intro j a _ hj
    rw [reduction_C_mul, quadraticLift_C_mul, lift_C_mul, reduction_X_pow hj, lift_X_pow hj]
    have hm : m = (m - j) + j := by omega
    have hd : ((X - C 2 : ℝ[X]) ^ (m - j)).natDegree ≤ m - j := by simp
    rw [show quadraticLift m ((X - C 2) ^ (m - j)) =
      X ^ j * quadraticLift (m - j) ((X - C 2) ^ (m - j)) by
        have he := quadraticLift_raise hd j
        rw [← hm] at he
        exact he]
    rw [quadraticLift_shifted_pow]
    rfl
  · intro f g _ _ ihf ihg
    rw [reduction_add, quadraticLift_add, lift_add, ihf, ihg]
  · exact hf

theorem eulerian_quadraticLift (m : ℕ) :
    (eulerian (2 * m + 1)).map (Int.castRingHom ℝ) = quadraticLift m (oddH m) ∧
      (eulerian (2 * m + 2)).map (Int.castRingHom ℝ) =
        (1 + X) * quadraticLift m (evenH m) := by
  rw [oddH, evenH, quadraticLift_reduction (oddF_degree_le m),
    quadraticLift_reduction (evenF_degree_le m)]
  exact eulerian_lift m

noncomputable def reciprocalQuadratic (r : ℝ) : ℝ[X] := X ^ 2 - C r * X + 1

theorem quadraticLift_root_product (r : Multiset ℝ) :
    quadraticLift r.card (r.map (fun a => (X - C a : ℝ[X]))).prod =
      (r.map reciprocalQuadratic).prod := by
  induction r using Multiset.induction_on with
  | empty => simp [quadraticLift]
  | cons a r ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons]
    rw [show r.card + 1 = 1 + r.card by omega, quadraticLift_mul
      (by simp : (X - C a : ℝ[X]).natDegree ≤ 1)
      (natDegree_multiset_prod_X_sub_C_eq_card r).le, quadraticLift_X_sub_C, ih]
    rfl

theorem quadraticLift_eq_quadratic_product {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic) :
    quadraticLift f.natDegree f = (f.roots.map reciprocalQuadratic).prod := by
  conv_lhs => arg 2; rw [hs.eq_prod_roots_of_monic hm]
  rw [hs.natDegree_eq_card_roots, quadraticLift_root_product]

end ResearchMain.EulerianPencil
