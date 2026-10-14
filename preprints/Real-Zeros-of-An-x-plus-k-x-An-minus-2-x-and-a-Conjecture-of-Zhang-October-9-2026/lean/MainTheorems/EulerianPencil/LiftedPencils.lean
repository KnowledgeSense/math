import MainTheorems.EulerianPencil.ReciprocalQuadratics

namespace ResearchMain.EulerianPencil

open Polynomial

theorem quadraticLift_splits_iff {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic) :
    (quadraticLift f.natDegree f).Splits ↔
      ∀ r : ℝ, f.eval r = 0 → r ≤ -2 ∨ 2 ≤ r := by
  classical
  rw [quadraticLift_eq_quadratic_product hs hm]
  constructor
  · intro hq r hr
    have hmem : reciprocalQuadratic r ∈ f.roots.map reciprocalQuadratic :=
      Multiset.mem_map.mpr ⟨r, (mem_roots hm.ne_zero).mpr hr, rfl⟩
    apply (reciprocalQuadratic_splits_iff r).mp
    apply hq.of_dvd
    · apply Multiset.prod_ne_zero
      intro hz
      obtain ⟨r, _, hr⟩ := Multiset.mem_map.mp hz
      exact (reciprocalQuadratic_monic r).ne_zero hr
    · exact Multiset.dvd_prod hmem
  · intro hroot
    apply Splits.multisetProd
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
    exact (reciprocalQuadratic_splits_iff r).mpr (hroot r ((mem_roots hm.ne_zero).mp hr))

namespace InterlacingPair

variable {f g : ℝ[X]} (h : InterlacingPair f g)
include h

theorem lifted_splits_iff (hb : ∀ r : ℝ, g.eval r = 0 → r < -2) (k : ℝ) :
    (quadraticLift (g.natDegree + 1) (f + C k * g)).Splits ↔
      k ≤ -(f.eval 2 / g.eval 2) ∨ -(f.eval (-2) / g.eval (-2)) ≤ k := by
  rw [← h.degree k, quadraticLift_splits_iff (h.splits k) (h.monic k)]
  exact h.two_ray_root_classification hb (by norm_num) k

end InterlacingPair

noncomputable def eulerianPencil (n : ℕ) (k : ℝ) : ℝ[X] :=
  (eulerian n).map (Int.castRingHom ℝ) +
    C k * X * (eulerian (n - 2)).map (Int.castRingHom ℝ)

theorem odd_eulerianPencil (m : ℕ) (k : ℝ) :
    eulerianPencil (2 * m + 3) k =
      quadraticLift (m + 1) (oddH (m + 1) + C k * oddH m) := by
  unfold eulerianPencil
  rw [show 2 * m + 3 - 2 = 2 * m + 1 by omega,
    show 2 * m + 3 = 2 * (m + 1) + 1 by omega,
    (eulerian_quadraticLift (m + 1)).1, (eulerian_quadraticLift m).1,
    quadraticLift_add, quadraticLift_C_mul, quadraticLift_raise (oddH_natDegree m).le 1]
  simp
  ring

theorem even_eulerianPencil (m : ℕ) (k : ℝ) :
    eulerianPencil (2 * m + 4) k =
      (1 + X) * quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m) := by
  unfold eulerianPencil
  rw [show 2 * m + 4 - 2 = 2 * m + 2 by omega,
    show 2 * m + 4 = 2 * (m + 1) + 2 by omega,
    (eulerian_quadraticLift (m + 1)).2, (eulerian_quadraticLift m).2,
    quadraticLift_add, quadraticLift_C_mul, quadraticLift_raise (evenH_natDegree m).le 1]
  simp
  ring

theorem odd_eulerianPencil_splits_iff (m : ℕ) (k : ℝ) :
    (eulerianPencil (2 * m + 3) k).Splits ↔
      k ≤ -((oddH (m + 1)).eval 2 / (oddH m).eval 2) ∨
        -((oddH (m + 1)).eval (-2) / (oddH m).eval (-2)) ≤ k := by
  rw [odd_eulerianPencil]
  simpa only [oddH_natDegree] using (oddH_interlacingPair m).lifted_splits_iff
    (fun _ => oddH_roots_lt_neg_two m) k

theorem even_eulerianPencil_splits_iff (m : ℕ) (k : ℝ) :
    (eulerianPencil (2 * m + 4) k).Splits ↔
      k ≤ -((evenH (m + 1)).eval 2 / (evenH m).eval 2) ∨
        -((evenH (m + 1)).eval (-2) / (evenH m).eval (-2)) ≤ k := by
  have hn : (1 + X : ℝ[X]) ≠ 0 := by simpa only [add_comm, map_one] using (monic_X_add_C (1 : ℝ)).ne_zero
  rw [even_eulerianPencil, splits_mul_iff_right hn
    (by simpa only [add_comm, map_one] using Splits.X_add_C (1 : ℝ))]
  simpa only [evenH_natDegree] using (evenH_interlacingPair m).lifted_splits_iff
    (fun _ => evenH_roots_lt_neg_two m) k

end ResearchMain.EulerianPencil
