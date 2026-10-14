import MainTheorems.PureOSequences.Boxes
import Mathlib.Data.Fintype.Pi

namespace ResearchMain.Domination

open Classical ResearchMain.PureOSequences

noncomputable def boundedParts {r : ℕ} (bounds : Fin r → ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun i => Finset.Icc 1 (bounds i)

theorem mem_boundedParts {r : ℕ} (bounds : Fin r → ℕ) (p : Fin r → ℕ) :
    p ∈ boundedParts bounds ↔ ∀ i, 1 ≤ p i ∧ p i ≤ bounds i := by
  simp [boundedParts, Fintype.mem_piFinset]

noncomputable def compositionCount {r : ℕ} (bounds : Fin r → ℕ) (N : ℕ) : ℕ :=
  ((boundedParts bounds).filter fun p => ∑ i, p i = N).card

noncomputable def compositionCountZ {r : ℕ} (bounds : Fin r → ℕ) (N : ℤ) : ℤ :=
  ∑ p ∈ boundedParts bounds, if ((∑ i, p i : ℕ) : ℤ) = N then 1 else 0

theorem compositionCountZ_nat {r : ℕ} (bounds : Fin r → ℕ) (N : ℕ) :
    compositionCountZ bounds N = compositionCount bounds N := by
  unfold compositionCountZ compositionCount
  rw [Finset.card_filter]
  conv_rhs => rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Nat.cast_inj]

noncomputable def exponentBounds {r : ℕ} (bounds : Fin r → ℕ) : Monomial r :=
  Finsupp.equivFunOnFinite.symm fun i => bounds i - 1

@[simp] theorem exponentBounds_apply {r : ℕ} (bounds : Fin r → ℕ) (i : Fin r) :
    exponentBounds bounds i = bounds i - 1 := by simp [exponentBounds]

theorem compositionCountZ_eq_box {r : ℕ} (bounds : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ bounds i) (N : ℤ) :
    compositionCountZ bounds N = boxCountZ (exponentBounds bounds) (N - r) := by
  unfold compositionCountZ boxCountZ
  symm
  apply Finset.sum_bij (fun m _ => fun i => m i + 1)
  · intro m hm
    apply (mem_boundedParts bounds _).mpr
    intro i
    have hmi := mem_divisorsFinset_iff.mp hm i
    simp only [exponentBounds_apply] at hmi
    have := hpos i
    omega
  · intro m _ n _ heq
    apply Finsupp.ext
    intro i
    have hi := congrFun heq i
    omega
  · intro p hp
    have hparts := (mem_boundedParts bounds p).mp hp
    refine ⟨Finsupp.equivFunOnFinite.symm (fun i => p i - 1), ?_, ?_⟩
    · apply mem_divisorsFinset_iff.mpr
      intro i
      change p i - 1 ≤ bounds i - 1
      exact Nat.sub_le_sub_right (hparts i).2 1
    · funext i
      change p i - 1 + 1 = p i
      exact Nat.sub_add_cancel (hparts i).1
  · intro m _
    have hsum : (∑ i : Fin r, (m i + 1)) = totalDeg m + r := by
      simp [Finset.sum_add_distrib, totalDeg_eq_sum_univ]
    change (if (totalDeg m : ℤ) = N - r then (1 : ℤ) else 0) =
      (if ((∑ i : Fin r, (m i + 1) : ℕ) : ℤ) = N then 1 else 0)
    simp only [hsum, Nat.cast_add]
    simp only [show (totalDeg m : ℤ) + r = N ↔ (totalDeg m : ℤ) = N - r by omega]

theorem compositionCountZ_ratioDecreasing {r : ℕ} (bounds : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ bounds i) : RatioDecreasing (compositionCountZ bounds) := by
  intro a b hab
  simp only [compositionCountZ_eq_box bounds hpos]
  have h := box_ratioDecreasing (exponentBounds bounds) (a - r) (b - r) (by omega)
  simpa only [add_sub_right_comm, sub_right_comm] using h

theorem compositionCountZ_nonneg {r : ℕ} (bounds : Fin r → ℕ) (N : ℤ) :
    0 ≤ compositionCountZ bounds N := by
  apply Finset.sum_nonneg
  intro p _
  split <;> norm_num

theorem exponentBounds_degree {r : ℕ} (bounds : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ bounds i) :
    totalDeg (exponentBounds bounds) + r = ∑ i, bounds i := by
  rw [totalDeg_eq_sum_univ]
  have hr : r = ∑ _i : Fin r, (1 : ℕ) := by simp
  calc
    (∑ i, (exponentBounds bounds) i) + r =
        (∑ i, (exponentBounds bounds) i) + (∑ _i : Fin r, (1 : ℕ)) :=
      congrArg ((∑ i, (exponentBounds bounds) i) + ·) hr
    _ = ∑ i : Fin r, ((exponentBounds bounds) i + 1) := Finset.sum_add_distrib.symm
    _ = ∑ i, bounds i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [exponentBounds_apply]
      exact Nat.sub_add_cancel (hpos i)

theorem compositionCountZ_pos {r : ℕ} (bounds : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ bounds i) (N : ℤ)
    (hlo : (r : ℤ) ≤ N) (hhi : N ≤ (∑ i, bounds i : ℕ)) :
    0 < compositionCountZ bounds N := by
  rw [compositionCountZ_eq_box bounds hpos]
  have he := exponentBounds_degree bounds hpos
  apply boxCountZ_pos
  · omega
  · omega

theorem compositionCountZ_zero {r : ℕ} (bounds : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ bounds i) (N : ℤ)
    (hN : N < r ∨ (∑ i, bounds i : ℕ) < N) : compositionCountZ bounds N = 0 := by
  rw [compositionCountZ_eq_box bounds hpos]
  have he := exponentBounds_degree bounds hpos
  apply boxCountZ_zero
  omega

end ResearchMain.Domination
