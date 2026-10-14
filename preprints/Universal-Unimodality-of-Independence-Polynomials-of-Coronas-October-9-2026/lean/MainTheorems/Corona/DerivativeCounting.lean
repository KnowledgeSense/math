import MainTheorems.Corona.CoronaPolynomial

namespace ResearchMain.Corona

open Classical Polynomial

variable {W : Type} [Fintype W] [DecidableEq W]

theorem independent_erase_injective (H : SimpleGraph W) (v : W) :
    Set.InjOn (fun S : Finset W => S.erase v)
      ((independentSets H).filter (fun S => v ∈ S) : Set (Finset W)) := by
  intro S hS T hT hST
  have hvS := (Finset.mem_filter.mp hS).2
  have hvT := (Finset.mem_filter.mp hT).2
  calc
    S = insert v (S.erase v) := (Finset.insert_erase hvS).symm
    _ = insert v (T.erase v) := congrArg (insert v) hST
    _ = T := Finset.insert_erase hvT

theorem derivative_fiber_bound (H : SimpleGraph W) (v : W) {x : ℝ} (hx : 0 ≤ x) :
    ∑ S ∈ (independentSets H).filter (fun S => v ∈ S), x ^ (S.card - 1) ≤
      (independencePolynomial H).eval x := by
  have hinj := independent_erase_injective H v
  have he : ∀ S ∈ (independentSets H).filter (fun S => v ∈ S),
      x ^ (S.card - 1) = x ^ (S.erase v).card := by
    intro S hS
    exact congrArg (fun n => x ^ n) (Finset.card_erase_of_mem (Finset.mem_filter.mp hS).2).symm
  have hsum : (∑ S ∈ (independentSets H).filter (fun S => v ∈ S), x ^ (S.card - 1)) =
      ∑ T ∈ ((independentSets H).filter (fun S => v ∈ S)).image (fun S => S.erase v), x ^ T.card := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl he
  have hsubset : ((independentSets H).filter (fun S => v ∈ S)).image (fun S => S.erase v) ⊆
      independentSets H := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    apply (mem_independentSets _ _).mpr
    exact independent_mono H ((mem_independentSets _ _).mp (Finset.mem_filter.mp hS).1)
      (Finset.erase_subset _ _)
  rw [hsum, independencePolynomial, eval_finsetSum]
  simp only [eval_pow, eval_X]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => pow_nonneg hx _)

theorem independencePolynomial_derivative_bound (H : SimpleGraph W) {x : ℝ} (hx : 0 ≤ x) :
    (independencePolynomial H).derivative.eval x ≤ Fintype.card W * (independencePolynomial H).eval x := by
  have he : (independencePolynomial H).derivative.eval x =
      ∑ v : W, ∑ S ∈ (independentSets H).filter (fun S => v ∈ S), x ^ (S.card - 1) := by
    rw [independencePolynomial]
    simp only [map_sum, eval_finsetSum, derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X,
      Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    have hmem : (Finset.univ.filter (fun v : W => v ∈ S)) = S := by ext v; simp
    rw [← Finset.sum_filter, hmem]
    simp
  rw [he]
  calc
    _ ≤ ∑ _v : W, (independencePolynomial H).eval x :=
      Finset.sum_le_sum (fun v _ => derivative_fiber_bound H v hx)
    _ = _ := by simp

end ResearchMain.Corona
