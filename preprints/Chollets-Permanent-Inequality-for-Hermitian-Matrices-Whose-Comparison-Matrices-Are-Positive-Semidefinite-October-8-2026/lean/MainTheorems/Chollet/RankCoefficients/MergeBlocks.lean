import MainTheorems.Chollet.RankCoefficients.SquareFree

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [DecidableEq I]

theorem rooted_union (s t : Finset I) (h : Disjoint s t) (c d : I → ℂ) (a b : ℂ) :
    rooted (s ∪ t) (fun r => if r ∈ s then a * c r else b * d r) =
      scalar a * rooted s c * monomial t + scalar b * monomial s * rooted t d := by
  have hns : ∀ r ∈ s, r ∉ t := fun r hr ht => Finset.disjoint_left.mp h hr ht
  have hnt : ∀ r ∈ t, r ∉ s := fun r hr hs => Finset.disjoint_left.mp h hs hr
  unfold rooted
  rw [Finset.sum_union h]
  congr 1
  · rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only
    rw [ite_eq_left hr, Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hns r hr),
      monomial_union _ _ (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) h),
      scalar_mul]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only
    rw [ite_eq_right (hnt r hr), Finset.erase_union_distrib,
      Finset.erase_eq_of_notMem (hnt r hr),
      monomial_union _ _ (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) h),
      scalar_mul]
    ring

theorem join_rooted (s t : Finset I) (h : Disjoint s t) (c d : I → ℂ)
    {i j : I} (hi : i ∈ s) (hj : j ∈ t) (u v : ℂ) :
    (scalar u * rowVariable i + scalar v * rowVariable j) * rooted s c * rooted t d =
      rooted (s ∪ t) (fun r => if r ∈ s then v * d j * c r else u * c i * d r) := by
  rw [rooted_union s t h c d (v * d j) (u * c i)]
  have hi' := variable_rooted s c hi
  have hj' := variable_rooted t d hj
  rw [scalar_mul, scalar_mul]
  calc
    (scalar u * rowVariable i + scalar v * rowVariable j) * rooted s c * rooted t d =
        scalar u * (rowVariable i * rooted s c) * rooted t d +
          scalar v * rooted s c * (rowVariable j * rooted t d) := by ring
    _ = scalar u * (scalar (c i) * monomial s) * rooted t d +
          scalar v * rooted s c * (scalar (d j) * monomial t) := by rw [hi', hj']
    _ = _ := by ring

theorem joined_phases_unit (s t : Finset I) (h : Disjoint s t) (c d : I → ℂ)
    {i j : I} (hi : i ∈ s) (hj : j ∈ t) (u v : ℂ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hc : ∀ r ∈ s, ‖c r‖ = 1) (hd : ∀ r ∈ t, ‖d r‖ = 1) :
    ∀ r ∈ s ∪ t,
      ‖if r ∈ s then v * d j * c r else u * c i * d r‖ = 1 := by
  intro r hr
  rcases Finset.mem_union.mp hr with hrs | hrt
  · simp [hrs, hv, hd j hj, hc r hrs]
  · have hrs : r ∉ s := fun hs => Finset.disjoint_left.mp h hs hrt
    simp [hrs, hu, hc i hi, hd r hrt]

theorem join_rooted_closed (s t : Finset I) (h : Disjoint s t) (c : I → ℂ)
    {i j : I} (hi : i ∈ s) (hj : j ∈ t) (u v : ℂ) :
    (scalar u * rowVariable i + scalar v * rowVariable j) * rooted s c * monomial t =
      scalar (u * c i) * monomial (s ∪ t) := by
  rw [monomial_union s t h, scalar_mul]
  calc
    (scalar u * rowVariable i + scalar v * rowVariable j) * rooted s c * monomial t =
        scalar u * (rowVariable i * rooted s c) * monomial t +
          scalar v * rooted s c * (rowVariable j * monomial t) := by ring
    _ = scalar u * (scalar (c i) * monomial s) * monomial t := by
      rw [variable_rooted s c hi, variable_monomial_zero t hj]
      ring
    _ = _ := by ring

theorem join_closed (s t : Finset I) {i j : I} (hi : i ∈ s) (hj : j ∈ t)
    (u v : ℂ) :
    (scalar u * rowVariable i + scalar v * rowVariable j) * monomial s * monomial t =
      (0 : SquareFree I) := by
  calc
    (scalar u * rowVariable i + scalar v * rowVariable j) * monomial s * monomial t =
        scalar u * (rowVariable i * monomial s) * monomial t +
          scalar v * monomial s * (rowVariable j * monomial t) := by ring
    _ = 0 := by rw [variable_monomial_zero s hi, variable_monomial_zero t hj]; ring

end ResearchMain.Chollet.RankCoefficients
