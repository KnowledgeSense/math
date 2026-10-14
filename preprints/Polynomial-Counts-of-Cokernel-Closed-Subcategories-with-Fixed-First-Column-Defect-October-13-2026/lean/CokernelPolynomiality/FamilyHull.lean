import CokernelPolynomiality.IntervalFamilies
import CokernelPolynomiality.IntervalHull

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

theorem IntervalHull.of_retract_intervals {n : ℕ} {Y : Finset (ℕ × ℕ)} (V : ChainRep n)
    (h : ∀ a b, a ≤ b → b ≤ n → ∀ (i : intervalRep n a b ⟶ V)
      (p : V ⟶ intervalRep n a b), i ≫ p=𝟙 _ → (a,b) ∈ Y) : IntervalHull n Y V := by
  induction interval_decomposition V with
  | zero V hV => exact .zero V hV
  | cons V K a b hab hbn _ e ih =>
    have hK : IntervalHull n Y K := ih (by
      intro c d hcd hdn i p hip
      apply h c d hcd hdn (i ≫ biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst ≫ p)
      simpa only [Category.assoc,e.inv_hom_id_assoc,biprod.inl_fst_assoc] using hip)
    have hI : (a,b) ∈ Y := h a b hab hbn (biprod.inr ≫ e.inv) (e.hom ≫ biprod.snd)
      (by simp [Category.assoc])
    exact .iso e.symm (.biprod K (intervalRep n a b) hK (.interval a b hab hbn hI))

theorem intervalFamily_mem_hull {n m : ℕ} {Y : Finset (ℕ × ℕ)} (c d : Fin m → ℕ)
    (h : ∀ j, IntervalHull n Y (intervalRep n (c j) (d j))) :
    IntervalHull n Y (intervalFamily n m c d) := by
  classical
  apply IntervalHull.of_retract_intervals
  intro a b hab hbn i p hip
  have hex : ∃ j : Fin m,
      (i ≫ intervalFamilyProj n m c d j) ≫ (intervalFamilyInj n m c d j ≫ p) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply interval_identity_ne_zero n a b hab hbn
    rw [← hip]
    calc
      i ≫ p = i ≫ (𝟙 (intervalFamily n m c d)) ≫ p := by simp
      _ = ∑ j : Fin m, (i ≫ intervalFamilyProj n m c d j) ≫
          (intervalFamilyInj n m c d j ≫ p) := by
        rw [← intervalFamily_total]
        simp only [Preadditive.comp_sum,Preadditive.sum_comp,Category.assoc]
      _ = 0 := Finset.sum_eq_zero (fun j _ => hn j)
  obtain ⟨j,hj⟩ := hex
  exact (h j).factor_nonzero a b hab hbn _ _ hj

end CokernelPolynomiality
