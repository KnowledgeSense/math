import MainTheorems.Corona.Fibers

namespace ResearchMain.Corona

open Classical Polynomial

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def Configurations (G : SimpleGraph V) (H : SimpleGraph W) :=
  Σ S : ↑(independentSets G), (v : V) → ↑(fiberChoices H S.val v)

noncomputable instance (G : SimpleGraph V) (H : SimpleGraph W) : Fintype (Configurations G H) :=
  inferInstanceAs (Fintype (Σ S : ↑(independentSets G), (v : V) → ↑(fiberChoices H S.val v)))

noncomputable def configurationEquiv (G : SimpleGraph V) (H : SimpleGraph W) :
    Configurations G H ≃ ↑(independentSets (corona G H)) where
  toFun c := ⟨assemble c.1.val (fun v => (c.2 v).val), by
    apply (mem_independentSets _ _).mpr
    apply (assemble_independent G H _ _).mpr
    refine ⟨(mem_independentSets _ _).mp c.1.property, ?_, ?_⟩
    · exact fun v => ((mem_fiberChoices _ _ _ _).mp (c.2 v).property).1
    · exact fun v hv => ((mem_fiberChoices _ _ _ _).mp (c.2 v).property).2 hv⟩
  invFun R :=
    let hR := (corona_independent G H R.val).mp ((mem_independentSets _ _).mp R.property)
    ⟨⟨R.val.toLeft, (mem_independentSets _ _).mpr hR.1⟩,
      fun v => ⟨attachmentFiber R.val v,
        (mem_fiberChoices _ _ _ _).mpr ⟨hR.2.1 v, hR.2.2 v⟩⟩⟩
  left_inv c := by
    rcases c with ⟨⟨S, hS⟩, T⟩
    dsimp only
    apply Sigma.ext
    · exact Subtype.ext (assemble_toLeft S (fun v => (T v).val))
    · apply Function.hfunext
      · rfl
      · intro v w hvw
        obtain rfl := eq_of_heq hvw
        apply Subtype.heq_iff_coe_eq (by
          intro A
          change A ∈ fiberChoices H (assemble S (fun v => (T v).val)).toLeft v ↔
            A ∈ fiberChoices H S v
          rw [assemble_toLeft]) |>.mpr
        exact attachmentFiber_assemble S (fun v => (T v).val) v
  right_inv R := by
    apply Subtype.ext
    exact assemble_fibers R.val

theorem fiberChoices_product (H : SimpleGraph W) (S : Finset V) :
    ∏ v, (if v ∈ S then (1 : ℝ[X]) else independencePolynomial H) =
      independencePolynomial H ^ (Fintype.card V - S.card) := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have he : Finset.univ.filter (fun v : V => v ∉ S) = Finset.univ \ S := by
    ext v
    simp
  rw [he, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ]

theorem configuration_sum (H : SimpleGraph W) (S : Finset V) :
    ∑ T : (v : V) → ↑(fiberChoices H S v),
      (X : ℝ[X]) ^ (S.card + ∑ v, (T v).val.card) =
      X ^ S.card * independencePolynomial H ^ (Fintype.card V - S.card) := by
  simp only [pow_add, ← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.mul_sum,
    ← Fintype.prod_sum (fun v (T : ↑(fiberChoices H S v)) => (X : ℝ[X]) ^ T.val.card)]
  have he : (∏ v, ∑ T : ↑(fiberChoices H S v), (X : ℝ[X]) ^ T.val.card) =
      ∏ v, (if v ∈ S then (1 : ℝ[X]) else independencePolynomial H) := by
    apply Finset.prod_congr rfl
    intro v _
    rw [Finset.sum_coe_sort (fiberChoices H S v) (fun T => (X : ℝ[X]) ^ T.card),
      fiberChoices_polynomial]
  rw [he, fiberChoices_product]

theorem independencePolynomial_corona (G : SimpleGraph V) (H : SimpleGraph W) :
    independencePolynomial (corona G H) =
      ∑ S ∈ independentSets G,
        X ^ S.card * independencePolynomial H ^ (Fintype.card V - S.card) := by
  have he := Fintype.sum_equiv (configurationEquiv G H)
    (fun c => (X : ℝ[X]) ^ (c.1.val.card + ∑ v, (c.2 v).val.card))
    (fun R => X ^ R.val.card) (by
      intro c
      change X ^ (c.1.val.card + ∑ v, (c.2 v).val.card) =
        X ^ (assemble c.1.val (fun v => (c.2 v).val)).card
      rw [assemble_card])
  rw [Finset.sum_coe_sort (independentSets (corona G H))
    (fun R => (X : ℝ[X]) ^ R.card)] at he
  unfold independencePolynomial
  rw [← he]
  change (∑ c : Σ S : ↑(independentSets G), (v : V) → ↑(fiberChoices H S.val v),
    (X : ℝ[X]) ^ (c.1.val.card + ∑ v, (c.2 v).val.card)) = _
  rw [Fintype.sum_sigma (fun c : Σ S : ↑(independentSets G),
    (v : V) → ↑(fiberChoices H S.val v) =>
      (X : ℝ[X]) ^ (c.1.val.card + ∑ v, (c.2 v).val.card))]
  simp only [configuration_sum]
  exact Finset.sum_coe_sort (independentSets G)
    (fun S => (X : ℝ[X]) ^ S.card * independencePolynomial H ^ (Fintype.card V - S.card))

end ResearchMain.Corona
