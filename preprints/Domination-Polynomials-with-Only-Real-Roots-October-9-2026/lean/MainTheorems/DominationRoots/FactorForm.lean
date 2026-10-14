import MainTheorems.DominationRoots.Isomorphisms

namespace ResearchMain.DominationRoots

open Classical Polynomial

noncomputable def linearStar : ℤ[X] := X + C 2

noncomputable def quadraticStar : ℤ[X] := X ^ 2 + C 3 * X + 1

theorem starFactor_one : starFactor 1 = X * linearStar := by
  unfold starFactor linearStar
  simp only [pow_one, map_ofNat]
  ring

theorem starFactor_two : starFactor 2 = X * quadraticStar := by
  unfold starFactor quadraticStar
  simp only [map_ofNat]
  ring

theorem star_product_factors {C : Type} [Fintype C] (s : C → ℕ)
    (hs : ∀ c, s c = 1 ∨ s c = 2) :
    ∃ a b : ℕ, a + b = Fintype.card C ∧
      (∏ c, starFactor (s c)) = X ^ (a + b) * linearStar ^ a * quadraticStar ^ b := by
  let a := (Finset.univ.filter (fun c => s c = 1)).card
  let b := (Finset.univ.filter (fun c => s c ≠ 1)).card
  have hab : a + b = Fintype.card C := by
    simpa only [a, b, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun c => s c = 1)
  have he (c : C) : starFactor (s c) = X * if s c = 1 then linearStar else quadraticStar := by
    rcases hs c with h | h
    · rw [h, ite_eq_left rfl, starFactor_one]
    · rw [h, ite_eq_right (by omega), starFactor_two]
  refine ⟨a, b, hab, ?_⟩
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hab, Finset.prod_ite]
  simp only [Finset.prod_const]
  change X ^ (a + b) * (linearStar ^ a * quadraticStar ^ b) = _
  ring

theorem leafExtension_factors {C I : Type} [Fintype C] [Fintype I]
    {W : C → Type} [∀ c, Fintype (W c)] (H : SimpleGraph C)
    (hs : ∀ c, Fintype.card (W c) = 1 ∨ Fintype.card (W c) = 2) :
    ∃ a b : ℕ, a + b = Fintype.card C ∧
      dominationPolynomial (leafExtension H I W) =
        X ^ (a + b + Fintype.card I) * linearStar ^ a * quadraticStar ^ b := by
  have hne (c : C) : Nonempty (W c) := by
    apply Fintype.card_pos_iff.mp
    rcases hs c with h | h <;> omega
  obtain ⟨a, b, hab, he⟩ := star_product_factors (fun c => Fintype.card (W c)) hs
  refine ⟨a, b, hab, ?_⟩
  rw [dominationPolynomial_extension H hne, he, ← mul_assoc, ← mul_assoc, ← pow_add,
    add_comm (Fintype.card I) (a + b)]

theorem linearStar_monic : linearStar.Monic := monic_X_add_C 2

theorem quadraticStar_monic : quadraticStar.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 2
  · unfold quadraticStar
    compute_degree
  · norm_num [quadraticStar, coeff_one, coeff_X]

theorem linearStar_natDegree : linearStar.natDegree = 1 := natDegree_X_add_C 2

theorem quadraticStar_natDegree : quadraticStar.natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold quadraticStar
    compute_degree
  · norm_num [quadraticStar, coeff_one, coeff_X]

theorem realRooted_domination_factors {V : Type} [Fintype V] (G : SimpleGraph V)
    (hr : RealRooted (dominationPolynomial G)) :
    ∃ a b t : ℕ, dominationPolynomial G =
      X ^ (a + b + t) * (X + C 2) ^ a * (X ^ 2 + C 3 * X + 1) ^ b ∧
        Fintype.card V = 2 * a + 3 * b + t := by
  have hG := realRooted_oneTwoLeafGraph hr
  have hs (v : CoreVertex G) :
      Fintype.card ↥(attachedLeaves G v.val) = 1 ∨ Fintype.card ↥(attachedLeaves G v.val) = 2 := by
    simpa only [Fintype.card_coe] using hG v
  obtain ⟨a, b, _, he⟩ := leafExtension_factors
    (I := ↥(isolatedVertices G)) (W := fun v : CoreVertex G => ↥(attachedLeaves G v.val))
    (coreGraph G) hs
  rw [dominationPolynomial_iso (supportGraphIso G), Fintype.card_coe] at he
  refine ⟨a, b, (isolatedVertices G).card, he, ?_⟩
  have hd := congrArg natDegree he
  rw [dominationPolynomial_natDegree,
    ((monic_X_pow _).mul (linearStar_monic.pow a)).natDegree_mul (quadraticStar_monic.pow b),
    (monic_X_pow _).natDegree_mul (linearStar_monic.pow a), natDegree_X_pow,
    natDegree_pow, natDegree_pow, linearStar_natDegree, quadraticStar_natDegree] at hd
  omega

end ResearchMain.DominationRoots
