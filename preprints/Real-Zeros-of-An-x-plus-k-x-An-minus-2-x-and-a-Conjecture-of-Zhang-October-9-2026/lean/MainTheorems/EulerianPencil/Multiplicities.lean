import MainTheorems.EulerianPencil.DistinctRoots

namespace ResearchMain.EulerianPencil

open Polynomial

theorem quadratic_product_monic (r : Multiset ℝ) :
    (r.map reciprocalQuadratic).prod.Monic := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a r ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (reciprocalQuadratic_monic a).mul ih

theorem quadratic_product_natDegree (r : Multiset ℝ) :
    (r.map reciprocalQuadratic).prod.natDegree = 2 * r.card := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a r ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rw [natDegree_mul (reciprocalQuadratic_monic a).ne_zero (quadratic_product_monic r).ne_zero,
      reciprocalQuadratic_natDegree, ih]
    omega

theorem quadraticLift_monic {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic) :
    (quadraticLift f.natDegree f).Monic := by
  rw [quadraticLift_eq_quadratic_product hs hm]
  exact quadratic_product_monic f.roots

theorem quadraticLift_natDegree {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic) :
    (quadraticLift f.natDegree f).natDegree = 2 * f.natDegree := by
  rw [quadraticLift_eq_quadratic_product hs hm, quadratic_product_natDegree,
    ← hs.natDegree_eq_card_roots]

theorem reciprocalQuadratic_pos_multiplicity (r : ℝ) :
    (reciprocalQuadratic r).rootMultiplicity 1 = if r = 2 then 2 else 0 := by
  split_ifs with hr
  · rw [hr, reciprocalQuadratic_endpoint_pos]
    simpa using rootMultiplicity_X_sub_C_pow (1 : ℝ) 2
  · apply rootMultiplicity_eq_zero
    intro he
    rw [IsRoot, reciprocalQuadratic_eval] at he
    exact hr (by linarith)

theorem reciprocalQuadratic_neg_multiplicity (r : ℝ) :
    (reciprocalQuadratic r).rootMultiplicity (-1) = if r = -2 then 2 else 0 := by
  split_ifs with hr
  · rw [hr, reciprocalQuadratic_endpoint_neg]
    convert rootMultiplicity_X_sub_C_pow (-1 : ℝ) 2 using 1
    simp
  · apply rootMultiplicity_eq_zero
    intro he
    rw [IsRoot, reciprocalQuadratic_eval] at he
    exact hr (by linarith)

theorem quadratic_product_endpoint_multiplicities (r : Multiset ℝ) :
    (r.map reciprocalQuadratic).prod.rootMultiplicity 1 = 2 * r.count 2 ∧
      (r.map reciprocalQuadratic).prod.rootMultiplicity (-1) = 2 * r.count (-2) := by
  classical
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a r ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, rootMultiplicity_mul
      ((reciprocalQuadratic_monic a).mul (quadratic_product_monic r)).ne_zero,
      reciprocalQuadratic_pos_multiplicity, reciprocalQuadratic_neg_multiplicity,
      ih.1, ih.2, Multiset.count_cons]
    simp only [eq_comm (a := a)]
    constructor <;> split_ifs <;> omega

theorem quadraticLift_endpoint_multiplicities {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic) :
    (quadraticLift f.natDegree f).rootMultiplicity 1 = 2 * f.rootMultiplicity 2 ∧
      (quadraticLift f.natDegree f).rootMultiplicity (-1) = 2 * f.rootMultiplicity (-2) := by
  rw [quadraticLift_eq_quadratic_product hs hm]
  simpa only [count_roots] using quadratic_product_endpoint_multiplicities f.roots

theorem simple_root_multiplicity {f : ℝ[X]} (hf : f ≠ 0) (hs : f.Separable)
    {x : ℝ} (hx : f.eval x = 0) : f.rootMultiplicity x = 1 := by
  have hp := (rootMultiplicity_pos hf).mpr hx
  have hle := rootMultiplicity_le_one_of_separable hs x
  omega

namespace InterlacingPair

variable {f g : ℝ[X]} (h : InterlacingPair f g)
include h

theorem boundary_multiplicity_pos (hb : ∀ r : ℝ, g.eval r = 0 → r < -2) :
    (quadraticLift (g.natDegree + 1)
      (f + C (-(f.eval 2 / g.eval 2)) * g)).rootMultiplicity 1 = 2 := by
  let k := -(f.eval 2 / g.eval 2)
  have hd := h.degree k
  have hs := h.splits k
  have hm := h.monic k
  have hr := separable_of_simpleRoots hs hm.ne_zero (h.simpleRoots k)
  have ht := h.root_at_boundary (b := 2) (fun r hr => (hb r hr).trans (by norm_num))
  have he := (quadraticLift_endpoint_multiplicities hs hm).1
  rw [hd, simple_root_multiplicity hm.ne_zero hr ht] at he
  exact he

theorem boundary_multiplicity_neg (hb : ∀ r : ℝ, g.eval r = 0 → r < -2) :
    (quadraticLift (g.natDegree + 1)
      (f + C (-(f.eval (-2) / g.eval (-2))) * g)).rootMultiplicity (-1) = 2 := by
  let k := -(f.eval (-2) / g.eval (-2))
  have hd := h.degree k
  have hs := h.splits k
  have hm := h.monic k
  have hr := separable_of_simpleRoots hs hm.ne_zero (h.simpleRoots k)
  have ht := h.root_at_boundary hb
  have he := (quadraticLift_endpoint_multiplicities hs hm).2
  rw [hd, simple_root_multiplicity hm.ne_zero hr ht] at he
  exact he

end InterlacingPair

end ResearchMain.EulerianPencil
