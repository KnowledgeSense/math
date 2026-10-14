import MainTheorems.EulerianPencil.Multiplicities

namespace ResearchMain.EulerianPencil

open Polynomial

theorem reciprocalQuadratic_root_negative {r x : ℝ} (hr : r < -2)
    (hx : (reciprocalQuadratic r).eval x = 0) : x < 0 := by
  rw [reciprocalQuadratic_eval] at hx
  by_contra hn
  have hx0 : 0 ≤ x := le_of_not_gt hn
  have hp : r * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hx0
  nlinarith [sq_nonneg x]

theorem reciprocalQuadratic_root_positive {r x : ℝ} (hr : 2 < r)
    (hx : (reciprocalQuadratic r).eval x = 0) : 0 < x := by
  rw [reciprocalQuadratic_eval] at hx
  by_contra hn
  have hx0 : x ≤ 0 := le_of_not_gt hn
  have hp : r * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hx0
  nlinarith [sq_nonneg x]

theorem quadraticLift_roots_negative {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic)
    (hr : ∀ r : ℝ, f.eval r = 0 → r < -2) {x : ℝ}
    (hx : (quadraticLift f.natDegree f).eval x = 0) : x < 0 := by
  rw [quadraticLift_eq_quadratic_product hs hm, eval_multiset_prod] at hx
  obtain ⟨q, hq, hqx⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hx)
  obtain ⟨a, hamem, rfl⟩ := Multiset.mem_map.mp hq
  exact reciprocalQuadratic_root_negative (hr a ((mem_roots hm.ne_zero).mp hamem)) hqx

theorem quadraticLift_endpoint_ne_zero {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic)
    (hr : ∀ r : ℝ, f.eval r = 0 → r < -2) :
    (quadraticLift f.natDegree f).eval 1 ≠ 0 ∧ (quadraticLift f.natDegree f).eval (-1) ≠ 0 := by
  constructor
  · intro he
    have hn := quadraticLift_roots_negative hs hm hr he
    linarith
  · rw [quadraticLift_eval_neg_one (le_refl _)]
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    intro he
    exact (lt_irrefl (-2 : ℝ)) (hr (-2) he)

def NegativeRoots (f : ℝ[X]) : Prop := ∀ x : ℝ, f.eval x = 0 → x < 0

structure NegativeFactor (f : ℝ[X]) (d : ℕ) : Prop where
  monic : f.Monic
  degree : f.natDegree = d
  splits : f.Splits
  separable : f.Separable
  negative : NegativeRoots f

theorem negative_quadraticLift {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic)
    (hr : f.Separable) (hb : ∀ r : ℝ, f.eval r = 0 → r < -2) :
    NegativeFactor (quadraticLift f.natDegree f) (2 * f.natDegree) := by
  have hd := (quadraticLift_distinct_iff hs hm hr).mpr (fun r hr => Or.inl (hb r hr))
  exact ⟨quadraticLift_monic hs hm, quadraticLift_natDegree hs hm, hd.1, hd.2,
    fun _ hx => quadraticLift_roots_negative hs hm hb hx⟩

theorem remove_simple_root {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic) (hr : f.Separable)
    {t : ℝ} (ht : f.eval t = 0) (hb : ∀ x : ℝ, f.eval x = 0 → x ≠ t → x < -2) :
    ∃ q : ℝ[X], f = (X - C t) * q ∧ q.Monic ∧ q.Splits ∧ q.Separable ∧
      q.natDegree + 1 = f.natDegree ∧ (∀ x : ℝ, q.eval x = 0 → x < -2) := by
  obtain ⟨q, he⟩ := dvd_iff_isRoot.mpr ht
  have hqm : q.Monic := (monic_X_sub_C t).of_mul_monic_left (he ▸ hm)
  have hqs : q.Splits := hs.of_dvd hm.ne_zero ⟨X - C t, by rw [he]; ring⟩
  have hqr : q.Separable := hr.of_dvd ⟨X - C t, by rw [he]; ring⟩
  have hqt : q.eval t ≠ 0 := by
    have hd := simpleRoots_of_separable hr t ht
    rw [he] at hd
    simpa [derivative_mul] using hd
  refine ⟨q, he, hqm, hqs, hqr, ?_, ?_⟩
  · rw [he, natDegree_mul (X_sub_C_ne_zero t) hqm.ne_zero, natDegree_X_sub_C]
    omega
  · intro x hx
    exact hb x (by rw [he, eval_mul, hx, mul_zero]) (fun he => hqt (he ▸ hx))

namespace InterlacingPair

variable {f g : ℝ[X]} (h : InterlacingPair f g)
include h

theorem exceptional_factor (hb : ∀ r : ℝ, g.eval r = 0 → r < -2)
    {k t : ℝ} (ht : -2 ≤ t) (hr : (f + C k * g).eval t = 0) :
    ∃ q : ℝ[X],
      quadraticLift (g.natDegree + 1) (f + C k * g) = reciprocalQuadratic t * q ∧
      NegativeFactor q (2 * g.natDegree) ∧ q.eval (-1) ≠ 0 := by
  have hs := h.splits k
  have hm := h.monic k
  have hsep := separable_of_simpleRoots hs hm.ne_zero (h.simpleRoots k)
  obtain ⟨q, he, hqm, hqs, hqr, hqd, hqb⟩ := remove_simple_root hs hm hsep hr
    (fun x hx hxt => h.remaining_roots_below hb ht k hr hx hxt)
  have hd : q.natDegree = g.natDegree := by rw [h.degree k] at hqd; omega
  refine ⟨quadraticLift q.natDegree q, ?_, ?_, (quadraticLift_endpoint_ne_zero hqs hqm hqb).2⟩
  · rw [he, show g.natDegree + 1 = 1 + q.natDegree by omega,
      quadraticLift_mul (by simp : (X - C t : ℝ[X]).natDegree ≤ 1) (le_refl _),
      quadraticLift_X_sub_C]
    rfl
  · simpa only [hd] using negative_quadraticLift hqs hqm hqr hqb

end InterlacingPair

end ResearchMain.EulerianPencil
