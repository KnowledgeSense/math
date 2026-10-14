import MainTheorems.EulerianPencil.QuadraticLift
import Mathlib.LinearAlgebra.Lagrange

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def rootNodes (g : ℝ[X]) : Finset ℝ := g.roots.toFinset

theorem nodal_rootNodes {g : ℝ[X]} (hs : g.Splits) (hm : g.Monic) (hr : g.Separable) :
    Lagrange.nodal (rootNodes g) id = g := by
  rw [Lagrange.nodal, rootNodes]
  change (g.roots.toFinset.val.map (fun a => (X - C a : ℝ[X]))).prod = g
  rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots hr)]
  exact (hs.eq_prod_roots_of_monic hm).symm

theorem rootNodes_card {g : ℝ[X]} (hs : g.Splits) (hr : g.Separable) :
    (rootNodes g).card = g.natDegree := by
  rw [rootNodes, Multiset.toFinset_card_of_nodup (nodup_roots hr)]
  exact hs.natDegree_eq_card_roots.symm

theorem rootNodes_mem {g : ℝ[X]} (hg : g ≠ 0) {x : ℝ} : x ∈ rootNodes g ↔ g.eval x = 0 := by
  simp only [rootNodes, Multiset.mem_toFinset, mem_roots hg, IsRoot]

theorem monic_linear_quotient {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) :
    f /ₘ g = X + C ((f /ₘ g).coeff 0) := by
  have hle : g.degree ≤ f.degree := by
    rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hf.ne_zero, df, dg]
    exact_mod_cast Nat.le_succ m
  have hm : (f /ₘ g).Monic := by
    rw [Monic, leadingCoeff_divByMonic_of_monic hg hle, hf.leadingCoeff]
  apply hm.eq_X_add_C
  rw [natDegree_divByMonic f hg, df, dg, Nat.add_sub_cancel_left]

theorem partial_fraction_polynomial {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable) :
    f = (X + C ((f /ₘ g).coeff 0)) * g +
      ∑ r ∈ rootNodes g, C (f.eval r / (derivative g).eval r) *
        Lagrange.nodal ((rootNodes g).erase r) id := by
  classical
  have hi : Set.InjOn (id : ℝ → ℝ) (rootNodes g) := fun _ _ _ _ he => he
  have hrem : f %ₘ g = Lagrange.interpolate (rootNodes g) id (fun r => (f %ₘ g).eval r) := by
    apply Lagrange.eq_interpolate hi
    rw [rootNodes_card hs hr]
    rw [← degree_eq_natDegree hg.ne_zero]
    exact degree_modByMonic_lt f hg
  have heval (r : ℝ) (hr : r ∈ rootNodes g) : (f %ₘ g).eval r = f.eval r := by
    rw [modByMonic_eq_sub_mul_div, eval_sub, eval_mul,
      (rootNodes_mem hg.ne_zero).mp hr, zero_mul, sub_zero]
  have hder (r : ℝ) (hr' : r ∈ rootNodes g) :
      (derivative g).eval r = ∏ s ∈ (rootNodes g).erase r, (r - s) := by
    have he := Lagrange.eval_nodal_derivative_eval_node_eq (v := (id : ℝ → ℝ)) hr'
    simpa only [nodal_rootNodes hs hg hr, Lagrange.eval_nodal, id_eq] using he
  have hsum : f %ₘ g = ∑ r ∈ rootNodes g, C (f.eval r / (derivative g).eval r) *
      Lagrange.nodal ((rootNodes g).erase r) id := by
    rw [hrem, Lagrange.interpolate_eq_sum]
    apply Finset.sum_congr rfl
    intro r hr'
    rw [heval r hr', hder r hr', Lagrange.nodal]
    rfl
  calc
    f = f %ₘ g + g * (f /ₘ g) := (modByMonic_add_div f g).symm
    _ = _ := by
      rw [hsum, monic_linear_quotient hf hg df dg]
      simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
      ring

theorem residue_negative {f g : ℝ[X]} {r : ℝ}
    (h : f.eval r * (derivative g).eval r < 0) : f.eval r / (derivative g).eval r < 0 := by
  rw [div_eq_mul_inv]
  rcases mul_neg_iff.mp h with h | h
  · exact mul_neg_of_pos_of_neg h.1 (inv_lt_zero.mpr h.2)
  · exact mul_neg_of_neg_of_pos h.1 (inv_pos.mpr h.2)

end ResearchMain.EulerianPencil
