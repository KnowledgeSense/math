import MainTheorems.DominationRoots.TraceProducts

namespace ResearchMain.DominationRoots

open Polynomial

def AllowedProduct (f : ℤ[X]) : Prop :=
  ∃ a b : ℕ, f = linearFactor ^ a * quadraticPolynomial ^ b

theorem allowedProduct_mul {f g : ℤ[X]} (hf : AllowedProduct f) (hg : AllowedProduct g) :
    AllowedProduct (f * g) := by
  obtain ⟨a, b, rfl⟩ := hf
  obtain ⟨c, d, rfl⟩ := hg
  refine ⟨a + c, b + d, ?_⟩
  simp only [pow_add]
  ring

theorem rootTrace_one : rootTrace 1 = 0 := by
  simp [rootTrace, realRoots, realPolynomial]

theorem rootTrace_pow {f : ℤ[X]} (hm : f.Monic) (n : ℕ) :
    rootTrace (f ^ n) = (n : ℝ) * rootTrace f := by
  induction n with
  | zero => simp [rootTrace_one]
  | succ n ih =>
    rw [pow_succ, rootTrace_mul (hm.pow n) hm, ih]
    push_cast
    ring

theorem allowedProduct_trace {f : ℤ[X]} (hf : AllowedProduct f) :
    rootTrace f = 2 * (f.natDegree : ℝ) := by
  obtain ⟨a, b, rfl⟩ := hf
  rw [rootTrace_mul (linearFactor_monic.pow a) (quadraticPolynomial_monic.pow b),
    rootTrace_pow linearFactor_monic, rootTrace_pow quadraticPolynomial_monic,
    linearFactor_trace, quadraticPolynomial_trace,
    (linearFactor_monic.pow a).natDegree_mul (quadraticPolynomial_monic.pow b),
    natDegree_pow, natDegree_pow, linearFactor_natDegree, quadraticPolynomial_natDegree]
  push_cast
  ring

theorem exceptional_factor {f : ℤ[X]} (hm : f.Monic) (ht : TotallyPositive f)
    (hx : ∃ x ∈ realRoots f, auxiliaryQ x = 0) :
    ∃ g : ℤ[X], g.Monic ∧ 0 < g.natDegree ∧ g ∣ f ∧
      rootTrace g = 2 * (g.natDegree : ℝ) ∧ AllowedProduct g := by
  obtain ⟨x, hx, hQ⟩ := hx
  have hpos := ht.2 x hx
  have hfeval : (aeval x) f = 0 := by
    have he := (mem_roots (hm.map (Int.castRingHom ℝ)).ne_zero).mp hx
    have hφ : Int.castRingHom ℝ = algebraMap ℤ ℝ := by
      ext z
      simp
    simpa only [Polynomial.IsRoot, eval_map, aeval_def, hφ] using he
  have hbad : x = 2 ∨ quadratic 3 1 x = 0 := by
    by_contra h
    push Not at h
    have hr : Regular x := ⟨ne_of_gt hpos.1, hpos.2, h.1, h.2⟩
    exact ((regular_iff_auxiliaryQ_ne_zero x).mp hr) hQ
  rcases hbad with rfl | hbad
  · refine ⟨linearFactor, linearFactor_monic, by rw [linearFactor_natDegree]; omega,
      linearFactor_dvd_of_root hfeval, ?_, ?_⟩
    · norm_num [linearFactor_trace, linearFactor_natDegree]
    · exact ⟨1, 0, by simp⟩
  · refine ⟨quadraticPolynomial, quadraticPolynomial_monic,
      by rw [quadraticPolynomial_natDegree]; omega,
      quadraticPolynomial_dvd_of_root hfeval hbad, ?_, ?_⟩
    · norm_num [quadraticPolynomial_trace, quadraticPolynomial_natDegree]
    · exact ⟨0, 1, by simp⟩

theorem trace_bound_and_equality {f : ℤ[X]} (hm : f.Monic) (ht : TotallyPositive f) :
    2 * (f.natDegree : ℝ) ≤ rootTrace f ∧
      (rootTrace f = 2 * (f.natDegree : ℝ) → AllowedProduct f) := by
  suffices ∀ n : ℕ, ∀ f : ℤ[X], f.natDegree = n → f.Monic → TotallyPositive f →
      2 * (f.natDegree : ℝ) ≤ rootTrace f ∧
        (rootTrace f = 2 * (f.natDegree : ℝ) → AllowedProduct f) from
    this f.natDegree f rfl hm ht
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hdegree hm ht
    by_cases h0 : f.natDegree = 0
    · have hf : f = 1 := hm.natDegree_eq_zero.mp h0
      subst f
      simp only [natDegree_one, Nat.cast_zero, mul_zero, rootTrace_one, le_refl,
        true_and, forall_const]
      exact ⟨0, 0, by simp⟩
    by_cases hQ : ∀ x ∈ realRoots f, auxiliaryQ x ≠ 0
    · have hs := rootTrace_strict hm ht (Nat.pos_of_ne_zero h0) hQ
      exact ⟨hs.le, fun he => (ne_of_lt hs) he.symm |>.elim⟩
    · push Not at hQ
      obtain ⟨g, hgm, hgd, ⟨q, heq⟩, hgt, hgallowed⟩ := exceptional_factor hm ht hQ
      have hqm : q.Monic := hgm.of_mul_monic_left (heq ▸ hm)
      have hqt := totallyPositive_of_dvd hm hqm ht ⟨g, by rw [heq]; ring⟩
      have hd : f.natDegree = g.natDegree + q.natDegree :=
        heq ▸ hgm.natDegree_mul hqm
      have hlt : q.natDegree < n := by omega
      obtain ⟨hqbound, hqeq⟩ := ih q.natDegree hlt q rfl hqm hqt
      have htrace : rootTrace f = rootTrace g + rootTrace q :=
        heq ▸ rootTrace_mul hgm hqm
      constructor
      · rw [hd, Nat.cast_add, htrace, hgt]
        linarith
      · intro he
        have hqe : rootTrace q = 2 * (q.natDegree : ℝ) := by
          rw [htrace, hgt, hd, Nat.cast_add] at he
          linarith
        rw [heq]
        exact allowedProduct_mul hgallowed (hqeq hqe)

theorem rootTrace_classification {f : ℤ[X]} (hm : f.Monic) (ht : TotallyPositive f) :
    2 * (f.natDegree : ℝ) ≤ rootTrace f ∧
      (rootTrace f = 2 * (f.natDegree : ℝ) ↔ AllowedProduct f) := by
  obtain ⟨hb, he⟩ := trace_bound_and_equality hm ht
  exact ⟨hb, ⟨he, allowedProduct_trace⟩⟩

end ResearchMain.DominationRoots
