/-
Adapted from stormj-UH/spivak-lean, TranscendencePi and TranscendencePiAux.
Copyright 2026 Jon-Erik G. Storm. Licensed under Apache-2.0.
Changes: project-local namespace and imports; isolated polynomial reduction.
See THIRD_PARTY_NOTICES.md and LICENSE-APACHE-2.0.md.
-/
/-
# `π` is transcendental (Lindemann, 1882)

`Spivak.TranscendencePi.transcendental_pi : Transcendental ℚ Real.pi`, and
`Spivak.TranscendencePi.transcendental_int_pi : Transcendental ℤ Real.pi`.

The proof is the classical one of Hermite–Lindemann as streamlined by Niven.
Suppose `π` is algebraic.  Then so is `iπ`; let `P ∈ ℤ[X]` be a nonzero polynomial
with `P(iπ) = 0`, with leading coefficient `a` and complex roots `α₁, …, α_n`
(with multiplicity).  Since `e^{iπ} = −1`,

    0 = ∏ⱼ (1 + e^{αⱼ}) = ∑_{t ⊆ {1,…,n}} e^{βₜ},      βₜ = ∑_{j∈t} αⱼ.

* The numbers `a·βₜ` are the roots of `q = ∏ₜ (X − a·βₜ)`, whose coefficients are
  symmetric integer polynomials in the algebraic integers `a·αⱼ`; by the fundamental
  theorem of symmetric polynomials and Vieta, `q ∈ ℤ[X]` (`TranscendencePiAux`).
* Write `q = X^m · F` with `F(0) ≠ 0`; the `k₀ ≥ 1` exponents `βₜ = 0` contribute
  `k₀` to the sum, so `k₀ + ∑_{βₜ ≠ 0} e^{βₜ} = 0`.  The polynomial
  `G(X) = F(aX) ∈ ℤ[X]` has `G(0) ≠ 0` and vanishes at every nonzero `βₜ`.
* Mathlib's analytic half of Lindemann–Weierstrass,
  `LindemannWeierstrass.exp_polynomial_approx`, applied to `G` gives for each large
  prime `p` an integer `nₚ` with `p ∤ nₚ` and `gₚ ∈ ℤ[X]` with
  `|nₚ e^{β} − p gₚ(β)| ≤ c^p/(p−1)!` at the roots of `G`.
* With `D = deg gₚ` and `h = a^D gₚ(X/a) ∈ ℤ[X]` (`scaleRoots`), the number
  `N = a^D k₀ nₚ + p ∑_{βₜ≠0} h(a βₜ)` is an integer (again by symmetry), is not
  divisible by `p`, and equals `−a^D ∑_{βₜ≠0} (nₚ e^{βₜ} − p gₚ(βₜ))`, whose absolute
  value is at most `#·(|a|^{deg G}|c|)^p/(p−1)! → 0`.  Contradiction.
-/
import OscillatoryRecurrence.TranscendencePiAux
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.Analysis.SpecificLimits.Normed

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace OscillatoryRecurrence
namespace TranscendencePi

open Polynomial Filter Finset
open scoped Nat Topology

/-- **Core of the argument.**  No nonzero integer polynomial has a complex root `z`
with `e^z = −1`. -/
theorem no_root_exp_eq_neg_one (P : ℤ[X]) (hP : P ≠ 0) {z : ℂ} (hz : z ∈ P.aroots ℂ)
    (hez : Complex.exp z = -1) : False := by
  classical
  set a : ℤ := P.leadingCoeff with hadef
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  obtain ⟨n, x, hx⟩ := exists_enum (P.aroots ℂ)
  set y : Fin n → ℂ := fun j => (a : ℂ) * x j with hydef
  have hy : ∀ k, IsInt ((univ.val.map y).esymm k) := by
    intro k
    have : univ.val.map y = (P.aroots ℂ).map (fun w => (a : ℂ) * w) := by
      rw [← hx, Multiset.map_map]; rfl
    rw [this]; exact esymm_int_of_roots P hP k
  /- the polynomial of scaled subset sums has integer coefficients -/
  set q : ℂ[X] := ∏ t : Finset (Fin n), (X - C (∑ j ∈ t, y j)) with hqdef
  have hqint : ∀ k, IsInt (q.coeff k) := by
    intro k
    rw [hqdef, ← genericProd_map, coeff_map]
    exact sym_int _ (genericProd_coeff_isSymmetric n k) y hy
  obtain ⟨Qz, hQz⟩ := exists_lift q hqint
  have hqmonic : q.Monic := monic_prod_of_monic _ _ (fun t _ => monic_X_sub_C _)
  have hQz0 : Qz ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hQz
    exact hqmonic.ne_zero hQz.symm
  obtain ⟨m, Fz, hFz, hFz0, hQeq⟩ := exists_eval_zero_ne Qz hQz0
  /- the multiset of scaled subset sums, split into zero and nonzero ones -/
  set R : Multiset ℂ := univ.val.map (fun t : Finset (Fin n) => ∑ j ∈ t, y j) with hRdef
  set k₀ : ℕ := R.count 0 with hk₀
  set R' : Multiset ℂ := R.filter (fun r => ¬ r = 0) with hR'
  have hk₀pos : 0 < k₀ := by
    rw [hk₀, Multiset.count_pos, hRdef, Multiset.mem_map]
    exact ⟨∅, Finset.mem_val.mpr (Finset.mem_univ _), by simp⟩
  have hsplit : ∀ f : ℂ → ℂ, (R.map f).sum = k₀ * f 0 + (R'.map f).sum := by
    intro f
    conv_lhs => rw [← Multiset.filter_add_not (· = 0) R]
    rw [Multiset.map_add, Multiset.sum_add, Multiset.filter_eq', Multiset.map_replicate,
      Multiset.sum_replicate, nsmul_eq_mul]
  /- the exponential relation -/
  have hexpR : (R.map (fun r => Complex.exp (r / a))).sum = 0 := by
    have key : ∀ t : Finset (Fin n),
        Complex.exp ((∑ j ∈ t, y j) / a) = ∏ j ∈ t, Complex.exp (x j) := by
      intro t
      rw [← Complex.exp_sum]
      congr 1
      rw [hydef, ← Finset.mul_sum]
      field_simp
    rw [hRdef, Multiset.map_map]
    change ∑ t : Finset (Fin n), Complex.exp ((∑ j ∈ t, y j) / a) = 0
    simp_rw [key]
    rw [← Finset.powerset_univ, ← Finset.prod_one_add]
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp (hx ▸ hz)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, hez]; ring)
  have hexpR' : (k₀ : ℂ) + (R'.map (fun r => Complex.exp (r / a))).sum = 0 := by
    have := hsplit (fun r => Complex.exp (r / a))
    rw [hexpR] at this
    simp only [zero_div, Complex.exp_zero, mul_one] at this
    linear_combination -this
  /- the auxiliary polynomial `G(X) = F(aX)` -/
  set G : ℤ[X] := Fz.comp (C a * X) with hGdef
  have hG0 : G.eval 0 ≠ 0 := by simpa [hGdef, eval_comp] using hFz0
  have hGne : G ≠ 0 := fun h => hG0 (by rw [h]; simp)
  have hGroot : ∀ r ∈ R', r / a ∈ G.aroots ℂ := by
    intro r hr
    rw [hR', Multiset.mem_filter] at hr
    obtain ⟨hrR, hr0⟩ := hr
    rw [mem_aroots]
    refine ⟨?_, ?_⟩
    · exact hGne
    · have hq0 : q.eval r = 0 := by
        rw [hqdef, eval_prod]
        obtain ⟨t, -, ht⟩ := Multiset.mem_map.mp hrR
        exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])
      have hQ : aeval r Qz = 0 := by
        rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, hQz]
        exact hq0
      rw [hQeq, map_mul, map_pow, aeval_X] at hQ
      have hF : aeval r Fz = 0 := (mul_eq_zero.mp hQ).resolve_left (pow_ne_zero _ hr0)
      rw [hGdef, aeval_comp]
      simp only [map_mul, aeval_X, map_intCast, eq_intCast]
      rw [mul_div_cancel₀ _ haC]
      exact hF
  /- the analytic input -/
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx G hG0
  set K : ℕ := G.natDegree with hKdef
  set C₀ : ℝ := |(a : ℝ)| ^ K * |c| with hC₀
  set A : ℝ := (Multiset.card R' : ℝ) with hAdef
  have hlim : Tendsto (fun N : ℕ => A * C₀ * (C₀ ^ N / N !)) atTop (𝓝 0) := by
    have h := FloorSemiring.tendsto_pow_div_factorial_atTop C₀
    simpa using h.const_mul (A * C₀)
  obtain ⟨P0, hP0⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)))
  obtain ⟨p, hpge, hpprime⟩ :=
    Nat.exists_infinite_primes (P0 + 1 + (G.eval 0).natAbs + a.natAbs + k₀ + 1)
  have hpP : P0 ≤ p - 1 := by omega
  have hpG : p > (G.eval 0).natAbs := by omega
  have hpa : a.natAbs < p := by omega
  have hpk : k₀ < p := by omega
  obtain ⟨nn, hpn, gp, hgpdeg, hgp⟩ := hc p hpG hpprime
  /- rescaling `gₚ` -/
  set D : ℕ := gp.natDegree with hDdef
  set h : ℤ[X] := gp.scaleRoots a with hhdef
  have hh : ∀ r : ℂ, aeval r h = (a : ℂ) ^ D * aeval (r / (a : ℂ)) gp := by
    intro r
    have := scaleRoots_eval₂_mul (algebraMap ℤ ℂ) (r / (a : ℂ)) a (p := gp)
    rw [show (algebraMap ℤ ℂ) a * (r / (a : ℂ)) = r by
      rw [algebraMap_int_eq, eq_intCast, mul_div_cancel₀ _ haC]] at this
    rw [aeval_def, aeval_def, this, algebraMap_int_eq, eq_intCast]
  /- the integer `J = ∑_{r ∈ R'} h(r)` -/
  obtain ⟨T, hT⟩ := sym_int _ (genericSum_isSymmetric n h) y hy
  rw [genericSum_aeval] at hT
  have hTR : (R.map (fun r : ℂ => aeval r h)).sum =
      ∑ t : Finset (Fin n), aeval (∑ j ∈ t, y j) h := by
    rw [hRdef, Multiset.map_map]; rfl
  have hsJ := hsplit (fun r : ℂ => aeval r h)
  have h0 : aeval (0 : ℂ) h = ((h.coeff 0 : ℤ) : ℂ) := by
    rw [aeval_def, eval₂_at_zero, algebraMap_int_eq, eq_intCast]
  set Jz : ℤ := T - k₀ * h.coeff 0 with hJzdef
  have hJ : (Jz : ℂ) = (R'.map (fun r : ℂ => aeval r h)).sum := by
    rw [hJzdef]
    push_cast
    rw [← hT, ← hTR, hsJ, h0]
    ring
  /- the integer `N` -/
  set N : ℤ := a ^ D * k₀ * nn + p * Jz with hNdef
  have hJ' : (R'.map (fun r : ℂ => aeval r h)).sum =
      (a : ℂ) ^ D * (R'.map (fun r : ℂ => aeval (r / (a : ℂ)) gp)).sum := by
    rw [← Multiset.sum_map_mul_left]
    congr 1
    exact Multiset.map_congr rfl (fun r _ => hh r)
  have hE : (R'.map (fun r : ℂ => Complex.exp (r / (a : ℂ)))).sum = -(k₀ : ℂ) := by
    linear_combination hexpR'
  have hNC : (N : ℂ) = -((a : ℂ) ^ D * (R'.map (fun r : ℂ =>
      (nn : ℂ) * Complex.exp (r / (a : ℂ)) - p * aeval (r / (a : ℂ)) gp)).sum) := by
    rw [Multiset.sum_map_sub, Multiset.sum_map_mul_left, Multiset.sum_map_mul_left]
    rw [hNdef]
    push_cast
    rw [hJ, hJ', hE]
    ring
  /- upper bound -/
  have hbd : ∀ r ∈ R', ‖(fun r : ℂ => (nn : ℂ) * Complex.exp (r / (a : ℂ)) - p * aeval (r / (a : ℂ)) gp) r‖ ≤
      c ^ p / (p - 1)! := by
    intro r hr
    have := hgp (hGroot r hr)
    rwa [zsmul_eq_mul, nsmul_eq_mul] at this
  have hsum := norm_sum_le_card_mul _ _ hbd
  have hnormN : ‖(N : ℂ)‖ = |(N : ℝ)| := Complex.norm_intCast N
  have hA0 : 0 ≤ A := by positivity
  have hfac : (0 : ℝ) < ((p - 1)! : ℝ) := by positivity
  have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs ha
  have hNle : |(N : ℝ)| ≤ |(a : ℝ)| ^ D * (A * (c ^ p / (p - 1)!)) := by
    rw [← hnormN, hNC, norm_neg, norm_mul, norm_pow]
    have : ‖(a : ℂ)‖ = |(a : ℝ)| := Complex.norm_intCast a
    rw [this]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hDle : D ≤ p * K := by
    have := hgpdeg; omega
  have hNle2 : |(N : ℝ)| ≤ A * C₀ * (C₀ ^ (p - 1) / (p - 1)!) := by
    refine hNle.trans ?_
    have hc1 : c ^ p ≤ |c| ^ p := le_trans (le_abs_self _) (le_of_eq (abs_pow c p))
    have step1 : A * (c ^ p / (p - 1)!) ≤ A * (|c| ^ p / (p - 1)!) := by
      apply mul_le_mul_of_nonneg_left _ hA0
      exact div_le_div_of_nonneg_right hc1 hfac.le
    have step2 : |(a : ℝ)| ^ D ≤ |(a : ℝ)| ^ (p * K) := pow_le_pow_right₀ ha1 hDle
    have hpos : 0 ≤ A * (|c| ^ p / (p - 1)!) := by positivity
    calc |(a : ℝ)| ^ D * (A * (c ^ p / (p - 1)!))
        ≤ |(a : ℝ)| ^ (p * K) * (A * (|c| ^ p / (p - 1)!)) :=
          mul_le_mul step2 step1 (by
            have := norm_nonneg ((R'.map (fun r : ℂ =>
              (nn : ℂ) * Complex.exp (r / (a : ℂ)) - p * aeval (r / (a : ℂ)) gp)).sum)
            linarith) (by positivity)
      _ = A * C₀ ^ p / (p - 1)! := by
          rw [hC₀, mul_pow, ← pow_mul, mul_comm K p]; ring
      _ = A * C₀ * (C₀ ^ (p - 1) / (p - 1)!) := by
          have : C₀ ^ p = C₀ * C₀ ^ (p - 1) := by
            rw [← pow_succ']; congr 1; have := hpprime.one_lt; omega
          rw [this]; ring
  /- lower bound: `p ∤ N` -/
  have hNne : N ≠ 0 := by
    intro hN0
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
    have hdvd : (p : ℤ) ∣ a ^ D * k₀ * nn := ⟨-Jz, by rw [hNdef] at hN0; linarith⟩
    rcases hpZ.dvd_mul.mp hdvd with h1 | h1
    · rcases hpZ.dvd_mul.mp h1 with h2 | h2
      · have h3 := hpZ.dvd_of_dvd_pow h2
        have := Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr h3)
        rw [Int.abs_eq_natAbs] at this
        omega
      · have := Int.le_of_dvd (by exact_mod_cast hk₀pos) h2
        omega
    · exact hpn h1
  have hNge : (1 : ℝ) ≤ |(N : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hNne
  have := hP0 (p - 1) hpP
  linarith

/-- **Lindemann's theorem: `π` is transcendental** (over `ℚ`). -/
theorem transcendental_pi : Transcendental ℚ Real.pi := by
  intro h
  obtain ⟨P, hP, hPz⟩ := exists_int_poly_of_isAlgebraic (isAlgebraic_I_mul_pi h)
  refine no_root_exp_eq_neg_one P hP (z := Complex.I * (Real.pi : ℂ)) ?_ ?_
  · rw [mem_aroots]; exact ⟨hP, hPz⟩
  · rw [mul_comm]; exact Complex.exp_pi_mul_I

/-- **`π` is transcendental over `ℤ`**: no nonzero integer polynomial vanishes at `π`. -/
theorem transcendental_int_pi : Transcendental ℤ Real.pi :=
  transcendental_pi.restrictScalars (RingHom.injective_int (algebraMap ℤ ℚ))

end TranscendencePi
end OscillatoryRecurrence
