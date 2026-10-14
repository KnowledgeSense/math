import TerminalLogConcavity.ChainLower
import TerminalLogConcavity.PhaseUpper
import TerminalLogConcavity.PhaseError

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

theorem site_constants_endpoint (a q i : ℕ) (hq : 2 ≤ q) :
    ((List.range q).map (fun k => (C (a ^ siteParameter q i (k+1)) : ℕ[X]))) =
      endpointConstants (a ^ baseCoupling q) (a ^ (i^2)) (q-2) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hq
  have first : siteParameter (2+n) i 1 = baseCoupling (2+n) + i^2 := by
    simp [siteParameter,endpointWeight]
  have last : siteParameter (2+n) i (2+n) = baseCoupling (2+n) := by
    simp [siteParameter,endpointWeight,show 2+n ≠ 1 by omega]
  have mid (k : ℕ) (hk : k ∈ List.range n) : siteParameter (2+n) i (k+2) = 2*baseCoupling (2+n) := by
    have hk' := List.mem_range.mp hk
    simp [siteParameter,endpointWeight,show k+2 ≠ 1 by omega,show k+2 ≠ 2+n by omega,Nat.mul_comm]
  have hq' : 2+n = (n+1)+1 := by omega
  rw [hq',List.range_succ_eq_map,List.map_cons,List.map_map,List.range_succ]
  simp only [List.map_append,List.map_cons,List.map_nil,Function.comp_def]
  have hm : (List.map (fun k => (C (a ^ siteParameter (2+n) i (k+2)) : ℕ[X])) (List.range n)) =
      List.replicate n (C ((a ^ baseCoupling (2+n))^2)) := by
    conv_rhs => arg 1; rw [← List.length_range (n := n)]
    apply List.map_eq_replicate_iff.mpr
    intro k hk
    rw [mid k hk, ← pow_mul, Nat.mul_comm (baseCoupling (2+n)) 2]
  have h1 : 0+1=1 := rfl
  simp only [Nat.succ_eq_add_one] at *
  rw [show n+1+1=2+n by omega]
  change C (a ^ siteParameter (2+n) i 1) ::
    (List.map (fun k => C (a ^ siteParameter (2+n) i (k+1+1))) (List.range n) ++
      [C (a ^ siteParameter (2+n) i (2+n))]) = _
  rw [show (fun k => (C (a ^ siteParameter (2+n) i (k+1+1)) : ℕ[X])) =
      (fun k => C (a ^ siteParameter (2+n) i (k+2))) by rfl, hm, first, last]
  simp only [endpointConstants,interiorConstants,show 2+n-2=n by omega,pow_add]
  rw [Nat.mul_comm (a ^ baseCoupling (2+n))]

theorem lowerChain_upper_error {q : ℕ} (hq : 2 ≤ q) (t i : ℕ) :
    CoeffLE (lowerChain q t i)
      (chainPhasePolynomial q t i +
        C ((amplifier t ^ (i^2)+2)*phaseError (amplifier t ^ baseCoupling q) (q-1)) *
          lowerSiteP q t i ^ q) := by
  have hz : 1 ≤ amplifier t ^ baseCoupling q := Nat.one_le_pow _ _ (amplifier_pos t)
  have hP : CoeffLE 1 (lowerSiteP q t i) := CoeffLE.le_add_right _ _
  have h := chainModel_upper_error hP hz (amplifier t ^ (i^2)) (q-2)
  have hq1 : q-2+1=q-1 := by omega
  have hq2 : q-2+2=q := by omega
  rw [hq1,hq2, ← site_constants_endpoint _ _ _ hq] at h
  have he : (amplifier t ^ baseCoupling q)^2 = amplifier t ^ (2*baseCoupling q) := by
    rw [← pow_mul,Nat.mul_comm (baseCoupling q) 2]
  rw [he] at h
  have hr : (chainModel (lowerSiteP q t i) (C (amplifier t ^ (2*baseCoupling q)))
      ((List.range q).map (fun k => C (amplifier t ^ siteParameter q i (k+1))))).1 = lowerChain q t i := by
    simp only [chainModel,chainWeights,lowerChain,lowerSiteWeight,lowerCouplerWeight,List.map_map,Function.comp_def]
  rw [hr, ← pow_mul] at h
  exact h

theorem lowerChain_phase_scaled {q : ℕ} (hq : 2 ≤ q) (t i j : ℕ)
    (ha : 128*q^4 ≤ amplifier t) (hi : i ≤ q) :
    4*q*(lowerChain q t i).coeff j ≤ (4*q+1)*(chainPhasePolynomial q t i).coeff j := by
  have h := lowerChain_upper_error hq t i j
  simp only [coeff_add, coeff_C_mul] at h
  have he := transfer_row_error_nat hq ha hi
  change 4*q*(amplifier t^(i^2)+2)*phaseError (amplifier t^baseCoupling q) (q-1) ≤
    ((amplifier t^baseCoupling q)^2)^(q-1) at he
  have hpow : ((amplifier t^baseCoupling q)^2)^(q-1) =
      amplifier t^(2*baseCoupling q*(q-1)) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hpow] at he
  have hbase : amplifier t^(2*baseCoupling q*(q-1)) * (lowerSiteP q t i ^ q).coeff j ≤
      (chainPhasePolynomial q t i).coeff j := by
    simp only [chainPhasePolynomial,coeff_C_mul,coeff_add]
    exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  have he' := Nat.mul_le_mul_right ((lowerSiteP q t i ^ q).coeff j) he
  have h' := Nat.mul_le_mul_left (4*q) h
  nlinarith only [h',he',hbase]

end TerminalLogConcavity
