import TerminalLogConcavity.PhaseTransfer

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

def phaseError (z n : ℕ) : ℕ := (z ^ 2 + 3 * z + 1) ^ n - (z ^ 2) ^ n

theorem phaseError_add (z n : ℕ) : phaseError z n + (z ^ 2) ^ n = (z ^ 2 + 3 * z + 1) ^ n := by
  exact Nat.sub_add_cancel (Nat.pow_le_pow_left (by omega) n)

@[simp] theorem phaseError_one (z : ℕ) : phaseError z 1 = 3 * z + 1 := by
  simp only [phaseError,pow_one]
  omega

theorem phaseError_succ (z n : ℕ) :
    phaseError z (n + 1) = (z ^ 2 + 3 * z + 1) * phaseError z n + (3 * z + 1) * (z ^ 2) ^ n := by
  have h := phaseError_add z n
  have h' := phaseError_add z (n+1)
  rw [pow_succ (z^2) n, pow_succ (z^2+3*z+1) n] at h'
  have hh := congrArg (fun x => (z^2+3*z+1)*x) h
  nlinarith only [hh,h']

theorem CoeffLE.C_mono {a b : ℕ} (h : a ≤ b) : CoeffLE (C a) (C b) := by
  intro n
  by_cases hn : n = 0 <;> simp [hn,h]

theorem CoeffLE.pow_mono {P : ℕ[X]} (hP : CoeffLE 1 P) {n m : ℕ} (h : n ≤ m) : CoeffLE (P ^ n) (P ^ m) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  simpa [pow_add] using (CoeffLE.refl (P ^ n)).mul (hP.pow k)

private theorem linear_power_bound {P : ℕ[X]} (hP : CoeffLE 1 P) (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    CoeffLE (C a * P ^ n + C b * P) (C (a+b) * P ^ n) := by
  have h := (CoeffLE.refl (C a * P ^ n)).add ((CoeffLE.refl (C b)).mul (hP.pow_mono hn))
  simpa only [pow_one, C_add, add_mul] using h

/-- A scalar error controls every nonconstant phase of the three-state transfer. -/
theorem phaseVector_bounds {P : ℕ[X]} (hP : CoeffLE 1 P) {z : ℕ} (hz : 1 ≤ z)
    {n : ℕ} (hn : 1 ≤ n) :
    CoeffLE (phaseVector P z n).zero (C ((z^2+3*z+1)^n) * P^(n+1)) ∧
    CoeffLE (phaseVector P z n).one (C (phaseError z n) * P^(n+1)) ∧
    CoeffLE (phaseVector P z n).two (C ((z^2)^n) + C (phaseError z n) * P^(n+1)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  induction n with
  | zero =>
    have h0 := linear_power_bound hP (z^2+2) z (by decide : 1 ≤ 2)
    have h1 := linear_power_bound hP 2 z (by decide : 1 ≤ 2)
    have h2 := (CoeffLE.refl (C (z^2))).add
      ((CoeffLE.C_mono (show 2*z ≤ 3*z+1 by omega)).mul (hP.pow_mono (show 1 ≤ 2 by decide)))
    have h0' := h0.trans ((CoeffLE.C_mono (show z^2+2+z ≤ z^2+3*z+1 by omega)).mul (CoeffLE.refl _))
    have h1' := h1.trans ((CoeffLE.C_mono (show 2+z ≤ 3*z+1 by omega)).mul (CoeffLE.refl _))
    simp only [phaseError_one, pow_one]
    constructor
    · convert h0' using 1 ; simp only [phaseVector, C_add, C_ofNat, C_pow] ; ring
    constructor
    · convert h1' using 1 ; simp only [phaseVector, C_ofNat, C_pow] ; ring
    · convert h2 using 1 ; simp only [phaseVector, C_mul, C_ofNat, C_pow, pow_one] ; ring
  | succ n ih =>
    have ih' := ih (by omega)
    obtain ⟨h0,h1,h2⟩ := ih'
    let k := n+1
    let d := (z^2)^k
    let e := phaseError z k
    change CoeffLE (phaseVector P z k).zero (C ((z^2+3*z+1)^k)*P^(k+1)) at h0
    change CoeffLE (phaseVector P z k).one (C e*P^(k+1)) at h1
    change CoeffLE (phaseVector P z k).two (C d+C e*P^(k+1)) at h2
    have hadd := phaseError_add z k
    have hT := (h0.add h1).add ((CoeffLE.refl (C z)).mul h2)
    have hT' : CoeffLE ((phaseVector P z k).zero + (phaseVector P z k).one + C z * (phaseVector P z k).two)
        (C (z*d) + C (d+(z+2)*e) * P^(k+1)) := by
      convert hT using 1
      rw [← hadd]
      simp only [d,e,C_add,C_mul,C_ofNat]
      ring
    have h0raw := (CoeffLE.refl P).mul (hT'.add ((CoeffLE.refl (C (z^2))).mul h0))
    have h1raw := (CoeffLE.refl P).mul hT'
    have h2raw := (CoeffLE.refl (C z)).mul hT'
    have hraise : CoeffLE P (P^(k+2)) := by simpa using hP.pow_mono (show 1 ≤ k+2 by omega)
    have hstep : CoeffLE (P^(k+1)) (P^(k+2)) := hP.pow_mono (by omega)
    have herr := phaseError_succ z k
    constructor
    · have hr : CoeffLE (phaseVector P z (k+1)).zero
          (C (z*d)*P + C (d+(z+2)*e+z^2*((z^2+3*z+1)^k))*P^(k+2)) := by
        convert h0raw using 1 <;> simp only [phaseVector,C_add,C_mul,C_ofNat,pow_succ] ; ring
      have hraise' := ((CoeffLE.refl (C (z*d))).mul hraise).add
        (CoeffLE.refl (C (d+(z+2)*e+z^2*((z^2+3*z+1)^k))*P^(k+2)))
      apply hr.trans (hraise'.trans _)
      rw [← add_mul, ← C_add]
      apply (CoeffLE.C_mono _).mul (CoeffLE.refl _)
      rw [pow_succ (z^2+3*z+1) k, ← hadd]
      change z*d+(d+(z+2)*e+z^2*(e+d)) ≤ (e+d)*(z^2+3*z+1)
      have hd := Nat.mul_le_mul_right d (show z+1+z^2 ≤ z^2+3*z+1 by omega)
      have he := Nat.mul_le_mul_right e (show z+2+z^2 ≤ z^2+3*z+1 by omega)
      nlinarith only [hd,he]
    constructor
    · have hr : CoeffLE (phaseVector P z (k+1)).one
          (C (z*d)*P + C (d+(z+2)*e)*P^(k+2)) := by
        convert h1raw using 1 <;> simp only [phaseVector,C_add,C_mul,C_ofNat,pow_succ] ; ring
      have hraise' := ((CoeffLE.refl (C (z*d))).mul hraise).add (CoeffLE.refl (C (d+(z+2)*e)*P^(k+2)))
      apply hr.trans (hraise'.trans _)
      rw [← add_mul, ← C_add]
      apply (CoeffLE.C_mono _).mul (CoeffLE.refl _)
      rw [herr]
      change z*d+(d+(z+2)*e) ≤ (z^2+3*z+1)*e+(3*z+1)*d
      have hd := Nat.mul_le_mul_right d (show z+1 ≤ 3*z+1 by omega)
      have he := Nat.mul_le_mul_right e (show z+2 ≤ z^2+3*z+1 by omega)
      nlinarith only [hd,he]
    · have hr : CoeffLE (phaseVector P z (k+1)).two
          (C ((z^2)^(k+1)) + C (z*(d+(z+2)*e))*P^(k+1)) := by
        convert h2raw using 1 <;> simp only [phaseVector,C_add,C_mul,C_ofNat,pow_succ,d] ; ring_nf ; simp ; ring
      apply hr.trans
      apply (CoeffLE.refl _).add
      apply (CoeffLE.C_mono _).mul hstep
      rw [herr]
      change z*(d+(z+2)*e) ≤ (z^2+3*z+1)*e+(3*z+1)*d
      have hd := Nat.mul_le_mul_right d (show z ≤ 3*z+1 by omega)
      have he := Nat.mul_le_mul_right e (show z^2+2*z ≤ z^2+3*z+1 by omega)
      nlinarith only [hd,he]

theorem chainModel_upper_error {P : ℕ[X]} (hP : CoeffLE 1 P) {z : ℕ} (hz : 1 ≤ z)
    (u n : ℕ) :
    CoeffLE (chainModel P (C (z^2)) (endpointConstants z u n)).1
      (C ((z^2)^(n+1)) * (C u + P^(n+2)) +
        C ((u+2)*phaseError z (n+1)) * P^(n+2)) := by
  obtain ⟨h0,h1,h2⟩ := phaseVector_bounds hP hz (show 1 ≤ n+1 by omega)
  have h := (h0.add h1).add ((CoeffLE.refl (C u)).mul h2)
  rw [phaseVector_endpoint]
  convert h using 1
  rw [← phaseError_add z (n+1)]
  simp only [C_add,C_mul,C_ofNat]
  ring

end TerminalLogConcavity
