import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
namespace HankelAutomaticity

/-- Number of ones in the ordinary binary expansion. -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The original integer Hankel determinant, including the empty order. -/
def determinant (n : ℕ) : ℤ :=
  Matrix.det (fun i j : Fin n => (digitSum (i.val+j.val) : ℤ))

/-- The lower binary digits have weight one; the digit in position `L+1`
has weight `x`. Matrix arguments below never reach a higher position. -/
def weightedMoment (L : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  (digitSum (n % 2^(L+1)) : ℚ) + (n / 2^(L+1) : ℕ)*x

def hankelMatrix (L n : ℕ) (x : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => weightedMoment L x (i.val+j.val)

def hankel (L n : ℕ) (x : ℚ) : ℚ := (hankelMatrix L n x).det

@[simp] theorem digitSum_zero : digitSum 0=0 := by simp [digitSum]
@[simp] theorem digitSum_one : digitSum 1=1 := by decide

 theorem digitSum_add_pow {L n : ℕ} (hn : n<2^L) :
    digitSum (n+2^L)=digitSum n+1 := by
  have hl : (Nat.digits 2 n).length ≤ L :=
    (Nat.digits_length_le_iff (by decide : 1<2) n).mpr hn
  have h := Nat.digits_append_zeroes_append_digits (b:=2)
    (k:=L-(Nat.digits 2 n).length) (m:=1) (n:=n) (by decide) (by decide)
  rw [Nat.add_sub_of_le hl, mul_one] at h
  unfold digitSum
  rw [← h, List.sum_append, List.sum_append]
  simp

 theorem digitSum_split {L n : ℕ} (hn : n<2^(L+1)) :
    digitSum n = digitSum (n%2^L)+n/2^L := by
  have hp : 0<2^L := by positivity
  have hq : n/2^L<2 := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    simpa [pow_succ, Nat.mul_comm] using hn
  have hq01 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hq)
  rcases hq01 with hq | hq
  · have hlt : n<2^L := (Nat.div_eq_zero_iff.mp hq).resolve_left hp.ne'
    simp [Nat.mod_eq_of_lt hlt, hq]
  · have he : n=n%2^L+2^L := by
      have h := Nat.mod_add_div n (2^L)
      rw [hq, mul_one] at h
      exact h.symm
    rw [he]
    have hm := Nat.mod_lt n hp
    rw [digitSum_add_pow hm]
    simp [Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm]

 theorem weightedMoment_one {L n : ℕ} (hn : n<2^(L+2)) :
    weightedMoment L 1 n = digitSum n := by
  have h := digitSum_split (L:=L+1) (n:=n) (by simpa [Nat.add_assoc] using hn)
  simp only [weightedMoment, mul_one, h, Nat.cast_add]

 theorem hankel_one {L n : ℕ} (hn : n≤2^(L+1)) :
    hankel L n 1 = (determinant n : ℚ) := by
  have hm : hankelMatrix L n 1 = fun i j : Fin n => (digitSum (i.val+j.val) : ℚ) := by
    ext i j
    apply weightedMoment_one
    have hi := i.isLt
    have hj := j.isLt
    have hp : 2^(L+2)=2*2^(L+1) := by rw [show L+2=(L+1)+1 by omega, pow_succ]; ring
    omega
  unfold hankel determinant
  rw [hm]
  exact (Int.castRingHom ℚ).map_det _ |>.symm

 theorem digitSum_eq_count_bits (n : ℕ) : digitSum n=n.bits.count true := by
  unfold digitSum
  rw [Nat.digits_two_eq_bits]
  induction n.bits with
  | nil => rfl
  | cons b w ih => cases b <;> simp_all [Nat.add_comm]

end HankelAutomaticity
