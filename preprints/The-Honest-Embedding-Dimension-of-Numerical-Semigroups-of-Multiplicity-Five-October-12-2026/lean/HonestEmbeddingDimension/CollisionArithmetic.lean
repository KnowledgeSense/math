import HonestEmbeddingDimension.SemigroupArithmetic

namespace HonestEmbeddingDimension

/-- Equal weighted residues reduce to equal residues of the coefficient pair. -/
theorem five_weighted_residue_cancel {a b k p q p' q' : ℕ}
    (ha : Nat.Coprime 5 a) (hb : b % 5 = (k * a) % 5)
    (h : (a * p + b * q) % 5 = (a * p' + b * q') % 5) :
    (p + k * q) % 5 = (p' + k * q') % 5 := by
  have hp : Nat.ModEq 5 (a * p + b * q) (a * (p + k * q)) := by
    have hh := (show Nat.ModEq 5 b (k * a) from hb).mul_right q
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.ModEq.refl (a * p)).add hh
  have hp' : Nat.ModEq 5 (a * p' + b * q') (a * (p' + k * q')) := by
    have hh := (show Nat.ModEq 5 b (k * a) from hb).mul_right q'
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.ModEq.refl (a * p')).add hh
  exact Nat.ModEq.cancel_left_of_coprime ha (hp.symm.trans ((show Nat.ModEq 5 _ _ from h).trans hp'))

/-- The paper's first-collision threshold for residue multiplier two. -/
theorem weighted_residue_injective_two {a b : ℕ} (_ha : 0 < a) (hab : a < b)
    (hcop : Nat.Coprime 5 a) (hb : b % 5 = (2 * a) % 5) :
    Set.InjOn (fun v : ℕ × ℕ => (a * v.1 + b * v.2) % 5)
      {v | a * v.1 + b * v.2 < 2 * a} := by
  rintro ⟨p, q⟩ hp ⟨p', q'⟩ hp' heq
  change a * p + b * q < 2 * a at hp
  change a * p' + b * q' < 2 * a at hp'
  have hp2 : p ≤ 1 := by nlinarith
  have hq2 : q ≤ 1 := by nlinarith
  have hpq : p + q ≤ 1 := by nlinarith
  have hp2' : p' ≤ 1 := by nlinarith
  have hq2' : q' ≤ 1 := by nlinarith
  have hpq' : p' + q' ≤ 1 := by nlinarith
  have hr := five_weighted_residue_cancel hcop hb heq
  rw [Nat.mod_eq_of_lt (show p + 2 * q < 5 from by omega),
    Nat.mod_eq_of_lt (show p' + 2 * q' < 5 from by omega)] at hr
  congr 1 <;> omega

/-- The paper's first-collision threshold for residue multiplier three. -/
theorem weighted_residue_injective_three {a b : ℕ} (_ha : 0 < a) (hab : a < b)
    (hcop : Nat.Coprime 5 a) (hb : b % 5 = (3 * a) % 5) :
    Set.InjOn (fun v : ℕ × ℕ => (a * v.1 + b * v.2) % 5)
      {v | a * v.1 + b * v.2 < min (3 * a) (2 * b)} := by
  rintro ⟨p, q⟩ hp ⟨p', q'⟩ hp' heq
  change a * p + b * q < min (3 * a) (2 * b) at hp
  change a * p' + b * q' < min (3 * a) (2 * b) at hp'
  have hpA := hp.trans_le (min_le_left _ _)
  have hpB := hp.trans_le (min_le_right _ _)
  have hpA' := hp'.trans_le (min_le_left _ _)
  have hpB' := hp'.trans_le (min_le_right _ _)
  have hp3 : p ≤ 2 := by nlinarith
  have hq2 : q ≤ 1 := by nlinarith
  have hpq : q = 1 → p ≤ 1 := by intro hq; subst q; nlinarith
  have hp3' : p' ≤ 2 := by nlinarith
  have hq2' : q' ≤ 1 := by nlinarith
  have hpq' : q' = 1 → p' ≤ 1 := by intro hq; subst q'; nlinarith
  have hr := five_weighted_residue_cancel hcop hb heq
  rw [Nat.mod_eq_of_lt (show p + 3 * q < 5 from by omega),
    Nat.mod_eq_of_lt (show p' + 3 * q' < 5 from by omega)] at hr
  congr 1 <;> omega

/-- The paper's first-collision threshold for residue multiplier four. -/
theorem weighted_residue_injective_four {a b : ℕ} (_ha : 0 < a) (hab : a < b)
    (hcop : Nat.Coprime 5 a) (hb : b % 5 = (4 * a) % 5) :
    Set.InjOn (fun v : ℕ × ℕ => (a * v.1 + b * v.2) % 5)
      {v | a * v.1 + b * v.2 < min (a + b) (4 * a)} := by
  rintro ⟨p, q⟩ hp ⟨p', q'⟩ hp' heq
  change a * p + b * q < min (a + b) (4 * a) at hp
  change a * p' + b * q' < min (a + b) (4 * a) at hp'
  have hpA := hp.trans_le (min_le_left _ _)
  have hpB := hp.trans_le (min_le_right _ _)
  have hpA' := hp'.trans_le (min_le_left _ _)
  have hpB' := hp'.trans_le (min_le_right _ _)
  have hp4 : p ≤ 3 := by nlinarith
  have hq2 : q ≤ 1 := by nlinarith
  have hpq : q = 1 → p = 0 := by intro hq; subst q; nlinarith
  have hp4' : p' ≤ 3 := by nlinarith
  have hq2' : q' ≤ 1 := by nlinarith
  have hpq' : q' = 1 → p' = 0 := by intro hq; subst q'; nlinarith
  have hr := five_weighted_residue_cancel hcop hb heq
  rw [Nat.mod_eq_of_lt (show p + 4 * q < 5 from by omega),
    Nat.mod_eq_of_lt (show p' + 4 * q' < 5 from by omega)] at hr
  congr 1 <;> omega

/-- Two distinct factorizations in the actual generators `5,a,b`. -/
def HasTwoFactorizations (a b n : ℕ) : Prop :=
  ∃ x p q x' p' q', n = 5 * x + a * p + b * q ∧
    n = 5 * x' + a * p' + b * q' ∧ (x ≠ x' ∨ p ≠ p' ∨ q ≠ q')

theorem exists_two_factorizations (a b : ℕ) : ∃ n, HasTwoFactorizations a b n := by
  refine ⟨5 * a, a, 0, 0, 0, 5, 0, ?_, ?_, ?_⟩
  · simp
  · simp [Nat.mul_comm]
  · omega

/-- The first collision is defined by the original least-double-factorization property. -/
noncomputable def firstCollision (a b : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_two_factorizations a b)

theorem firstCollision_spec (a b : ℕ) : HasTwoFactorizations a b (firstCollision a b) := by
  classical
  exact Nat.find_spec (exists_two_factorizations a b)

theorem firstCollision_le {a b n : ℕ} (hn : HasTwoFactorizations a b n) :
    firstCollision a b ≤ n := by
  classical
  exact Nat.find_min' (exists_two_factorizations a b) hn

theorem firstCollision_representation (a b : ℕ) :
    ∃ x p q, firstCollision a b = 5 * x + a * p + b * q := by
  obtain ⟨x, p, q, _, _, _, h, _, _⟩ := firstCollision_spec a b
  exact ⟨x, p, q, h⟩

/-- Pair-residue independence below a witnessed collision proves the exact least collision. -/
theorem firstCollision_eq_of_residue_injective {a b L : ℕ}
    (hL : HasTwoFactorizations a b L)
    (hinj : Set.InjOn (fun v : ℕ × ℕ => (a * v.1 + b * v.2) % 5)
      {v | a * v.1 + b * v.2 < L}) : firstCollision a b = L := by
  apply le_antisymm (firstCollision_le hL)
  by_contra hh
  have hlt : firstCollision a b < L := by omega
  obtain ⟨x, p, q, x', p', q', heq, heq', hne⟩ := firstCollision_spec a b
  have hpair : (p, q) = (p', q') := by
    apply hinj (by change a * p + b * q < L; omega)
      (by change a * p' + b * q' < L; omega)
    change (a * p + b * q) % 5 = (a * p' + b * q') % 5
    have hmod := congrArg (fun n : ℕ => n % 5) (heq.symm.trans heq')
    simpa [Nat.add_mod] using hmod
  have hp : p = p' := congrArg Prod.fst hpair
  have hq : q = q' := congrArg Prod.snd hpair
  subst p'
  subst q'
  omega

/-- The relation `k*a = 5*u+b` gives an actual double factorization. -/
theorem collision_multiple_a {a b k : ℕ} (_hk : k ≠ 0)
    (hba : b ≤ k * a) (hb : b % 5 = (k * a) % 5) :
    HasTwoFactorizations a b (k * a) := by
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_exists_eq_add hba).mp hb
  refine ⟨0, k, 0, u, 0, 1, ?_, ?_, ?_⟩
  · simp [Nat.mul_comm]
  · omega
  · omega

/-- The relation `k*b = 5*u+a` gives an actual double factorization. -/
theorem collision_multiple_b {a b k : ℕ} (_hk : k ≠ 0)
    (hab : a ≤ k * b) (ha : a % 5 = (k * b) % 5) :
    HasTwoFactorizations a b (k * b) := by
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_exists_eq_add hab).mp ha
  refine ⟨0, 0, k, u, 1, 0, ?_, ?_, ?_⟩
  · simp [Nat.mul_comm]
  · omega
  · omega

/-- The relation `a+b = 5*u` gives an actual double factorization. -/
theorem collision_sum {a b : ℕ} (hab : (a + b) % 5 = 0) :
    HasTwoFactorizations a b (a + b) := by
  obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero hab
  refine ⟨0, 1, 1, u, 0, 0, ?_, ?_, ?_⟩
  · simp
  · omega
  · omega

/-- Lemma 3.2, the complete first-collision formula in residue case two. -/
theorem firstCollision_eq_two {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hba : b < 2 * a) (hcop : Nat.Coprime 5 a) (hb : b % 5 = (2 * a) % 5) :
    firstCollision a b = 2 * a :=
  firstCollision_eq_of_residue_injective (collision_multiple_a (by omega) hba.le hb)
    (weighted_residue_injective_two ha hab hcop hb)

/-- Lemma 3.2, the complete first-collision formula in residue case three. -/
theorem firstCollision_eq_three {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hba : b < 3 * a) (hcop : Nat.Coprime 5 a) (hb : b % 5 = (3 * a) % 5) :
    firstCollision a b = min (3 * a) (2 * b) := by
  apply firstCollision_eq_of_residue_injective _
    (weighted_residue_injective_three ha hab hcop hb)
  rcases le_total (3 * a) (2 * b) with hle | hle
  · rw [min_eq_left hle]
    exact collision_multiple_a (by omega) hba.le hb
  · rw [min_eq_right hle]
    exact collision_multiple_b (by omega) (by omega) (by omega)

/-- Lemma 3.2, the complete first-collision formula in residue case four. -/
theorem firstCollision_eq_four {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hba : b < 4 * a) (hcop : Nat.Coprime 5 a) (hb : b % 5 = (4 * a) % 5) :
    firstCollision a b = min (a + b) (4 * a) := by
  apply firstCollision_eq_of_residue_injective _
    (weighted_residue_injective_four ha hab hcop hb)
  rcases le_total (a + b) (4 * a) with hle | hle
  · rw [min_eq_left hle]
    exact collision_sum (by omega)
  · rw [min_eq_right hle]
    exact collision_multiple_a (by omega) hba.le hb

end HonestEmbeddingDimension
