import Dowling.PartitionCounting

noncomputable section
namespace Dowling
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G]

theorem sum_ite_roots {R : Type*} [CommSemiring R] (n k : ℕ) (c : R) :
    (∑ p : GainPartition G n, if p.roots.card = k then c else 0) =
      (whitneyCount G n k : R)*c := by
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rfl

theorem whitneyCount_succ_succ (n k : ℕ) :
    whitneyCount G (n+1) (k+1) = whitneyCount G n k +
      (1+Fintype.card G*(k+1))*whitneyCount G n (k+1) := by
  have h := sum_partitions_succ (G := G) n (fun j => if j=k+1 then (1:ℕ) else 0)
  rw [sum_ite_roots] at h
  simp only [Nat.cast_id,mul_one,Nat.add_right_cancel_iff,mul_ite,mul_one,mul_zero] at h
  have he (p : GainPartition G n) :
      (if p.roots.card=k+1 then 1+Fintype.card G*p.roots.card else 0) =
      (if p.roots.card=k+1 then 1+Fintype.card G*(k+1) else 0) := by
    split <;> simp_all
  simp_rw [he] at h
  rw [Finset.sum_add_distrib,sum_ite_roots,sum_ite_roots] at h
  simpa only [Nat.cast_id,mul_one,mul_comm] using h

theorem whitneyCount_succ_zero (n : ℕ) : whitneyCount G (n+1) 0 = whitneyCount G n 0 := by
  have h := sum_partitions_succ (G := G) n (fun j => if j=0 then (1:ℕ) else 0)
  rw [sum_ite_roots] at h
  simp only [Nat.cast_id,mul_one,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,zero_add,
    mul_ite,mul_one,mul_zero] at h
  have he (p : GainPartition G n) :
      (if p.roots.card=0 then 1+Fintype.card G*p.roots.card else 0) =
      (if p.roots.card=0 then 1 else 0) := by split <;> simp_all
  simp_rw [he] at h
  rw [sum_ite_roots] at h
  simpa using h

omit [Fintype G] in
theorem zero_partition_unique (p : GainPartition G 0) : p = GainPartition.discrete := by
  apply GainPartition.code_injective
  funext i
  exact Fin.elim0 i

instance : Unique (GainPartition G 0) where
  default := GainPartition.discrete
  uniq := zero_partition_unique

theorem whitneyCount_zero (k : ℕ) : whitneyCount G 0 k = if k=0 then 1 else 0 := by
  have h := sum_ite_roots (G := G) 0 k (1:ℕ)
  have hr : (GainPartition.discrete : GainPartition G 0).roots.card = 0 := by
    have := (GainPartition.discrete : GainPartition G 0).roots_card_le
    omega
  simp only [Finset.univ_unique,Finset.sum_singleton,mul_one] at h
  change (if (GainPartition.discrete : GainPartition G 0).roots.card = k then 1 else 0) = _ at h
  rw [hr] at h
  simpa only [Nat.cast_id,eq_comm] using h.symm

@[simp] theorem whitneyCount_zero_column (n : ℕ) : whitneyCount G n 0 = 1 := by
  induction n with
  | zero => simp [whitneyCount_zero]
  | succ n ih => rw [whitneyCount_succ_zero,ih]

end Dowling
