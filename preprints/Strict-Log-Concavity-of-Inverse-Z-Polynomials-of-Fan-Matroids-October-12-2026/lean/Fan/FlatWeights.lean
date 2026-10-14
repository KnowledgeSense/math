import Fan.ExtensionMobius
import Fan.PendantLowerInterval

namespace Fan
open Finset Polynomial
open scoped Classical

noncomputable def flatWeight {n : ℕ} (p : Configuration n) : Polynomial ℤ :=
  C (((-1 : ℤ)^(n-configurationRank p))*upperMu p) * X^(n-configurationRank p) * lowerQ p

theorem configurationRank_le {n : ℕ} (p : Configuration n) : configurationRank p ≤ n := by
  simpa only [configuration_top_rank] using (configurationRank_strictMono n).monotone (show p≤⊤ from le_top)

theorem inverseZ_sum_weights (n : ℕ) : inverseZ n=∑ p : Configuration n, flatWeight p := by
  rw [inverseZ_configuration]
  change MatroidInverseZ.inverseZ configurationRank (⊥ : Configuration n) ⊤=_
  have hi : (Icc (⊥ : Configuration n) ⊤ : Finset (Configuration n))=univ := by ext p; simp
  simp only [MatroidInverseZ.inverseZ,hi,configuration_top_rank,flatWeight,lowerQ,upperMu]

theorem flatWeight_append_empty {n : ℕ} (p : Configuration (n+1)) :
    flatWeight (appendConfiguration p false false (allowed_false_false p.val))=
      (if Fin.last n∈p.val.1 then X else 2*X)*flatWeight p := by
  have hr := configurationRank_le p
  have he : n+2-configurationRank p=(n+1-configurationRank p)+1 := by omega
  unfold flatWeight
  rw [appendConfiguration_rank,upperMu_append,lowerQ_append_empty]
  simp only [Bool.false_or,Bool.false_eq_true,ite_false,Nat.add_zero,he]
  by_cases hs : Fin.last n∈p.val.1
  · simp only [extensionMuWeight,Bool.false_or,Bool.false_eq_true,ite_false,hs,ite_true,
      pow_succ,map_mul,map_neg,map_one]
    ring
  · simp only [extensionMuWeight,Bool.false_or,Bool.false_eq_true,ite_false,hs,pow_succ,
      map_mul,map_neg,map_ofNat,map_one]
    ring

theorem flatWeight_append_pendant {n : ℕ} (p : Configuration (n+1))
    (hp : Fin.last n∉p.val.1) :
    flatWeight (appendConfiguration p false true ((allowed_false_true p.val).mpr hp))=flatWeight p := by
  unfold flatWeight
  rw [appendConfiguration_rank,upperMu_append,lowerQ_append_pendant p hp]
  simp only [Bool.false_or,ite_true,extensionMuWeight,one_mul]
  have he : n+2-(configurationRank p+1)=n+1-configurationRank p := by omega
  rw [he]

/-- Last-spoke-absent flats, with an explicit positive-rank index. -/
noncomputable def nonhubSum (n : ℕ) : Polynomial ℤ :=
  ∑ p : Configuration (n+1), if Fin.last n∈p.val.1 then 0 else flatWeight p

theorem nonhub_append {n : ℕ} (p : Configuration (n+1)) (b c : Bool)
    (ha : Allowed p.val b c) :
    (if Fin.last (n+1)∈(appendConfiguration p b c ha).val.1 then (0 : Polynomial ℤ)
      else flatWeight (appendConfiguration p b c ha))=
      if b then 0 else flatWeight (appendConfiguration p b c ha) := by
  change (if Fin.last (n+1)∈appendSet p.val.1 b then (0 : Polynomial ℤ) else _)=_
  simp only [mem_append_last]

theorem nonhubSum_recurrence (n : ℕ) :
    nonhubSum (n+1)=(1+X)*nonhubSum n+X*inverseZ (n+1) := by
  classical
  unfold nonhubSum
  rw [sum_extensions,inverseZ_sum_weights,mul_sum,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  simp only [nonhub_append]
  by_cases hp : Fin.last n∈p.val.1
  · simp [hp,flatWeight_append_empty]
  · simp [hp,flatWeight_append_empty,flatWeight_append_pendant p hp]
    ring

end Fan
