import BoseBurton.SubspaceCountingFrames
import BoseBurton.GaussianFrames

noncomputable section
namespace BoseBurton
open Submodule Module Finset
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Fintype K] [Module.Finite K V] [Finite V]

omit [Module.Finite K V] in
theorem independentFrame_count (k : ℕ) (hk : k≤finrank K V) :
    Nat.card (IndependentFrame K V k)=∏ i : Fin k,(Fintype.card K^(finrank K V)-Fintype.card K^i.val) :=
  card_linearIndependent hk

theorem subspace_count_mul_frames (k : ℕ) :
    Nat.card (IndependentFrame K V k)=Nat.card (SubspacesOfDimension K V k)*
      (∏ i : Fin k,(Fintype.card K^k-Fintype.card K^i.val)) := by
  classical
  let : Fintype (SubspacesOfDimension K V k) := Fintype.ofFinite _
  rw [← Nat.card_congr (independentFrameSpanEquiv (K:=K) (V:=V) k),Nat.card_sigma]
  have he (U : SubspacesOfDimension K V k) : Nat.card (IndependentFrame K U.val k)=
      ∏ i : Fin k,(Fintype.card K^k-Fintype.card K^i.val) := by
    have h := independentFrame_count K U.val k (by rw [U.property])
    simpa only [U.property] using h
  simp only [he,sum_const,nsmul_eq_mul,card_univ,Nat.card_eq_fintype_card,Nat.cast_id]

theorem cast_frame_count_product (n k : ℕ) (hk : k≤n) :
    ((∏ i : Fin k,(Fintype.card K^n-Fintype.card K^i.val) : ℕ) : ℝ)=
      frameProduct (Fintype.card K : ℝ) n k := by
  rw [frameProduct,← Fin.prod_univ_eq_prod_range]
  push_cast
  apply prod_congr rfl
  intro i _
  have hle : Fintype.card K^i.val≤Fintype.card K^n :=
    Nat.pow_le_pow_right (Fintype.card_pos) (by omega)
  rw [Nat.cast_sub hle,Nat.cast_pow,Nat.cast_pow]

theorem frameProduct_self_pos (q : ℝ) (hq : 1<q) (k : ℕ) : 0<frameProduct q k k := by
  unfold frameProduct
  apply prod_pos
  intro i hi
  apply sub_pos.mpr
  exact pow_lt_pow_right₀ hq (mem_range.mp hi)

theorem subspace_count_gaussian (k : ℕ) (hk : k≤finrank K V) :
    (Nat.card {U : Submodule K V // finrank K U=k} : ℝ)=
      gaussian (Fintype.card K : ℝ) (finrank K V) k := by
  have hq : (1:ℝ)<Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α:=K)
  have h := congrArg (fun n : ℕ=>(n:ℝ)) (subspace_count_mul_frames K V k)
  rw [independentFrame_count K V k hk,Nat.cast_mul,cast_frame_count_product K _ _ hk,
    cast_frame_count_product K k k le_rfl] at h
  change _=(Nat.card {U : Submodule K V // finrank K U=k}:ℝ)*_ at h
  rw [← frameProduct_quotient (Fintype.card K : ℝ) hq (finrank K V) k hk]
  exact (eq_div_iff (frameProduct_self_pos _ hq k).ne').mpr h.symm

end BoseBurton
