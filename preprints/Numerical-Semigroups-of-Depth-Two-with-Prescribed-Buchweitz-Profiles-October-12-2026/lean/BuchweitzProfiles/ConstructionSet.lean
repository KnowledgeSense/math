import BuchweitzProfiles.Construction
import BuchweitzProfiles.Counting

/-! Natural-number generators and their separation properties. -/
namespace BuchweitzProfiles

def constructionCutoff (N M : Nat) : Nat :=
  (2*N+2)*(((2*(2*N+2)+1)*M)+2*M)+1

def largeGenerator (N M d t j : Nat) : Nat :=
  ((constructionCutoff N M : ℤ)-1-digitRho (2*N+2) M d t j).toNat

theorem constructionCutoff_cast (N M : Nat) :
    (constructionCutoff N M : ℤ) =
      (2*(N:ℤ)+2)*(digitUnit (2*N+2) M+2*M)+1 := by
  unfold constructionCutoff digitUnit
  push_cast
  ring

theorem largeGenerator_integer_bounds (N M d t j : Nat)
    (hN : 2 ≤ N) (hM : 0 < M) (hd : 2 ≤ d) (hdN : d ≤ N+1)
    (ht : t ≤ 2*d-2) (hj0 : 0 < j) (hj : j < M) :
    0 < (constructionCutoff N M : ℤ)-1-digitRho (2*N+2) M d t j ∧
    (constructionCutoff N M : ℤ)-1-digitRho (2*N+2) M d t j ≤
      (constructionCutoff N M : ℤ)-2 ∧
    (constructionCutoff N M : ℤ) <
      2*((constructionCutoff N M : ℤ)-1-digitRho (2*N+2) M d t j) := by
  have hh := large_generator_bounds (N:ℤ) M d t j
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  dsimp at hh
  rw [constructionCutoff_cast]
  have hu : 0 < digitUnit (2*(N:ℤ)+2) M := by unfold digitUnit; positivity
  have hm : 0 ≤ ((N:ℤ)+2)*(digitUnit (2*N+2) M+2*M) := by positivity
  exact ⟨by linarith [hh.1], hh.2⟩

theorem largeGenerator_cast (N M d t j : Nat)
    (hN : 2 ≤ N) (hM : 0 < M) (hd : 2 ≤ d) (hdN : d ≤ N+1)
    (ht : t ≤ 2*d-2) (hj0 : 0 < j) (hj : j < M) :
    (largeGenerator N M d t j : ℤ) =
      (constructionCutoff N M : ℤ)-1-digitRho (2*N+2) M d t j := by
  unfold largeGenerator
  exact Int.toNat_of_nonneg (largeGenerator_integer_bounds N M d t j hN hM hd hdN ht hj0 hj).1.le

theorem largeGenerator_bounds (N M d t j : Nat)
    (hN : 2 ≤ N) (hM : 0 < M) (hd : 2 ≤ d) (hdN : d ≤ N+1)
    (ht : t ≤ 2*d-2) (hj0 : 0 < j) (hj : j < M) :
    0 < largeGenerator N M d t j ∧
      largeGenerator N M d t j ≤ constructionCutoff N M-2 ∧
      constructionCutoff N M < 2*largeGenerator N M d t j := by
  have hh := largeGenerator_integer_bounds N M d t j hN hM hd hdN ht hj0 hj
  rw [← largeGenerator_cast N M d t j hN hM hd hdN ht hj0 hj] at hh
  omega

theorem largeGenerator_mod (N M d t j : Nat)
    (hN : 2 ≤ N) (hM : 0 < M) (hd : 2 ≤ d) (hdN : d ≤ N+1)
    (ht : t ≤ 2*d-2) (hj0 : 0 < j) (hj : j < M) :
    largeGenerator N M d t j % M = M-j := by
  have hv := largeGenerator_cast N M d t j hN hM hd hdN ht hj0 hj
  have he : (largeGenerator N M d t j : ℤ) % (M:ℤ) = -(j:ℤ) % (M:ℤ) := by
    rw [hv, constructionCutoff_cast]
    simp [digitRho, digitUnit, Int.add_emod, Int.sub_emod, Int.mul_emod,
      Int.emod_eq_of_lt (show 0 ≤ (j:ℤ) by omega) (show (j:ℤ) < M by omega)]
  have hj' : (-(j:ℤ)) % (M:ℤ) = (M:ℤ)-j := by
    calc
      _ = ((M:ℤ)-j) % (M:ℤ) := by simp
      _ = _ := Int.emod_eq_of_lt (by omega) (by omega)
  rw [hj'] at he
  have he' : (largeGenerator N M d t j % M : ℤ) = ((M-j:Nat):ℤ) := by
    rw [Nat.cast_sub (by omega : j ≤ M)]
    exact he
  exact_mod_cast he'

theorem smallGenerators_bound (N M x : Nat) (hN : 2 ≤ N) (hM : 0 < M)
    (hx : x ∈ insert 0 (smallGenerators ((2*(2*N+2)+1)*M) M)) :
    x ≤ constructionCutoff N M-2 := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · omega
  have hh := (row_bounds hx).2
  have hu : 0 < ((2*(2*N+2)+1)*M)+2*M := by positivity
  unfold constructionCutoff
  simp only [Nat.one_mul] at hh
  have hK : 2 ≤ 2*N+2 := by omega
  have hm := Nat.mul_le_mul_right (((2*(2*N+2)+1)*M)+2*M) hK
  omega

theorem smallGenerators_mod (N M x : Nat)
    (hx : x ∈ insert 0 (smallGenerators ((2*(2*N+2)+1)*M) M)) :
    x % M = 0 := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · simp
  obtain ⟨b, _, rfl⟩ := mem_row.mp hx
  simp [Nat.add_mod]

theorem smallGenerators_card (N M : Nat) (hM : 0 < M) :
    (insert 0 (smallGenerators ((2*(2*N+2)+1)*M) M)).card = 4 := by
  have hu : 0 < (2*(2*N+2)+1)*M := by positivity
  have hz : 0 ∉ smallGenerators ((2*(2*N+2)+1)*M) M := by
    intro hx
    have hh := (row_bounds hx).1
    simp only [Nat.one_mul] at hh
    omega
  rw [Finset.card_insert_of_notMem hz]
  unfold smallGenerators
  rw [card_row _ _ _ hM]

theorem smallGenerators_positive (N M : Nat) (hM : 0 < M) :
    ∃ x ∈ insert 0 (smallGenerators ((2*(2*N+2)+1)*M) M), 0 < x := by
  refine ⟨(2*(2*N+2)+1)*M, Finset.mem_insert_of_mem ?_, by positivity⟩
  exact mem_row.mpr ⟨0, by omega, by simp⟩

end BuchweitzProfiles
