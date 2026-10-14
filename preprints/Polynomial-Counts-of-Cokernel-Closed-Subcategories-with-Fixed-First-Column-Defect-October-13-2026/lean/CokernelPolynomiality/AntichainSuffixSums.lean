import CokernelPolynomiality.PairCokernelLinear

noncomputable section
namespace CokernelPolynomiality

def finSuffixSum {m : ℕ} (z : Fin (m+1) → ℂ) (j : Fin (m+1)) : ℂ :=
  ∑ k : Fin (m+1), if j ≤ k then z k else 0

theorem finSuffixSum_last {m : ℕ} (z : Fin (m+1) → ℂ) :
    finSuffixSum z (Fin.last m)=z (Fin.last m) := by
  unfold finSuffixSum
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro k _ hk
    rw [ite_eq_right]
    intro h
    apply hk
    exact le_antisymm (Fin.le_last k) h
  · simp

theorem finSuffixSum_castSucc {m : ℕ} (z : Fin (m+1) → ℂ) (j : Fin m) :
    finSuffixSum z j.castSucc=z j.castSucc+finSuffixSum z j.succ := by
  have he (k : Fin (m+1)) :
      (if j.castSucc ≤ k then z k else 0)=
        (if k=j.castSucc then z k else 0)+(if j.succ ≤ k then z k else 0) := by
    by_cases hk : k=j.castSucc
    · subst k
      simp [show ¬j.succ ≤ j.castSucc by simp]
    · by_cases hjk : j.castSucc ≤ k
      · have hsk : j.succ ≤ k := by
          have hne : k.val ≠ j.val := by intro h; apply hk; exact Fin.ext h
          change j.val+1 ≤ k.val
          change j.val ≤ k.val at hjk
          omega
        simp [hk,hjk,hsk]
      · have hsk : ¬j.succ ≤ k := by
          intro h
          apply hjk
          exact le_trans (by change j.val ≤ j.val+1; omega) h
        simp [hk,hjk,hsk]
  simp only [finSuffixSum,he,Finset.sum_add_distrib]
  simp

def antichainOutputStart {m : ℕ} (b : ℕ) (c : Fin (m+1) → ℕ) : Fin (m+1) → ℕ :=
  Fin.lastCases (b+1) (fun j => c j.succ)

@[simp] theorem antichainOutputStart_castSucc {m : ℕ} (b : ℕ) (c : Fin (m+1) → ℕ) (j : Fin m) :
    antichainOutputStart b c j.castSucc=c j.succ := by simp [antichainOutputStart]

@[simp] theorem antichainOutputStart_last {m : ℕ} (b : ℕ) (c : Fin (m+1) → ℕ) :
    antichainOutputStart b c (Fin.last m)=b+1 := by simp [antichainOutputStart]

theorem antichainOutputStart_ge {m : ℕ} (b : ℕ) (c : Fin (m+1) → ℕ)
    (hc : Monotone c) (hcb : ∀ j, c j ≤ b) (j k : Fin (m+1)) (hjk : j ≤ k) :
    c j ≤ antichainOutputStart b c k := by
  induction k using Fin.lastCases with
  | last => simpa using le_trans (hcb j) (Nat.le_succ b)
  | cast k =>
    rw [antichainOutputStart_castSucc]
    apply hc
    exact le_trans hjk (by change k.val ≤ k.val+1; omega)

end CokernelPolynomiality
