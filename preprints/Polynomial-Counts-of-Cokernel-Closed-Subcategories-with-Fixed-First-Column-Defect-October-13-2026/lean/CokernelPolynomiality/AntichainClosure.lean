import CokernelPolynomiality.AntichainCokernel
import CokernelPolynomiality.FamilyHull
import CokernelPolynomiality.Definitions

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

theorem intervalRep_isZero_of_lt (n a b : ℕ) (hba : b < a) : IsZero (intervalRep n a b) := by
  apply isZero_of_vertices_zero
  intro i x
  apply Subtype.ext
  exact intervalSpace_val_zero (by unfold intervalActive; omega) x

theorem antichainOutput_mem_hull {m n a b : ℕ} {Y : Finset (ℕ × ℕ)}
    (hY : IsClosed Y) (hab : (a,b) ∈ Y) (c d : Fin (m+1) → ℕ)
    (hc : Monotone c) (hd : Antitone d) (hac : ∀ j, a ≤ c j)
    (hcb : ∀ j, c j ≤ b) (hbd : ∀ j, b ≤ d j) (hdn : ∀ j, d j ≤ n)
    (hmem : ∀ j, (c j,d j) ∈ Y) :
    IntervalHull n Y (intervalFamily n (m+1) (antichainOutputStart b c) d) := by
  apply intervalFamily_mem_hull
  intro j
  induction j using Fin.lastCases with
  | last =>
    simp only [antichainOutputStart_last]
    by_cases ht : b < d (Fin.last m)
    · apply IntervalHull.interval _ _ (by omega) (hdn _)
      have hh := hY a b (c (Fin.last m)) (d (Fin.last m))
        (c (Fin.last m)) (d (Fin.last m)) hab (hmem _) (hmem _)
        (hac _) (hcb _) (hbd _) (hac _) (hcb _) (hbd _)
      simpa only [min_self] using hh.2 (by simpa using ht)
    · apply IntervalHull.zero
      apply intervalRep_isZero_of_lt
      omega
  | cast j =>
    simp only [antichainOutputStart_castSucc]
    apply IntervalHull.interval _ _ ((hcb _).trans (hbd _)) (hdn _)
    have hj : j.castSucc ≤ j.succ := by change j.val ≤ j.val+1; omega
    have hh := (hY a b (c j.castSucc) (d j.castSucc) (c j.succ) (d j.succ)
      hab (hmem _) (hmem _) (hac _) (hcb _) (hbd _) (hac _) (hcb _) (hbd _)).1
    simpa only [max_eq_right (hc hj),max_eq_left (hd hj)] using hh

theorem antichain_cokernel_mem_hull {m n a b : ℕ} {Y : Finset (ℕ × ℕ)}
    (hY : IsClosed Y) (hab : (a,b) ∈ Y) (c d : Fin (m+1) → ℕ)
    (hc : Monotone c) (hd : Antitone d) (hac : ∀ j, a ≤ c j)
    (hcb : ∀ j, c j ≤ b) (hbd : ∀ j, b ≤ d j) (hdn : ∀ j, d j ≤ n)
    (hmem : ∀ j, (c j,d j) ∈ Y) :
    IntervalHull n Y (cokernel (antichainSourceHom n a b c d hac hbd)) :=
  .iso (antichainCokernelIso n a b c d hc hd hac hcb hbd).symm
    (antichainOutput_mem_hull hY hab c d hc hd hac hcb hbd hdn hmem)

end CokernelPolynomiality
