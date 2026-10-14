import CokernelPolynomiality.AntichainClosure
import CokernelPolynomiality.FamilyMatrix

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def orderedFamilySource {m : ℕ} (n a b : ℕ) (c d : Fin m → ℕ)
    (hac : ∀ j, a ≤ c j) (hbd : ∀ j, b ≤ d j) :
    intervalRep n a b ⟶ intervalFamily n m c d :=
  intervalFamilyLift (fun j => intervalHom n a b (c j) (d j) (hac j) (hbd j))

theorem orderedFamily_cokernel_mem_hull {m n a b : ℕ} {Y : Finset (ℕ × ℕ)}
    (hY : IsClosed Y) (hab : (a,b) ∈ Y) (c d : Fin m → ℕ)
    (hc : Monotone c) (hd : Antitone d) (hac : ∀ j, a ≤ c j)
    (hcb : ∀ j, c j ≤ b) (hbd : ∀ j, b ≤ d j) (hdn : ∀ j, d j ≤ n)
    (hmem : ∀ j, (c j,d j) ∈ Y) :
    IntervalHull n Y (cokernel (orderedFamilySource n a b c d hac hbd)) := by
  cases m with
  | zero =>
    have hf : orderedFamilySource n a b c d hac hbd=0 := by
      apply intervalFamily_hom_ext
      intro j
      exact Fin.elim0 j
    apply IntervalHull.iso ((cokernelIsoOfEq hf) ≪≫ cokernelZeroIsoTarget).symm
    apply intervalFamily_mem_hull
    intro j
    exact Fin.elim0 j
  | succ m =>
    exact antichain_cokernel_mem_hull hY hab c d hc hd hac hcb hbd hdn hmem

end CokernelPolynomiality
