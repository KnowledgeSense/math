import Dowling.KLProductOrientation

noncomputable section
namespace Dowling
open MatroidInverseZ Finset
open scoped Classical BigOperators
universe u

/-- Multiplicativity on a genuinely finite dependent product of ranked intervals. -/
theorem intervalP_pi_fin : ∀ (n : ℕ) (β : Fin n → Type u)
    [∀ i, PartialOrder (β i)] [∀ i, Fintype (β i)] [∀ i, LocallyFiniteOrder (β i)]
    [∀ i, DecidableEq (β i)] [∀ i, DecidableLE (β i)]
    (r : ∀ i, β i → ℕ) (_hr : ∀ i, Monotone (r i))
    (a b : ∀ i, β i), a ≤ b →
    intervalP (fun x => ∑ i, r i (x i)) a b = ∏ i, intervalP (r i) (a i) (b i) := by
  intro n
  induction n with
  | zero =>
    intro β _ _ _ _ _ r _ a b _
    have he : a=b := funext (fun i => Fin.elim0 i)
    subst b
    simp only [intervalP_diag,Fin.prod_univ_zero]
  | succ n ih =>
    intro β _ _ _ _ _ r hr a b hab
    let e := piFinSuccOrderIso β
    let rt : (∀ i : Fin n, β i.succ) → ℕ := fun x => ∑ i, r i.succ (x i)
    have hrt : Monotone rt := by
      intro x y hxy
      exact sum_le_sum (fun i _ => hr i.succ (hxy i))
    have he (x : β 0 × ∀ i : Fin n, β i.succ) :
        (∑ i, r i (e x i)) = r 0 x.1+rt x.2 := by
      rw [Fin.sum_univ_succ]
      rfl
    have ht := intervalP_transport e.toOrderEmbedding
      (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
      (fun x => r 0 x.1+rt x.2) (fun x => ∑ i, r i (x i))
      (fun x y => by
        change (∑ i, r i (e y i))-(∑ i, r i (e x i)) = _
        rw [he,he]) (e.symm a) (e.symm b)
    change intervalP (fun x => ∑ i, r i (x i)) (e (e.symm a)) (e (e.symm b)) = _ at ht
    rw [e.apply_symm_apply,e.apply_symm_apply] at ht
    rw [ht,intervalP_product (r 0) rt (hr 0) hrt _ _ (e.symm.monotone hab)]
    change intervalP (r 0) (a 0) (b 0) *
      intervalP rt (fun i => a i.succ) (fun i => b i.succ) = _
    rw [ih (fun i => β i.succ) (fun i => r i.succ) (fun i => hr i.succ)
      (fun i => a i.succ) (fun i => b i.succ) (fun i => hab i.succ),Fin.prod_univ_succ]

end Dowling
