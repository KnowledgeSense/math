import Fan.ExtensionSums
import Fan.MobiusColumn

namespace Fan
open Finset
open scoped Classical

noncomputable def extensionMuWeight {n : ℕ} (p : Pair (n+1)) (b c : Bool) : ℤ :=
  if b||c then 1 else if Fin.last n∈p.1 then -1 else -2

noncomputable def extensionMuCandidate (n : ℕ) (z : Configuration (n+2)) : ℤ :=
  let x := (extensionEquiv n).symm z
  extensionMuWeight x.1.val x.2.val.1 x.2.val.2 * upperMu x.1

theorem extensionMuCandidate_append {n : ℕ} (p : Configuration (n+1)) (b c : Bool)
    (ha : Allowed p.val b c) :
    extensionMuCandidate n (appendConfiguration p b c ha)=extensionMuWeight p.val b c*upperMu p := by
  change extensionMuCandidate n (extensionEquiv n ⟨p,⟨(b,c),ha⟩⟩)=_
  unfold extensionMuCandidate
  rw [Equiv.symm_apply_apply]

theorem appendConfiguration_le_iff {n : ℕ} (p q : Configuration (n+1))
    (b c d e : Bool) (ha : Allowed p.val b c) (hb : Allowed q.val d e) :
    appendConfiguration p b c ha ≤ appendConfiguration q d e hb ↔ p≤q ∧ b≤d ∧ c≤e :=
  appendPair_le_iff _ _ _ _ _ _

theorem extension_weight_sum {n : ℕ} (p q : Configuration (n+1)) (b c : Bool)
    (ha : Allowed p.val b c) (v : ℤ) :
    (if p≤q ∧ b≤false ∧ c≤false then extensionMuWeight q.val false false*v else 0) +
      (if Fin.last n∈q.val.1 then
        (if p≤q ∧ b≤true ∧ c≤true then extensionMuWeight q.val true true*v else 0)
      else
        (if p≤q ∧ b≤true ∧ c≤false then extensionMuWeight q.val true false*v else 0)+
        (if p≤q ∧ b≤false ∧ c≤true then extensionMuWeight q.val false true*v else 0)) =
      if b||c then (if p≤q then v else 0) else 0 := by
  classical
  by_cases hpq : p≤q
  · by_cases hq : Fin.last n∈q.val.1
    · cases b <;> cases c <;> simp [extensionMuWeight,hpq,hq,Bool.le_iff_imp]
    · have hboth : ¬(b=true ∧ c=true) := by
        rintro ⟨rfl,rfl⟩
        exact hq (hpq.1 ((allowed_true_true p.val).mp ha))
      cases b <;> cases c <;> simp_all [extensionMuWeight,Bool.le_iff_imp]
      ring
  · cases b <;> cases c <;> simp [hpq,Bool.le_iff_imp]

theorem extensionMuCandidate_sum (n : ℕ) (z : Configuration (n+2)) :
    (∑ w ∈ Icc z ⊤, extensionMuCandidate n w)=if z=⊤ then 1 else 0 := by
  classical
  obtain ⟨⟨p,⟨⟨b,c⟩,ha⟩⟩,rfl⟩ := (extensionEquiv n).surjective z
  change (∑ w ∈ Icc (appendConfiguration p b c ha) ⊤, extensionMuCandidate n w)=
    if appendConfiguration p b c ha=⊤ then 1 else 0
  have hi : Icc (appendConfiguration p b c ha) ⊤=
      univ.filter (appendConfiguration p b c ha≤·) := by ext w; simp
  rw [hi,sum_filter,sum_extensions]
  have hsum : (∑ q : Configuration (n+1), (
      (if appendConfiguration p b c ha≤appendConfiguration q false false (allowed_false_false q.val)
        then extensionMuCandidate n (appendConfiguration q false false (allowed_false_false q.val)) else 0)+
      (if h : Fin.last n∈q.val.1 then
        (if appendConfiguration p b c ha≤appendConfiguration q true true ((allowed_true_true q.val).mpr h)
          then extensionMuCandidate n (appendConfiguration q true true ((allowed_true_true q.val).mpr h)) else 0)
      else
        (if appendConfiguration p b c ha≤appendConfiguration q true false ((allowed_true_false q.val).mpr h)
          then extensionMuCandidate n (appendConfiguration q true false ((allowed_true_false q.val).mpr h)) else 0)+
        (if appendConfiguration p b c ha≤appendConfiguration q false true ((allowed_false_true q.val).mpr h)
          then extensionMuCandidate n (appendConfiguration q false true ((allowed_false_true q.val).mpr h)) else 0)))) =
      ∑ q : Configuration (n+1), if b||c then (if p≤q then upperMu q else 0) else 0 := by
    apply sum_congr rfl
    intro q _
    simp only [appendConfiguration_le_iff,extensionMuCandidate_append]
    simpa only [dite_eq_ite] using extension_weight_sum p q b c ha (upperMu q)
  rw [hsum]
  simp only [sum_ite_irrel,sum_const_zero,upperMu_sum,appendConfiguration_eq_top_iff]
  by_cases hp : p=⊤
  · subst p
    have ht := top_spoke (Fin.last n)
    cases b <;> cases c
    · simp
    · exact False.elim (((allowed_false_true _).mp ha) ht)
    · exact False.elim (((allowed_true_false _).mp ha) ht)
    · simp
  · cases b <;> cases c <;> simp [hp]

/-- The upper Möbius factor is evaluated from the actual last-vertex flat
classification. No contraction-polynomial formula is assumed. -/
theorem upperMu_append {n : ℕ} (p : Configuration (n+1)) (b c : Bool)
    (ha : Allowed p.val b c) :
    upperMu (appendConfiguration p b c ha)=extensionMuWeight p.val b c*upperMu p := by
  have h := mu_column_unique (extensionMuCandidate n) (extensionMuCandidate_sum n)
    (appendConfiguration p b c ha)
  rw [extensionMuCandidate_append] at h
  exact h.symm

end Fan
