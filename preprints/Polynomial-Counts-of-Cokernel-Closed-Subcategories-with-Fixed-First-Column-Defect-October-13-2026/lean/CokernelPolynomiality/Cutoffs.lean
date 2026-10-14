import CokernelPolynomiality.Levels

namespace CokernelPolynomiality
noncomputable section

variable {m : ℕ}

 def firstHit (P : Fin m → Prop) : Fin (m+1) := by
  classical
  let H : ∃ k : ℕ, ∀ hk : k < m, P ⟨k,hk⟩ := ⟨m,fun h => False.elim ((lt_irrefl m) h)⟩
  exact ⟨Nat.find H,by
    have hb : Nat.find H ≤ m := Nat.find_min' H (fun h => False.elim ((lt_irrefl m) h))
    omega⟩

 theorem firstHit_spec (P : Fin m → Prop) (h : (firstHit P).val < m) :
    P ⟨(firstHit P).val,h⟩ := by
  classical
  exact Nat.find_spec (show ∃ k : ℕ, ∀ hk : k < m, P ⟨k,hk⟩ from
    ⟨m,fun h => False.elim ((lt_irrefl m) h)⟩) h

 theorem firstHit_le_of (P : Fin m → Prop) (t : Fin m) (ht : P t) :
    (firstHit P).val ≤ t.val := by
  classical
  exact Nat.find_min' _ (fun _ => ht)

 theorem firstHit_le_iff (P : Fin m → Prop)
    (hP : ∀ s t, s ≤ t → P s → P t) (t : Fin m) :
    (firstHit P).val ≤ t.val ↔ P t := by
  constructor
  · intro h
    have hb : (firstHit P).val < m := by have := t.isLt; omega
    exact hP ⟨_,hb⟩ t h (firstHit_spec P hb)
  · exact firstHit_le_of P t

 theorem firstHit_antitone (P Q : Fin m → Prop) (hPQ : ∀ t, P t → Q t) :
    firstHit Q ≤ firstHit P := by
  by_cases hp : (firstHit P).val < m
  · exact firstHit_le_of Q ⟨_,hp⟩ (hPQ _ (firstHit_spec P hp))
  · have hq := (firstHit Q).isLt
    have hp' := (firstHit P).isLt
    change (firstHit Q).val ≤ (firstHit P).val
    omega

 theorem cutoff_unique (a b : Fin (m+1))
    (h : ∀ t : Fin m, a.val ≤ t.val ↔ b.val ≤ t.val) : a = b := by
  apply Fin.ext
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · have ha : a.val < m := by have := b.isLt; omega
    have hh := (h ⟨a.val,ha⟩).mp le_rfl
    change b.val ≤ a.val at hh
    omega
  · have hb : b.val < m := by have := a.isLt; omega
    have hh := (h ⟨b.val,hb⟩).mpr le_rfl
    change a.val ≤ b.val at hh
    omega

end
end CokernelPolynomiality
