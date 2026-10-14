import ASR312.Boundary

namespace ASR312

 theorem startsPositive_cons_not_minus {a : Entry} {l : List Entry}
    (h : StartsPositive (a :: l)) : a ≠ .minus := by
  intro he
  subst a
  simp [StartsPositive,nonzeroEntries] at h

 theorem firstColumn_not_minus {r k : ℕ} (A : Rectangle r (k+1)) (h : IsASR A) (i : Fin r) :
    A i 0 ≠ .minus := by
  have hh := (h.1 i).2.1
  rw [row,List.ofFn_succ] at hh
  exact startsPositive_cons_not_minus hh

 theorem chain_plus_only (l : List Entry) (h : l.IsChain (· ≠ ·))
    (hp : ∀ x ∈ l, x = .plus) : l = [] ∨ l = [.plus] := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a l =>
    have ha := hp a (by simp)
    subst a
    cases l with
    | nil => exact Or.inr rfl
    | cons b l =>
      have hb := hp b (by simp)
      subst b
      have hh := (List.isChain_cons_cons.mp h).1
      exact False.elim (hh rfl)

 theorem alternating_without_minus (l : List Entry) (ha : Alternates l)
    (hm : ∀ x ∈ l, x ≠ .minus) :
    nonzeroEntries l = [] ∨ nonzeroEntries l = [.plus] := by
  apply chain_plus_only _ ha
  intro x hx
  obtain ⟨hx,hz⟩ := List.mem_filter.mp hx
  have hh := hm x hx
  cases x <;> simp_all

 theorem firstColumn_entries {r k : ℕ} (A : Rectangle r (k+1)) (h : IsASR A) :
    nonzeroEntries (col A 0) = [] ∨ nonzeroEntries (col A 0) = [.plus] := by
  apply alternating_without_minus _ (h.2 0).1
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact firstColumn_not_minus A h i

 theorem extendable_implies_avoids {r k : ℕ} {A : Rectangle r k}
    (h : ExtendablyAvoids312 A) : Avoids312 A := by
  obtain ⟨n,hr,hk,B,_,hb,he⟩ := h
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  apply hb
  refine ⟨Fin.castLE hr i₁,Fin.castLE hr i₂,Fin.castLE hr i₃,
    Fin.castLE hk j₁,Fin.castLE hk j₂,Fin.castLE hk j₃,h12,h23,hj12,hj23,?_,?_,?_⟩
  · rw [he]; exact h13
  · rw [he]; exact h21
  · rw [he]; exact h32

 theorem asm_extendable_iff {n : ℕ} (A : Rectangle n n) (h : IsASM A) :
    ExtendablyAvoids312 A ↔ Avoids312 A := by
  constructor
  · exact extendable_implies_avoids
  · intro ha
    exact ⟨n,le_rfl,le_rfl,A,h,ha,fun _ _ => rfl⟩

end ASR312
