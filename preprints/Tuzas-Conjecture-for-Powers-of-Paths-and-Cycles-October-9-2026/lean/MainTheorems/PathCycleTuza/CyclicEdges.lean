import MainTheorems.PathCycleTuza.Basic

namespace ResearchMain.PathCycleTuza

def cyclicAdd (n : ℕ) (x : Fin n) (d : ℕ) (hd : d < n) : Fin n :=
  ⟨if x.val + d < n then x.val + d else x.val + d - n,
    by have hx := x.isLt; split_ifs <;> omega⟩

theorem cyclicAdd_injective (n d : ℕ) (hd : d < n) : Function.Injective (fun x => cyclicAdd n x d hd) := by
  intro x y h
  have he := congrArg Fin.val h
  have hx := x.isLt
  have hy := y.isLt
  apply Fin.ext
  dsimp [cyclicAdd] at he
  split_ifs at he <;> omega

theorem cyclicAdd_compose (n : ℕ) (x : Fin n) (u v : ℕ) (hw : u + v < n) :
    cyclicAdd n (cyclicAdd n x u (by omega)) v (by omega) = cyclicAdd n x (u + v) hw := by
  apply Fin.ext
  have hx := x.isLt
  dsimp [cyclicAdd]
  split_ifs <;> omega

def cyclicLength {n : ℕ} : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun x y => min (Nat.dist x.val y.val) (n - Nat.dist x.val y.val),
    by intro x y; dsimp; rw [Nat.dist_comm]⟩

def cyclicEdge (n d : ℕ) (hd : d < n) (x : Fin n) : Sym2 (Fin n) :=
  s(x, cyclicAdd n x d hd)

theorem cyclicEdge_length (n d : ℕ) (hd : d < n) (hs : 2 * d < n) (x : Fin n) :
    cyclicLength (cyclicEdge n d hd x) = d := by
  have hx := x.isLt
  simp only [cyclicEdge, cyclicLength, Sym2.lift_mk]
  dsimp [cyclicAdd]
  split_ifs <;> unfold Nat.dist <;> omega

theorem cyclicEdge_injective (n d : ℕ) (hd : d < n) (hp : 0 < d) (hs : 2 * d < n) :
    Function.Injective (cyclicEdge n d hd) := by
  intro x y h
  unfold cyclicEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact h₁
  · have he₁ := congrArg Fin.val h₁
    have he₂ := congrArg Fin.val h₂
    have hx := x.isLt
    have hy := y.isLt
    dsimp [cyclicAdd] at he₁ he₂
    split_ifs at he₁ he₂ <;> omega

theorem cyclicAdd_adj (n k d : ℕ) (x : Fin n) (hp : 0 < d) (hk : d ≤ k) (hn : 2 * k < n) :
    (cyclePower n k).Adj x (cyclicAdd n x d (by omega)) := by
  have hd : d < n := by omega
  have hs : 2 * d < n := by omega
  have he := cyclicEdge_length n d hd hs x
  change min (Nat.dist x.val (cyclicAdd n x d hd).val)
    (n - Nat.dist x.val (cyclicAdd n x d hd).val) = d at he
  refine ⟨?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    have hx := x.isLt
    dsimp [cyclicAdd] at hv
    split_ifs at hv <;> omega
  · apply min_le_iff.mp
    rw [he]
    exact hk

end ResearchMain.PathCycleTuza
