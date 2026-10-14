import Fan.ConfigurationCast

namespace Fan
open Finset
open scoped Classical

noncomputable def nonhubVertices {n : ℕ} (p : Configuration n) : Finset (Fin n) := univ \ p.val.1
noncomputable def trailingCut {n : ℕ} (p : Configuration n) : ℕ :=
  (nonhubVertices p).sup (fun i => i.val+1)

@[simp] theorem mem_nonhubVertices {n : ℕ} (p : Configuration n) (i : Fin n) :
    i∈nonhubVertices p ↔ i∉p.val.1 := by simp [nonhubVertices]

theorem trailingCut_le {n : ℕ} (p : Configuration n) : trailingCut p ≤ n := by
  apply Finset.sup_le
  intro i _
  have := i.isLt
  omega

theorem nonhub_le_trailingCut {n : ℕ} (p : Configuration n) {i : Fin n} (hi : i∉p.val.1) :
    i.val+1 ≤ trailingCut p := Finset.le_sup (f:=fun j : Fin n => j.val+1) ((mem_nonhubVertices p i).mpr hi)

theorem spoke_of_trailingCut_le {n : ℕ} (p : Configuration n) {i : Fin n}
    (hi : trailingCut p ≤ i.val) : i∈p.val.1 := by
  by_contra hn
  have := nonhub_le_trailingCut p hn
  omega

theorem trailingCut_endpoint {n : ℕ} (p : Configuration n) (i : Fin n)
    (hi : i.val+1=trailingCut p) : i∉p.val.1 := by
  have hne : (nonhubVertices p).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : trailingCut p=0 := by simp [trailingCut,he]
    omega
  obtain ⟨j,hj,hje⟩ := Finset.sup_mem_of_nonempty (f:=fun j : Fin n => j.val+1) hne
  have he : i=j := Fin.ext (by change j.val+1=trailingCut p at hje; omega)
  subst j
  exact (mem_nonhubVertices p i).mp hj

theorem EndsNonhub.trailingCut_eq {n : ℕ} {p : Configuration n} (hp : EndsNonhub p) :
    trailingCut p=n := by
  apply Nat.le_antisymm (trailingCut_le p)
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact nonhub_le_trailingCut p (hp (Fin.last n) rfl)

@[simp] theorem trailingCut_cast {m n : ℕ} (h : m=n) (p : Configuration m) :
    trailingCut (configurationCast h p)=trailingCut p := by subst n; rfl

theorem configuration_eq_top_of_spokes {n : ℕ} (p : Configuration n)
    (hp : ∀ i : Fin n, i∈p.val.1) : p=⊤ := by
  apply top_unique
  constructor
  · intro i _
    exact hp i
  · intro j hj
    have hjpos := (⊤ : Configuration n).property.1 j hj
    let i : Fin n := ⟨j.val-1,by have := j.isLt; omega⟩
    have hij : i.val+1=j.val := by dsimp [i]; omega
    exact (p.property.2 i j hij).2 (hp i) (hp j)

end Fan
