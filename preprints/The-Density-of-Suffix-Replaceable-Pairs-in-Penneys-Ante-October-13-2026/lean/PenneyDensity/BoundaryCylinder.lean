import PenneyDensity.BoundaryMarginal
import PenneyDensity.MatchingCounting

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 def cylinderIndex (K L : ℕ) (h : L≤K) (p : Bool × Bool × Fin L) : Bool × Fin (2*K) :=
  (p.1,⟨if p.2.1 then 2*K-L+p.2.2.val else p.2.2.val,by split <;> omega⟩)

 theorem cylinderIndex_injective (K L : ℕ) (h : L≤K) :
    Function.Injective (cylinderIndex K L h) := by
  rintro ⟨b,s,i⟩ ⟨c,t,j⟩ he
  have hb := congrArg Prod.fst he
  have hv := congrArg (fun p : Bool × Fin (2*K) => p.2.val) he
  dsimp [cylinderIndex] at hv
  cases s <;> cases t <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hv
  · have hi : i=j := Fin.ext (by omega)
    simp only [Prod.mk.injEq]
    exact ⟨hb,True.intro,hi⟩
  · omega
  · omega
  · have hi : i=j := Fin.ext (by omega)
    simp only [Prod.mk.injEq]
    exact ⟨hb,True.intro,hi⟩

 def BoundaryCylinder {K : ℕ} (L : ℕ) (h : L≤K) (g : Bool × Fin (2*K) → Bool) : Prop :=
  ∀ p : Bool × Bool × Fin L,g (cylinderIndex K L h p)=p.2.1

 def suffixCoordinate (K k : ℕ) (hk : k≤K) (b : Bool) (j : Fin k) : Bool × Fin (2*K) :=
  (b,⟨2*K-k+j.val,by omega⟩)

 def prefixCoordinate (K k : ℕ) (hk : k≤K) (b : Bool) (j : Fin k) : Bool × Fin (2*K) :=
  (b,⟨j.val,by omega⟩)

 def boundaryMatching (K L k : ℕ) (hL : 0<L) (hLk : 2*L≤k) (hk : k≤K)
    (b c : Bool) : DirectedMatching (Bool × Fin (2*K)) (Fin k) where
  pivot j := if j.val<L then suffixCoordinate K k hk b j else prefixCoordinate K k hk c j
  parent j := if j.val<L then prefixCoordinate K k hk c j else suffixCoordinate K k hk b j
  pivot_injective := by
    intro i j he
    apply Fin.ext
    have hv := congrArg (fun p : Bool × Fin (2*K) => p.2.val) he
    dsimp [suffixCoordinate,prefixCoordinate] at hv
    split at hv <;> split at hv <;> dsimp at hv <;> omega
  parent_not_pivot := by
    intro i j he
    have hv := congrArg (fun p : Bool × Fin (2*K) => p.2.val) he
    dsimp [suffixCoordinate,prefixCoordinate] at hv
    split at hv <;> split at hv <;> dsimp at hv <;> omega

 theorem cylinder_not_pivot (K L k : ℕ) (hL : 0<L) (hLk : 2*L≤k) (hk : k≤K)
    (b c : Bool) (p : Bool × Bool × Fin L) (j : Fin k) :
    cylinderIndex K L (by omega) p≠(boundaryMatching K L k hL hLk hk b c).pivot j := by
  intro he
  have hv := congrArg (fun p : Bool × Fin (2*K) => p.2.val) he
  dsimp [cylinderIndex,boundaryMatching,suffixCoordinate,prefixCoordinate] at hv
  split at hv <;> split at hv <;> dsimp at hv <;> omega

 def cylinderFreeIndex (K L k : ℕ) (hL : 0<L) (hLk : 2*L≤k) (hk : k≤K)
    (b c : Bool) (p : Bool × Bool × Fin L) :
    (boundaryMatching K L k hL hLk hk b c).Free :=
  ⟨cylinderIndex K L (by omega) p,by
    rintro ⟨j,hj⟩
    exact cylinder_not_pivot K L k hL hLk hk b c p j hj.symm⟩

 theorem cylinderFreeIndex_injective (K L k : ℕ) (hL : 0<L) (hLk : 2*L≤k) (hk : k≤K)
    (b c : Bool) : Function.Injective (cylinderFreeIndex K L k hL hLk hk b c) := by
  intro p q he
  exact cylinderIndex_injective K L (by omega) (congrArg Subtype.val he)

 def BoundaryComparison {K k : ℕ} (hk : k≤K) (b c : Bool)
    (g : Bool × Fin (2*K) → Bool) : Prop :=
  ∀ j : Fin k,g (suffixCoordinate K k hk b j)=g (prefixCoordinate K k hk c j)

 theorem matching_iff_comparison (K L k : ℕ) (hL : 0<L) (hLk : 2*L≤k) (hk : k≤K)
    (b c : Bool) (g : Bool × Fin (2*K) → Bool) :
    (∀ j,g ((boundaryMatching K L k hL hLk hk b c).pivot j)=
      g ((boundaryMatching K L k hL hLk hk b c).parent j)) ↔ BoundaryComparison hk b c g := by
  constructor
  · intro hm j
    have hh := hm j
    dsimp [boundaryMatching] at hh
    split at hh
    · exact hh
    · exact hh.symm
  · intro hm j
    dsimp [boundaryMatching]
    split
    · exact hm j
    · exact (hm j).symm

 theorem card_cylinder (K L : ℕ) (h : L≤K) :
    Nat.card {g : Bool × Fin (2*K) → Bool // BoundaryCylinder L h g}=2^(4*K-4*L) := by
  have hc := card_prescribed_coordinates (cylinderIndex K L h)
    (cylinderIndex_injective K L h) (fun p => p.2.1)
  simp only [← Nat.card_eq_fintype_card] at hc
  simpa only [BoundaryCylinder,Nat.card_prod,show Nat.card Bool=2 by simp [Nat.card_eq_fintype_card],Nat.card_fin,
    show 2*(2*K)=4*K by omega,show 2*(2*L)=4*L by omega] using hc

 theorem card_cylinder_comparison (K L k : ℕ) (hL : 0<L) (hLk : 2*L≤k) (hk : k≤K)
    (b c : Bool) :
    Nat.card {g : Bool × Fin (2*K) → Bool //
      BoundaryComparison hk b c g ∧ BoundaryCylinder L (by omega) g}=2^(4*K-k-4*L) := by
  let M := boundaryMatching K L k hL hLk hk b c
  have hc := M.card_fixed_matching (cylinderFreeIndex K L k hL hLk hk b c)
    (cylinderFreeIndex_injective K L k hL hLk hk b c) (fun p => p.2.1)
  have he : ∀ g : Bool × Fin (2*K) → Bool,
      ((∀ j,g (M.pivot j)=g (M.parent j)) ∧
        ∀ p,g (cylinderFreeIndex K L k hL hLk hk b c p).val=p.2.1) ↔
      BoundaryComparison hk b c g ∧ BoundaryCylinder L (by omega) g := by
    intro g
    rw [matching_iff_comparison]
    rfl
  simp only [← Nat.card_eq_fintype_card] at hc
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)] at hc
  simpa only [Nat.card_prod,show Nat.card Bool=2 by simp [Nat.card_eq_fintype_card],Nat.card_fin,
    show 2*(2*K)=4*K by omega,show 2*(2*L)=4*L by omega] using hc

end PenneyDensity
