import PenneyDensity.BoundaryCylinder
import PenneyDensity.OverlapCounting

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 theorem boundary_overlap_iff_comparison {K k : ℕ} (hk0 : 0<k) (hk : k≤K)
    (b c : Bool) (g : Bool × Fin (2*K) → Bool) :
    properOverlap (boundaryWords g b) (boundaryWords g c) k ↔ BoundaryComparison hk b c g := by
  have hk2 : k<2*K := by omega
  simp only [properOverlap,boundaryWords,List.length_ofFn,hk0,hk2,true_and]
  have hl : ((List.ofFn (fun i : Fin (2*K) => g (b,i))).drop (2*K-k)).length=k := by
    simp only [List.length_drop,List.length_ofFn]
    omega
  have hr : ((List.ofFn (fun i : Fin (2*K) => g (c,i))).take k).length=k := by
    simp only [List.length_take,List.length_ofFn]
    omega
  constructor
  · intro he j
    have hh := congrArg (fun l : List Bool => l[j.val]?) he
    have hjl : j.val<((List.ofFn (fun i : Fin (2*K) => g (b,i))).drop (2*K-k)).length := by omega
    have hjr : j.val<((List.ofFn (fun i : Fin (2*K) => g (c,i))).take k).length := by omega
    simpa only [List.getElem?_eq_getElem hjl,List.getElem?_eq_getElem hjr,List.getElem_drop,
      List.getElem_take,List.getElem_ofFn,Option.some.injEq,suffixCoordinate,prefixCoordinate] using hh
  · intro he
    apply List.ext_getElem
    · omega
    · intro j hj hj'
      have hjk : j<k := by omega
      simpa only [List.getElem_drop,List.getElem_take,List.getElem_ofFn,
        suffixCoordinate,prefixCoordinate] using he ⟨j,hjk⟩

 theorem cylinder_forbids_short_overlap {K L k : ℕ} (hL : 0<L) (hLK : L≤K)
    (hk0 : 0<k) (hk : k≤K) (hkL : k<2*L) (b c : Bool)
    (g : Bool × Fin (2*K) → Bool) (hC : BoundaryCylinder L hLK g) :
    ¬properOverlap (boundaryWords g b) (boundaryWords g c) k := by
  intro ho
  have hc := (boundary_overlap_iff_comparison hk0 hk b c g).mp ho
  let j : Fin k := ⟨k-L,by omega⟩
  let r : Fin L := ⟨L+j.val-k,by dsimp [j]; omega⟩
  let t : Fin L := ⟨j.val,by dsimp [j]; omega⟩
  have hs := hC (b,true,r)
  have ht := hC (c,false,t)
  have hsidx : cylinderIndex K L hLK (b,true,r)=suffixCoordinate K k hk b j := by
    apply Prod.ext
    · rfl
    apply Fin.ext
    dsimp [cylinderIndex,suffixCoordinate,r,j]
    omega
  have htidx : cylinderIndex K L hLK (c,false,t)=prefixCoordinate K k hk c j := by
    apply Prod.ext
    · rfl
    apply Fin.ext
    rfl
  rw [hsidx] at hs
  rw [htidx] at ht
  have he := hc j
  rw [hs,ht] at he
  cases he

 theorem probability_cylinder (K L : ℕ) (h : L≤K) :
    probability (fun g : Bool × Fin (2*K) → Bool => BoundaryCylinder L h g)=(1/2 : ℝ)^(4*L) := by
  rw [probability,card_cylinder]
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_bool,Fintype.card_prod,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat]
  have he : 2*(2*K)=4*K := by omega
  rw [he]
  exact power_ratio (by omega)

 theorem probability_cylinder_overlap {K L k : ℕ} (hL : 0<L) (hLk : 2*L≤k) (hk : k≤K)
    (b c : Bool) :
    probability (fun g : Bool × Fin (2*K) → Bool =>
      properOverlap (boundaryWords g b) (boundaryWords g c) k ∧ BoundaryCylinder L (by omega) g)=
        (1/2 : ℝ)^(4*L)*(1/2 : ℝ)^k := by
  have he : ∀ g : Bool × Fin (2*K) → Bool,
      (properOverlap (boundaryWords g b) (boundaryWords g c) k ∧ BoundaryCylinder L (by omega) g) ↔
      (BoundaryComparison hk b c g ∧ BoundaryCylinder L (by omega) g) := by
    intro g
    rw [boundary_overlap_iff_comparison (by omega) hk b c g]
  have hp := probability_equal_of_equiv (Equiv.refl (Bool × Fin (2*K) → Bool))
    (fun g => properOverlap (boundaryWords g b) (boundaryWords g c) k ∧ BoundaryCylinder L (by omega) g)
    (fun g => BoundaryComparison hk b c g ∧ BoundaryCylinder L (by omega) g) he
  rw [hp,probability,card_cylinder_comparison K L k hL hLk hk b c]
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_bool,Fintype.card_prod,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat]
  have hmul : 2*(2*K)=4*K := by omega
  have hsub : 4*K-k-4*L=4*K-(4*L+k) := by omega
  rw [hmul,hsub,power_ratio (by omega),pow_add]

end PenneyDensity
