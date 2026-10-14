import PenneyDensity.ForestCounting

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 def blockIndex (N j m : ℕ) (hfit : j+m≤N) (r : Fin m) : Fin N :=
  ⟨j+r.val,by omega⟩

 theorem blockIndex_injective (N j m : ℕ) (hfit : j+m≤N) :
    Function.Injective (blockIndex N j m hfit) := by
  intro r s he
  apply Fin.ext
  have := congrArg Fin.val he
  dsimp [blockIndex] at this
  omega

 def blockForest (N i j m : ℕ) (hij : i<j) (hfit : j+m≤N) : EqualityForest N where
  active := Finset.univ.image (blockIndex N j m hfit)
  parent r := ⟨r.val-(j-i),Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.isLt⟩
  descending r hr := by
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hr
    dsimp [blockIndex]
    omega

 def EqualBlocks {N : ℕ} (f : Fin N → Bool) (i j m : ℕ)
    (hi : i+m≤N) (hj : j+m≤N) : Prop :=
  ∀ r : Fin m,f (blockIndex N i m hi r)=f (blockIndex N j m hj r)

 theorem blockForest_satisfies {N i j m : ℕ} (hij : i<j) (hj : j+m≤N)
    (f : Fin N → Bool) :
    (blockForest N i j m hij hj).Satisfies f ↔
      EqualBlocks f i j m (by omega) hj := by
  constructor
  · intro hf r
    have hh := hf (blockIndex N j m hj r) (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩)
    have hp : (blockForest N i j m hij hj).parent (blockIndex N j m hj r)=
        blockIndex N i m (by omega) r := by
      apply Fin.ext
      dsimp [blockForest,blockIndex]
      omega
    rw [hp] at hh
    exact hh.symm
  · intro hf r hr
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hr
    have hp : (blockForest N i j m hij hj).parent (blockIndex N j m hj t)=
        blockIndex N i m (by omega) t := by
      apply Fin.ext
      dsimp [blockForest,blockIndex]
      omega
    rw [hp]
    exact (hf t).symm

 theorem card_equal_blocks {N i j m : ℕ} (hij : i<j) (hj : j+m≤N) :
    Fintype.card {f : Fin N → Bool // EqualBlocks f i j m (by omega) hj}=2^(N-m) := by
  have hc := (blockForest N i j m hij hj).card_assignments
  have he := Fintype.card_congr (Equiv.subtypeEquivRight
    (fun f => blockForest_satisfies hij hj f))
  rw [← he,hc]
  congr 1
  simp only [blockForest,Finset.card_image_of_injective _ (blockIndex_injective N j m hj),
    Finset.card_univ,Fintype.card_fin]

/-- Coordinate/list bridge for a block of a literal finite binary word. -/
theorem equalBlocks_iff_lists {N i j m : ℕ} (hi : i+m≤N) (hj : j+m≤N)
    (f : Fin N → Bool) : EqualBlocks f i j m hi hj ↔
      ((List.ofFn f).drop i).take m=((List.ofFn f).drop j).take m := by
  have hli : (((List.ofFn f).drop i).take m).length=m := by
    simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  have hlj : (((List.ofFn f).drop j).take m).length=m := by
    simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  constructor
  · intro he
    apply List.ext_getElem
    · omega
    · intro r hr hs
      have hrm : r<m := by omega
      simpa only [List.getElem_take,List.getElem_drop,List.getElem_ofFn,blockIndex]
        using he ⟨r,hrm⟩
  · intro he r
    have hr : r.val<(((List.ofFn f).drop i).take m).length := by omega
    have hs : r.val<(((List.ofFn f).drop j).take m).length := by omega
    have hh := congrArg (fun l : List Bool => l[r.val]?) he
    simpa only [List.getElem?_eq_getElem hr,List.getElem?_eq_getElem hs,
      List.getElem_take,List.getElem_drop,List.getElem_ofFn,Option.some.injEq,blockIndex] using hh

end PenneyDensity
