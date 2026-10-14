import SumsetRanges.ModelExponent
import SumsetRanges.RestrictedSetOperations

open Finset
namespace SumsetRanges

/-- The release's explicit bounded integer model for the restricted construction.
 It preserves every actual restricted sumset through order h. -/
theorem restricted_integer_model (h k n s : ℕ) (hh : 2≤h) (hk : 2≤k)
    (hnk : n≤k) (hs : s≤2*h) (A : Finset (ModelSpace n s)) (hcard : A.card=k)
    (hA : ∀ a∈A,latticeNorm a.1≤2*h-1 ∧ 0≤a.2.1 ∧ a.2.1≤(h*k:ℕ) ∧
      ∀ i,0≤a.2.2 i ∧ a.2.2 i≤1) :
    ∃ B : Finset ℤ, B.card=k ∧ (∀ b∈B,0≤b ∧ b≤(k^(restrictedExponent h):ℕ)) ∧
      ∀ q≤h,(restrictedSums B q).card=(restrictedSums A q).card := by
  classical
  let L := momentOrder h
  let φ := extendedMomentMap n L s
  let N := 2*h*k^L
  let M := restrictedScale h*k^L
  let shift : ModelCoordinate L s → ℤ := fun _ => N
  let A0 := A.image φ
  let A1 := A0.image (fun x => shift+x)
  have hL : 1≤L := momentOrder_pos h hh
  have hk1 : 1≤k := by omega
  have hkp : k≤k^L := by
    have hp := Nat.pow_le_pow_right hk1 hL
    simpa using hp
  have hp1 : 1≤k^L := Nat.one_le_pow _ _ hk1
  have hN : 1≤N := by dsimp [N]; nlinarith
  have hNM : 2*N≤M := by
    have hm := restrictedScale_ge h
    have he := Nat.mul_le_mul_right (k^L) hm
    dsimp [N,M]
    nlinarith
  have hnorm : ∀ a∈A,latticeNorm a.1≤2*h-1 := fun a ha => (hA a ha).1
  have hsize (q : ℕ) (hq : q≤h) : 2*q*(2*h-1)≤L+1 := by
    dsimp [L,momentOrder]
    have hz : 2*h-1≤2*h := Nat.sub_le _ _
    nlinarith
  have hinjq (q : ℕ) (hq : q≤h) : Set.InjOn φ (restrictedSums A q) :=
    extendedMomentMap_injOn_restrictedSums n L s (2*h-1) q A hnorm (hsize q hq)
  have hinjA : Set.InjOn φ A := by simpa using hinjq 1 (by omega)
  have hbound : ∀ a∈A,∀ i,(φ a i).natAbs≤N := by
    intro a ha i
    rcases i with j | (_ | j)
    · change ((momentMap n L a.1) j).natAbs≤N
      have hb := moment_coordinate_bound_by n L (2*h-1) k hnk a.1 (hnorm a ha) j
      have hN' : (2*h-1)*k^L≤N := by dsimp [N]; nlinarith [Nat.sub_le (2*h) 1]
      exact hb.trans hN'
    · change a.2.1.natAbs≤N
      have hn' : h*k≤N := by dsimp [N]; nlinarith
      have hi : (a.2.1.natAbs:ℤ)≤(N:ℤ) := by
        rw [Int.natAbs_of_nonneg (hA a ha).2.1]
        exact (hA a ha).2.2.1.trans (by exact_mod_cast hn')
      exact_mod_cast hi
    · change (a.2.2 j).natAbs≤N
      have hi : ((a.2.2 j).natAbs:ℤ)≤(N:ℤ) := by
        rw [Int.natAbs_of_nonneg ((hA a ha).2.2.2 j).1]
        exact ((hA a ha).2.2.2 j).2.trans (by exact_mod_cast hN)
      exact_mod_cast hi
  have hA1 : ∀ a∈A1,∀ i,0≤a i ∧ a i≤(M:ℤ) := by
    intro a ha i
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hn := hbound x hx i
    have hn' : ((φ x i).natAbs:ℤ)≤(N:ℤ) := by exact_mod_cast hn
    have hpos := Int.le_natAbs (a := φ x i)
    have hneg := Int.le_natAbs (a := -φ x i)
    simp only [Int.natAbs_neg] at hneg
    have hm' : (2:ℤ)*N≤M := by exact_mod_cast hNM
    change 0≤(N:ℤ)+φ x i ∧ (N:ℤ)+φ x i≤M
    omega
  have hD : 1≤Fintype.card (ModelCoordinate L s) := by simp [ModelCoordinate]; omega
  have hDupper : Fintype.card (ModelCoordinate L s)≤restrictedDimension h := by
    simp only [ModelCoordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_option]
    dsimp [L,restrictedDimension]
    omega
  obtain ⟨B,hBc,hB,hBs⟩ := finite_bounded_integer_model M h (h*M+1) A1 hD (by omega) (by omega) hA1
  refine ⟨B,?_,?_,?_⟩
  · rw [hBc]
    calc
      A1.card=A0.card := Finset.card_image_of_injective _ (fun x y he => add_left_cancel he)
      _ = A.card := Finset.card_image_of_injOn hinjA
      _ = k := hcard
  · intro b hb
    have hbound' := hB b hb
    refine ⟨hbound'.1,?_⟩
    apply hbound'.2.trans
    exact_mod_cast restricted_model_diameter_bound h k (Fintype.card (ModelCoordinate L s)) hk hDupper
  · intro q hq
    rw [hBs q hq]
    change (restrictedSums (A0.image (fun x => shift+x)) q).card=(restrictedSums A q).card
    rw [restrictedSums_translate,Finset.card_image_of_injective _ (fun x y he => add_left_cancel he)]
    exact card_restrictedSums_image A φ hinjA q (hinjq q hq)

end SumsetRanges
