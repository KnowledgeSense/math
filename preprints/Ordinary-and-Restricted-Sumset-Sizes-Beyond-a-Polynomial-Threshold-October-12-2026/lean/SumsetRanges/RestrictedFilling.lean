import SumsetRanges.RestrictedFillingParameters

open Finset
namespace SumsetRanges

/-- The release's restricted filling lemma, with its exact rational diameter bound cleared. -/
theorem restricted_filling (h s d : ℕ) (hh : 2≤h)
    (hs : 64*(2*h-1)*h≤s) (hd : s-1≤d)
    (hmax : (64*(2*h-1)*h)^h*d≤(2*h-1)*s^h) :
    ∃B : Finset ℤ, B.card=s ∧ B⊆Icc 0 (d:ℤ) ∧ (d:ℤ)∈B ∧
      (∀x : ℕ,x<s/2 → (x:ℤ)∈B) ∧
      restrictedSums B h=Icc (h.choose 2:ℤ) ((h:ℤ)*d-h.choose 2) := by
  let l := 2*h-1
  let n := s/(4*l)
  let D := (d-l+1)/l
  obtain ⟨hn,hDn,hDmax,hlD,hdlo,hdhi,hbudget⟩ := restricted_filling_parameters h s d hh hs hd hmax
  change 8*h≤n at hn
  change n-1≤D at hDn
  change (8*h)^h*D≤n^h at hDmax
  change l≤l*D at hlD
  change l*D+l-1≤d at hdlo
  change d≤l*D+2*l-2 at hdhi
  change l*n+2*l+s/2≤s at hbudget
  have hl : 1≤l := by dsimp [l]; omega
  have hhl : h≤l := by dsimp [l]; omega
  have hlz : (l:ℤ)=2*(h:ℤ)-1 := by dsimp [l]; omega
  have heta : 2*(h.choose 2:ℤ)=(h:ℤ)*((h:ℤ)-1) := by
    have he : (2:ℤ)*(h.choose 2:ℤ)=(h:ℤ)*((h-1:ℕ):ℤ) := by exact_mod_cast choose_two_double h
    simpa [Int.ofNat_sub (by omega : 1≤h)] using he
  have hwidth : (l:ℤ)≤(h:ℤ)*(l-1)-2*(h.choose 2:ℤ)+1 := by
    nlinarith
  obtain ⟨A0,hA0c,hA0b,_,hA0f⟩ := positional_filling h n D hh hn hDn hDmax
  let A1 := residueBlowup A0 l
  let d' := l*D+l-1
  have hd'z : (d':ℤ)=(l:ℤ)*D+l-1 := by
    dsimp [d']
    rw [Int.ofNat_sub (by omega : 1≤l*D+l)]
    push_cast
    rfl
  have hA1c : A1.card=l*n := by dsimp [A1]; rw [card_residueBlowup A0 l hl,hA0c]
  have hA1b : A1⊆Icc 0 (d':ℤ) := by
    intro x hx
    rw [hd'z]
    exact Finset.mem_Icc.mpr (residueBlowup_bounds A0 l D (fun a ha => Finset.mem_Icc.mp (hA0b ha)) hx)
  have hA1f : restrictedSums A1 h=Icc (h.choose 2:ℤ) ((h:ℤ)*d'-h.choose 2) := by
    rw [hd'z]
    exact residueBlowup_fills A0 l D h hl hhl hwidth
      (fun a ha => Finset.mem_Icc.mp (hA0b ha)) hA0f
  let a : ℤ := (d':ℤ)-l
  have ha : 0≤a := by
    have hz : (l:ℤ)≤(l:ℤ)*D := by exact_mod_cast hlD
    dsimp [a]
    rw [hd'z]
    omega
  have had' : a≤d' := by dsimp [a]; omega
  have hd'd : (d':ℤ)≤d := by exact_mod_cast hdlo
  have hlength : (h:ℤ)≤(d:ℤ)-a+1 := by dsimp [a]; omega
  have hgap : (h:ℤ)*a+h.choose 2≤(h:ℤ)*d'-h.choose 2+1 := by
    dsimp [a]
    nlinarith
  let A := A1∪Icc a (d:ℤ)
  have hAf : restrictedSums A h=Icc (h.choose 2:ℤ) ((h:ℤ)*d-h.choose 2) :=
    restricted_filling_terminal A1 h a d' d hA1b ha had' hd'd hlength hgap hA1f
  have hAb : A⊆Icc 0 (d:ℤ) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hhx := Finset.mem_Icc.mp (hA1b hx)
      exact Finset.mem_Icc.mpr ⟨hhx.1,by omega⟩
    · have hhx := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega,hhx.2⟩
  have hJc : (Icc a (d:ℤ)).card≤2*l := by
    rw [Int.card_Icc]
    apply Int.toNat_le.mpr
    have hz : (d:ℤ)≤(l:ℤ)*D+2*l-2 := by
      have hz' : (d:ℤ)≤((l*D+2*l-2:ℕ):ℤ) := by exact_mod_cast hdhi
      rw [Int.ofNat_sub (by omega : 2≤l*D+2*l)] at hz'
      push_cast at hz'
      exact hz'
    dsimp [a]
    rw [hd'z]
    omega
  have hAc : A.card+s/2≤s := by
    have hc := Finset.card_union_le A1 (Icc a (d:ℤ))
    change A.card≤A1.card+(Icc a (d:ℤ)).card at hc
    rw [hA1c] at hc
    omega
  obtain ⟨B,hBc,hAB,hBb,hBi⟩ := bounded_pad A d s (s/2) hAb (by omega) hAc
  refine ⟨B,hBc,hBb,?_,hBi,?_⟩
  · apply hAB
    exact Finset.mem_union_right A1 (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
  · exact restricted_filling_superset A B h d hAB hBb hAf

end SumsetRanges
