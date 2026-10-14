import FourGeneratedSemigroups.SpuriousTranslation

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

def slicePoint (x y z : ℕ) : Factorization :=
  Finsupp.single 1 x+Finsupp.single 2 y+Finsupp.single 3 z
@[simp] lemma slicePoint_zero (x y z : ℕ) : slicePoint x y z 0=0 := by simp [slicePoint]
@[simp] lemma slicePoint_first (x y z : ℕ) : slicePoint x y z 1=x := by simp [slicePoint]
@[simp] lemma slicePoint_second (x y z : ℕ) : slicePoint x y z 2=y := by simp [slicePoint]
@[simp] lemma slicePoint_third (x y z : ℕ) : slicePoint x y z 3=z := by simp [slicePoint]

/-- A gap between consecutive top-slice corners determines a boundary generator
with prescribed first and second exponents. -/
theorem topSlice_gap_generator (u v : Factorization)
    (hu : u∈staircaseCorners G) (hv : v∈staircaseCorners G)
    (hz : u 3=v 3) (htop : v 3+1=criticalExponent G.generators G.positive 3)
    (hx : u 1<v 1)
    (hprev : ∀ w∈staircaseCorners G,w 3=v 3 → w 1<v 1 → w 1≤u 1) :
    ∃ h∈staircaseBoundary G,h 0=0 ∧ h 1=u 1+1 ∧ h 2=v 2+1 ∧ h 3≤v 3 := by
  let g := slicePoint (u 1+1) (v 2+1) (v 3)
  have hy := corner_second_reverse G u v hu hv hz hx
  have hg : g∉staircase G := by
    intro hgT
    obtain ⟨w,hw,hgw⟩ := exists_corner_above G g hgT
    have hgw1 := hgw 1
    have hgw2 := hgw 2
    have hgw3 := hgw 3
    simp only [g,slicePoint_first,slicePoint_second,slicePoint_third] at hgw1 hgw2 hgw3
    have hw3 : w 3=v 3 := by have := hw.1.2.1; omega
    have hw1 : w 1<v 1 := by
      by_contra hn
      have hvw : v≤w := by
        intro i; fin_cases i <;> simp_all [hv.1.1,hw.1.1] ; omega
      have he := corner_maximal G v hv w hw.1 hvw
      have := congrArg (fun c : Factorization => c 2) he
      omega
    have hh := hprev w hw hw3 hw1
    omega
  obtain ⟨h,hh,hgdiv⟩ := exists_boundary_le G g hg
  have hd0 := hgdiv 0
  have hd1 := hgdiv 1
  have hd2 := hgdiv 2
  have hd3 := hgdiv 3
  simp only [g,slicePoint_zero,slicePoint_first,slicePoint_second,slicePoint_third] at hd0 hd1 hd2 hd3
  have h1 : h 1=u 1+1 := by
    by_contra hn
    have hhu : h≤u := by
      intro i; fin_cases i <;> simp_all [hu.1.1] <;> omega
    exact hh.1 (staircase_lower G hu.1 hhu)
  have h2 : h 2=v 2+1 := by
    by_contra hn
    have hhv : h≤v := by
      intro i; fin_cases i <;> simp_all [hv.1.1] ; omega
    exact hh.1 (staircase_lower G hv.1 hhv)
  exact ⟨h,hh,by omega,h1,h2,hd3⟩

/-- For a spurious corner, its preceding gap generator has full support. -/
theorem spurious_gap_fullSupport (p : Factorization) (hp0 : p 0=0) (hp3 : p 3=0)
    (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (u v : Factorization) (hu : u∈staircaseCorners G) (hv : v∈spuriousCorners G)
    (hz : u 3=v 3) (hx : u 1<v 1)
    (hprev : ∀ w∈staircaseCorners G,w 3=v 3 → w 1<v 1 → w 1≤u 1) :
    ∃ h,FullSupportBoundary G h ∧ h 2=v 2+1 := by
  obtain ⟨h,hh,hh0,hh1,hh2,hh3⟩ := topSlice_gap_generator G u v hu hv.1 hz
    (spuriousCorner_top G v hv) hx hprev
  have hshift := spurious_translation_mem G p hp0 hp3 hp v hv
  have h3 : 0<h 3 := by
    by_contra hn
    have hle : h≤v.erase 3+p := by
      intro i; fin_cases i <;> simp_all [hv.1.1.1] <;> omega
    exact hh.1 (staircase_lower G hshift hle)
  refine ⟨h,⟨hh,hh0,?_⟩,hh2⟩
  intro i hi
  fin_cases i <;> simp_all

end FourGeneratedSemigroups
