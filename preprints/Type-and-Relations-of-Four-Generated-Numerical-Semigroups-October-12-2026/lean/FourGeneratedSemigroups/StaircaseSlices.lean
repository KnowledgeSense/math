import FourGeneratedSemigroups.PlaneStaircase
import FourGeneratedSemigroups.TopSliceGap

noncomputable section
namespace FourGeneratedSemigroups
open PlaneStaircase
variable {S : NumericalSemigroup} (G : FourGenerated S)

def planeSlice (z : ℕ) : Set Point := {p | slicePoint p.1 p.2 z ∈ staircase G}

lemma slicePoint_le_iff (p q : Point) (z w : ℕ) :
    slicePoint p.1 p.2 z ≤ slicePoint q.1 q.2 w ↔ p ≤ q ∧ z ≤ w := by
  constructor
  · intro h
    exact ⟨⟨by simpa using h 1,by simpa using h 2⟩,by simpa using h 3⟩
  · rintro ⟨hp,hz⟩ i
    fin_cases i <;> simp_all
    · exact hp.1
    · exact hp.2

lemma slicePoint_injective (z : ℕ) : Function.Injective (fun p : Point => slicePoint p.1 p.2 z) := by
  intro p q h
  apply Prod.ext
  · simpa using congrArg (fun a : Factorization => a 1) h
  · simpa using congrArg (fun a : Factorization => a 2) h

lemma slicePoint_reconstruct (a : Factorization) (ha : a 0=0) :
    slicePoint (a 1) (a 2) (a 3)=a := by
  ext i
  fin_cases i <;> simp_all

lemma planeSlice_finite (z : ℕ) : (planeSlice G z).Finite :=
  (finite_staircase G).preimage (slicePoint_injective z).injOn

lemma planeSlice_lower (z : ℕ) : IsLowerSet (planeSlice G z) := by
  intro q p hpq hq
  exact staircase_lower G hq ((slicePoint_le_iff p q z z).mpr ⟨hpq,le_rfl⟩)

lemma planeSlice_antitone : Antitone (planeSlice G) := by
  intro z w hzw p hp
  exact staircase_lower G hp ((slicePoint_le_iff p p z w).mpr ⟨le_rfl,hzw⟩)

lemma planeSlice_top_empty : planeSlice G (criticalExponent G.generators G.positive 3)=∅ := by
  ext p
  simp only [Set.mem_empty_iff_false,iff_false]
  intro h
  have := h.2.1
  simp at this

lemma planeSlice_zero_mem {z : ℕ} (hz : z<criticalExponent G.generators G.positive 3) :
    (0,0) ∈ planeSlice G z := by
  change slicePoint 0 0 z ∈ staircase G
  refine ⟨by simp,by simpa,?_⟩
  simpa [slicePoint] using below_critical_pure_degree_apery G 3 (by decide) z hz

lemma slicePoint_corner_iff (p : Point) (z : ℕ) :
    slicePoint p.1 p.2 z ∈ staircaseCorners G ↔
      p ∈ LostCorners (planeSlice G z) (planeSlice G (z+1)) := by
  constructor
  · intro h
    refine ⟨⟨h.1,?_⟩,?_⟩
    · intro q hq hpq
      have he := corner_maximal G _ h _ hq ((slicePoint_le_iff p q z z).mpr ⟨hpq,le_rfl⟩)
      exact (slicePoint_injective z he).symm
    · intro hp
      apply h.2 3 (by decide)
      have he : slicePoint p.1 p.2 z+Finsupp.single 3 1=slicePoint p.1 p.2 (z+1) := by
        ext i
        fin_cases i <;> simp
      simpa only [planeSlice,Set.mem_ofPred_eq,he] using hp
  · rintro ⟨hp,hpnext⟩
    refine ⟨hp.1,?_⟩
    intro i hi hs
    fin_cases i
    · contradiction
    · have he : slicePoint p.1 p.2 z+Finsupp.single 1 1=slicePoint (p.1+1) p.2 z := by
        ext j; fin_cases j <;> simp
      change slicePoint p.1 p.2 z+Finsupp.single 1 1 ∈ staircase G at hs
      rw [he] at hs
      have hh := hp.2 (p.1+1,p.2) hs ⟨by omega,le_rfl⟩
      have := congrArg Prod.fst hh
      omega
    · have he : slicePoint p.1 p.2 z+Finsupp.single 2 1=slicePoint p.1 (p.2+1) z := by
        ext j; fin_cases j <;> simp
      change slicePoint p.1 p.2 z+Finsupp.single 2 1 ∈ staircase G at hs
      rw [he] at hs
      have hh := hp.2 (p.1,p.2+1) hs ⟨le_rfl,by omega⟩
      have := congrArg Prod.snd hh
      omega
    · apply hpnext
      have he : slicePoint p.1 p.2 z+Finsupp.single 3 1=slicePoint p.1 p.2 (z+1) := by
        ext j; fin_cases j <;> simp
      change slicePoint p.1 p.2 z+Finsupp.single 3 1 ∈ staircase G at hs
      simpa only [planeSlice,Set.mem_ofPred_eq,he] using hs

lemma slicePoint_boundary_iff (p : Point) (z : ℕ) :
    slicePoint p.1 p.2 z ∈ staircaseBoundary G ↔
      p ∈ Boundary (planeSlice G z) ∧ (z=0 ∨ p ∈ planeSlice G (z-1)) := by
  constructor
  · intro h
    refine ⟨⟨h.1,?_⟩,?_⟩
    · intro q hqp
      apply h.2
      apply lt_of_le_of_ne ((slicePoint_le_iff q p z z).mpr ⟨hqp.le,le_rfl⟩)
      intro he
      exact hqp.ne (slicePoint_injective z he)
    · by_cases hz : z=0
      · exact Or.inl hz
      · right
        apply h.2
        apply lt_of_le_of_ne ((slicePoint_le_iff p p (z-1) z).mpr ⟨le_rfl,by omega⟩)
        intro he
        have hh := congrArg (fun a : Factorization => a 3) he
        simp only [slicePoint_third] at hh
        omega
  · rintro ⟨hp,hprev⟩
    refine ⟨hp.1,?_⟩
    intro b hb
    have hb0 : b 0=0 := by have hh := hb.le 0; simp at hh; exact hh
    have hbx : b 1≤p.1 := by simpa using hb.le 1
    have hby : b 2≤p.2 := by simpa using hb.le 2
    have hbz : b 3≤z := by simpa using hb.le 3
    have hshape := slicePoint_reconstruct b hb0
    by_cases hz : b 3=z
    · have hlt : (b 1,b 2) < p := by
        apply lt_of_le_of_ne (show (b 1,b 2) ≤ p from ⟨hbx,hby⟩)
        intro he
        apply hb.ne
        rw [←hshape,hz]
        rw [←congrArg Prod.fst he,←congrArg Prod.snd he]
      have hm := hp.2 (b 1,b 2) hlt
      change slicePoint (b 1) (b 2) z ∈ staircase G at hm
      simpa only [←hz,hshape] using hm
    · have hprev' : p ∈ planeSlice G (z-1) := hprev.resolve_left (by omega)
      apply staircase_lower G hprev'
      rw [←hshape]
      exact (slicePoint_le_iff (b 1,b 2) p (b 3) (z-1)).mpr ⟨⟨hbx,hby⟩,by omega⟩

lemma slicePoint_boundary_zero_iff (p : Point) :
    slicePoint p.1 p.2 0 ∈ staircaseBoundary G ↔ p ∈ Boundary (planeSlice G 0) := by
  simp [slicePoint_boundary_iff]

lemma slicePoint_boundary_succ_iff (p : Point) (z : ℕ) :
    slicePoint p.1 p.2 (z+1) ∈ staircaseBoundary G ↔
      p ∈ Generators (planeSlice G z) (planeSlice G (z+1)) := by
  simp [slicePoint_boundary_iff,Generators]

lemma boundary_third_le_top {a : Factorization} (ha : a ∈ staircaseBoundary G) :
    a 3 ≤ criticalExponent G.generators G.positive 3 := by
  by_cases he : a=Finsupp.single 3 (criticalExponent G.generators G.positive 3)
  · simp [he]
  · exact (boundary_below_top_unless_pure G a ha he).le

end FourGeneratedSemigroups
