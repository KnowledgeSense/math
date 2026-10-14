import SumsetRanges.RestrictedIntervals
import SumsetRanges.PositionalFilling
import Mathlib.Data.Finset.Sort

open Finset
namespace SumsetRanges

def residueBlowup (A : Finset ℤ) (l : ℕ) : Finset ℤ :=
  (A.product (Icc 0 ((l:ℤ)-1))).image (fun p : ℤ×ℤ => (l:ℤ)*p.1+p.2)

theorem residue_pair_injective (l : ℕ) (hl : 1≤l) (a b r s : ℤ)
    (hr : 0≤r ∧ r<(l:ℤ)) (hs : 0≤s ∧ s<(l:ℤ))
    (he : (l:ℤ)*a+r=(l:ℤ)*b+s) : a=b ∧ r=s := by
  have he' := congrArg (fun x : ℤ => x%(l:ℤ)) he
  have hrs : r=s := by
    simpa [Int.add_emod,Int.mul_emod,Int.emod_eq_of_lt hr.1 hr.2,
      Int.emod_eq_of_lt hs.1 hs.2] using he'
  have hmul : (l:ℤ)*a=(l:ℤ)*b := by omega
  exact ⟨mul_left_cancel₀ (by exact_mod_cast (by omega : l≠0)) hmul,hrs⟩

theorem card_residueBlowup (A : Finset ℤ) (l : ℕ) (hl : 1≤l) :
    (residueBlowup A l).card=l*A.card := by
  rw [residueBlowup,Finset.card_image_of_injOn]
  · simp [Finset.card_product,mul_comm]
  · intro p hp q hq he
    obtain ⟨_,hr⟩ := Finset.mem_product.mp hp
    obtain ⟨_,hs⟩ := Finset.mem_product.mp hq
    have hr' := Finset.mem_Icc.mp hr
    have hs' := Finset.mem_Icc.mp hs
    obtain ⟨ha,hb⟩ := residue_pair_injective l hl p.1 q.1 p.2 q.2
      ⟨hr'.1,by omega⟩ ⟨hs'.1,by omega⟩ he
    exact Prod.ext ha hb

theorem residueBlowup_bounds (A : Finset ℤ) (l D : ℕ)
    (hA : ∀a∈A,0≤a ∧ a≤D) {x : ℤ} (hx : x∈residueBlowup A l) :
    0≤x ∧ x≤(l:ℤ)*D+l-1 := by
  obtain ⟨⟨a,r⟩,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ha,hr⟩ := Finset.mem_product.mp hp
  obtain ⟨hr0,hrl⟩ := Finset.mem_Icc.mp hr
  obtain ⟨ha0,haD⟩ := hA a ha
  constructor <;> nlinarith

theorem int_restricted_tuple (A : Finset ℤ) (q : ℕ) {x : ℤ}
    (hx : x∈restrictedSums A q) :
    ∃v : Fin q → ℤ, (∀i,v i∈A) ∧ Function.Injective v ∧ ∑i,v i=x := by
  obtain ⟨S,hS,hc,rfl⟩ := mem_restrictedSums.mp hx
  refine ⟨S.orderEmbOfFin hc,fun i => hS (S.orderEmbOfFin_mem hc i),
    (S.orderEmbOfFin hc).injective,?_⟩
  conv_rhs => rw [←S.image_orderEmbOfFin_univ hc]
  rw [Finset.sum_image]
  exact fun _ _ _ _ he => (S.orderEmbOfFin hc).injective he

theorem residueBlowup_sum_mem (A : Finset ℤ) (l q : ℕ) (hl : 1≤l)
    {t r : ℤ} (ht : t∈ordinarySums A q) (hr : r∈restrictedSums (Icc 0 ((l:ℤ)-1)) q) :
    (l:ℤ)*t+r∈restrictedSums (residueBlowup A l) q := by
  obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp ht
  obtain ⟨w,hw,hi,rfl⟩ := int_restricted_tuple _ _ hr
  let u : Fin q → ℤ := fun i => (l:ℤ)*v i+w i
  have hu (i : Fin q) : u i∈residueBlowup A l := by
    exact Finset.mem_image.mpr ⟨(v i,w i),Finset.mem_product.mpr ⟨hv i,hw i⟩,rfl⟩
  have hui : Function.Injective u := by
    intro i j he
    have hwi := Finset.mem_Icc.mp (hw i)
    have hwj := Finset.mem_Icc.mp (hw j)
    exact hi (residue_pair_injective l hl (v i) (v j) (w i) (w j)
      ⟨hwi.1,by omega⟩ ⟨hwj.1,by omega⟩ he).2
  have hm := sum_mem_restrictedSums _ q u hu hui
  simpa [u,Finset.sum_add_distrib,Finset.mul_sum] using hm

/-- Distinct residues turn every ordinary representation into a restricted representation. -/
theorem residueBlowup_fills (A : Finset ℤ) (l D h : ℕ) (hl : 1≤l) (hhl : h≤l)
    (hwidth : (l:ℤ)≤(h:ℤ)*(l-1)-2*(h.choose 2:ℤ)+1)
    (hA : ∀a∈A,0≤a ∧ a≤D) (hfill : ordinarySums A h=Icc 0 ((h*D:ℕ):ℤ)) :
    restrictedSums (residueBlowup A l) h=
      Icc (h.choose 2:ℤ) ((h:ℤ)*((l:ℤ)*D+l-1)-h.choose 2) := by
  have hres := restrictedSums_int_Icc 0 ((l:ℤ)-1) h (by omega) (by omega)
  simp only [mul_zero,zero_add] at hres
  ext x
  constructor
  · intro hx
    simpa using Finset.mem_Icc.mpr (restrictedSums_int_bounds (residueBlowup A l)
      0 ((l:ℤ)*D+l-1) (fun _ hx => residueBlowup_bounds A l D hA hx) h hx)
  · intro hx
    obtain ⟨hx0,hxD⟩ := Finset.mem_Icc.mp hx
    let low (j : ℕ) : ℤ := -((l:ℤ)*j+(h:ℤ)*(l-1)-h.choose 2)
    let high (j : ℕ) : ℤ := -((l:ℤ)*j+h.choose 2)
    have cover (j : ℕ) (_hj : j≤h*D) (z : ℤ) (hz : low j≤z) (hz' : z≤high j) :
        ∃r : ℤ,r∈restrictedSums (Icc 0 ((l:ℤ)-1)) h ∧ -((l:ℤ)*j+r)=z := by
      refine ⟨-z-(l:ℤ)*j,?_,by ring⟩
      rw [hres]
      apply Finset.mem_Icc.mpr
      dsimp [low,high] at hz hz'
      constructor <;> omega
    have hlo (j : ℕ) (_hj : j<h*D) : low (j+1)≤low j := by dsimp [low]; nlinarith
    have hov (j : ℕ) (_hj : j<h*D) : low j≤high (j+1)+1 := by
      dsimp [low,high]; nlinarith
    obtain ⟨j,hj,r,hr,he⟩ := integer_interval_chain (fun j r => -((l:ℤ)*j+r))
      (fun _ r => r∈restrictedSums (Icc 0 ((l:ℤ)-1)) h) low high (h*D)
      cover hlo hov (-x) (by dsimp [low]; nlinarith)
      (by dsimp [high]; simp only [mul_zero,zero_add]; omega)
    have hjmem : (j:ℤ)∈ordinarySums A h := by
      rw [hfill]
      exact Finset.mem_Icc.mpr ⟨by positivity,by exact_mod_cast hj⟩
    have hm := residueBlowup_sum_mem A l h hl hjmem hr
    have he' : (l:ℤ)*j+r=x := by omega
    simpa [he'] using hm

end SumsetRanges
