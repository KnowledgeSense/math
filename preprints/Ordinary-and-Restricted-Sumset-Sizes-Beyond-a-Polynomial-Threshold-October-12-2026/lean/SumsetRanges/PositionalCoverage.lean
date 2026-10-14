import SumsetRanges.PositionalBounds
import SumsetRanges.IntervalChain
import Mathlib.Data.Int.Interval

open Finset
open scoped Pointwise
namespace SumsetRanges

theorem topDigits_cover (g s D u : ℕ) (hg : 1≤g) (hu : u<D+g^s) :
    ∃a∈topDigits g s D, ∃t : ℕ, t<g^s ∧ a+(t:ℤ)=(u:ℤ) := by
  have hp : 0<g^s := by positivity
  by_cases hq : u/g^s≤D/g^s
  · refine ⟨((u/g^s*g^s:ℕ):ℤ),?_,u%g^s,Nat.mod_lt _ hp,?_⟩
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨u/g^s,Finset.mem_range.mpr (by omega),rfl⟩
    · have he := Nat.div_add_mod u (g^s)
      rw [mul_comm (g^s)] at he
      exact_mod_cast he
  · have hDu : D≤u := by
      by_contra hh
      have hh' := Nat.div_le_div_right (c:=g^s) (by omega : u≤D)
      omega
    refine ⟨D,Finset.mem_insert_self _ _,u-D,by omega,?_⟩
    exact_mod_cast Nat.add_sub_of_le hDu

/-- One top digit joins the adjacent positional intervals, including the final short gap. -/
theorem positional_interval_mem (g s D j : ℕ) (hg : 1≤g) (hj : j≤s)
    (w : ℤ) (hlo : (j:ℤ)*D+1-(g:ℤ)^j≤w)
    (hhi : w≤(j+1:ℕ)*D+(g:ℤ)^s-(g:ℤ)^j) :
    w∈ordinarySums (positionalCore g s D) (s+1) := by
  let u := (w-((j:ℤ)*D+1-(g:ℤ)^j)).toNat
  have hu : (u:ℤ)=w-((j:ℤ)*D+1-(g:ℤ)^j) := Int.toNat_of_nonneg (by omega)
  have hub : u<D+g^s := by
    have he : ((D+g^s:ℕ):ℤ)=(D:ℤ)+(g:ℤ)^s := by push_cast; rfl
    have he' : ((j+1:ℕ):ℤ)=(j:ℤ)+1 := by push_cast; rfl
    exact_mod_cast (show (u:ℤ)<((D+g^s:ℕ):ℤ) by rw [hu,he]; rw [he'] at hhi; nlinarith)
  obtain ⟨a,ha,t,ht,he⟩ := topDigits_cover g s D u hg hub
  have htmem := mixed_digits_mem g s D j t hg hj ht
  rw [ordinarySums]
  apply Finset.mem_add.mpr
  refine ⟨a,topDigits_subset_core g s D ha,_,htmem,?_⟩
  omega

/-- The concrete positional core fills the whole interval using s+1 summands. -/
theorem positionalCore_fills (g s D : ℕ) (hg : 1≤g) (hD : g^s≤D) :
    ordinarySums (positionalCore g s D) (s+1)=Finset.Icc 0 (((s+1)*D:ℕ):ℤ) := by
  ext w
  constructor
  · intro hw
    obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hw
    apply Finset.mem_Icc.mpr
    constructor
    · exact Finset.sum_nonneg (fun i _ => (positionalCore_bounds g s D hg hD (hv i)).1)
    · calc
        (∑i,v i) ≤ ∑_i : Fin (s+1),(D:ℤ) :=
          Finset.sum_le_sum (fun i _ => (positionalCore_bounds g s D hg hD (hv i)).2)
        _ = (((s+1)*D:ℕ):ℤ) := by simp
  · intro hw
    obtain ⟨hw0,hwD⟩ := Finset.mem_Icc.mp hw
    let lo (j : ℕ) : ℤ := -((j+1:ℕ)*D+(g:ℤ)^s-(g:ℤ)^j)
    let hi (j : ℕ) : ℤ := -((j:ℤ)*D+1-(g:ℤ)^j)
    have hcover (j : ℕ) (hj : j≤s) (z : ℤ) (hz : lo j≤z) (hz' : z≤hi j) :
        ∃x : ℤ, x∈ordinarySums (positionalCore g s D) (s+1) ∧ -x=z := by
      refine ⟨-z,positional_interval_mem g s D j hg hj (-z) ?_ ?_,by omega⟩
      · dsimp [hi] at hz'; omega
      · dsimp [lo] at hz; push_cast at hz ⊢; omega
    have hpow (j : ℕ) (hj : j≤s) : (g:ℤ)^j≤D := by
      exact_mod_cast (Nat.le_trans (Nat.pow_le_pow_right hg hj) hD)
    have hlo (j : ℕ) (hj : j<s) : lo (j+1)≤lo j := by
      have hp := hpow (j+1) (by omega)
      have h0 : 0≤(g:ℤ)^j := by positivity
      dsimp [lo]
      nlinarith
    have hov (j : ℕ) (hj : j<s) : lo j≤hi (j+1)+1 := by
      have hp : (g:ℤ)^j≤(g:ℤ)^s := by exact_mod_cast Nat.pow_le_pow_right hg (by omega : j≤s)
      have h0 : 0≤(g:ℤ)^(j+1) := by positivity
      dsimp [lo,hi]
      nlinarith
    obtain ⟨j,_,x,hx,he⟩ := integer_interval_chain (fun _ (x : ℤ) => -x)
      (fun _ x => x∈ordinarySums (positionalCore g s D) (s+1)) lo hi s
      hcover hlo hov (-w) (by dsimp [lo]; push_cast at hwD ⊢; omega)
      (by simpa [hi] using neg_nonpos.mpr hw0)
    have hxw : x=w := by omega
    simpa [hxw] using hx

end SumsetRanges
