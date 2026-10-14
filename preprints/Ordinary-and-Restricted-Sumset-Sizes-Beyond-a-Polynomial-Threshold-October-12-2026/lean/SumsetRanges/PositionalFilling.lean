import SumsetRanges.FillingExtension
import Mathlib.Data.Nat.Find

open Finset
namespace SumsetRanges

/-- The positional filling lemma, with the rational diameter bound cleared of denominators. -/
theorem positional_filling (h n D : ℕ) (hh : 2≤h) (hn : 8*h≤n)
    (hD : n-1≤D) (hmax : (8*h)^h*D≤n^h) :
    ∃B : Finset ℤ, B.card=n ∧ B⊆Icc 0 (D:ℤ) ∧
      (∀x : ℕ,x<n/2 → (x:ℤ)∈B) ∧ ordinarySums B h=Icc 0 ((h*D:ℕ):ℤ) := by
  let g := n/(4*h)
  have hg : 2≤g := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  have hgn : 4*h*g≤n := by dsimp [g]; exact Nat.mul_div_le n (4*h)
  have hng : n≤8*h*g := by
    have hdiv := Nat.div_add_mod n (4*h)
    have hmod := Nat.mod_lt n (by omega : 0<4*h)
    change 4*h*g+n%(4*h)=n at hdiv
    nlinarith
  have hpow : D≤g^h := by
    have hp : (8*h)^h*D≤(8*h)^h*g^h := calc
      _ ≤ n^h := hmax
      _ ≤ (8*h*g)^h := Nat.pow_le_pow_left hng _
      _ = _ := by rw [mul_pow]
    exact Nat.le_of_mul_le_mul_left hp (by positivity)
  have hex : ∃r : ℕ,D≤g^r := ⟨h,hpow⟩
  let r := Nat.find hex
  have hr : D≤g^r := Nat.find_spec hex
  have hrh : r≤h := Nat.find_min' hex hpow
  have hr0 : 0<r := by
    by_contra hz
    have he : r=0 := by omega
    rw [he,pow_zero] at hr
    omega
  let s := r-1
  have hsr : s+1=r := by dsimp [s]; omega
  have hsD : g^s≤D := by
    have hm := Nat.find_min hex (show s<r by dsimp [s]; omega)
    change ¬D≤g^s at hm
    omega
  have hDs : D≤g^(s+1) := by simpa [hsr] using hr
  let A := positionalCore g s D
  have hAc : A.card≤g+2+2*s*g := card_positionalCore_le g s D (by omega) hDs
  have hAn : A.card+n/2≤n := by
    have hs : s+1≤h := by omega
    have hhalf : 2*A.card≤n := by nlinarith
    omega
  have hAb : A⊆Icc 0 (D:ℤ) := by
    intro a ha
    exact Finset.mem_Icc.mpr (positionalCore_bounds g s D (by omega) hsD ha)
  have hfill : ordinarySums A h=Icc 0 ((h*D:ℕ):ℤ) := by
    apply ordinary_filling_extend A D (s+1) h (by omega) (by omega)
      (fun a ha => Finset.mem_Icc.mp (hAb ha))
      (zero_mem_positionalCore g s D) (top_mem_positionalCore g s D)
    exact positionalCore_fills g s D (by omega) hsD
  exact filling_pad A D h n (n/2) hAb (by omega) hAn hfill

end SumsetRanges
