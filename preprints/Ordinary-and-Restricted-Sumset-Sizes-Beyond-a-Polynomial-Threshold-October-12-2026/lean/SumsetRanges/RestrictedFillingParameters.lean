import SumsetRanges.RestrictedFillingExtension

namespace SumsetRanges

/-- Exact integer arithmetic for the residue blow-up parameters. -/
theorem restricted_filling_parameters (h s d : ℕ) (hh : 2≤h)
    (hs : 64*(2*h-1)*h≤s) (hd : s-1≤d)
    (hmax : (64*(2*h-1)*h)^h*d≤(2*h-1)*s^h) :
    let l := 2*h-1
    let n := s/(4*l)
    let D := (d-l+1)/l
    8*h≤n ∧ n-1≤D ∧ (8*h)^h*D≤n^h ∧
      l≤l*D ∧ l*D+l-1≤d ∧ d≤l*D+2*l-2 ∧ l*n+2*l+s/2≤s := by
  let l := 2*h-1
  let n := s/(4*l)
  let D := (d-l+1)/l
  change 8*h≤n ∧ n-1≤D ∧ (8*h)^h*D≤n^h ∧
    l≤l*D ∧ l*D+l-1≤d ∧ d≤l*D+2*l-2 ∧ l*n+2*l+s/2≤s
  have hl : 1≤l := by dsimp [l]; omega
  have hs' : 64*l*h≤s := hs
  have hmax' : (64*l*h)^h*d≤l*s^h := hmax
  have hn : 8*h≤n := (Nat.le_div_iff_mul_le (by positivity)).mpr (by nlinarith)
  have hns : 4*l*n≤s := by dsimp [n]; exact Nat.mul_div_le _ _
  have hsn : s≤8*l*n := by
    have he := Nat.div_add_mod s (4*l)
    have hr := Nat.mod_lt s (by positivity : 0<4*l)
    change 4*l*n+s%(4*l)=s at he
    nlinarith
  have hsd : s≤d+1 := by omega
  have hdl : l≤d := by nlinarith [Nat.mul_le_mul_left l hh]
  have hdm : d-l+l=d := Nat.sub_add_cancel hdl
  have hDdiv := Nat.div_add_mod (d-l+1) l
  change l*D+(d-l+1)%l=d-l+1 at hDdiv
  have hDmod := Nat.mod_lt (d-l+1) (by omega : 0<l)
  have hDl : l*D≤d := by omega
  have hDn : n-1≤D := by
    by_contra hf
    have hhf : l*(D+2)≤l*n := Nat.mul_le_mul_left _ (by omega)
    nlinarith only [hns,hhf,hsd,hdm,hDdiv,hDmod]
  have hDpos : 1≤D := by omega
  have hpower : (8*h)^h*D≤n^h := by
    have hp : (64*l*h)^h*D≤s^h := by
      have hh' : l*((64*l*h)^h*D)≤l*s^h := calc
        _ = (64*l*h)^h*(l*D) := by ring
        _ ≤ (64*l*h)^h*d := Nat.mul_le_mul_left _ hDl
        _ ≤ l*s^h := hmax'
      exact Nat.le_of_mul_le_mul_left hh' (by omega)
    have hscaled : (8*l)^h*((8*h)^h*D)≤(8*l)^h*n^h := calc
      _ = (64*l*h)^h*D := by rw [←mul_assoc,←mul_pow]; congr 2; ring
      _ ≤ s^h := hp
      _ ≤ (8*l*n)^h := Nat.pow_le_pow_left hsn _
      _ = _ := by rw [mul_pow]
    exact Nat.le_of_mul_le_mul_left hscaled (by positivity)
  refine ⟨hn,hDn,hpower,?_,?_,?_,?_⟩
  · nlinarith
  · omega
  · omega
  · have hhalf : 2*(s/2)≤s := Nat.mul_div_le _ _
    nlinarith

end SumsetRanges
