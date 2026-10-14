import SumsetRanges.OrdinaryFiniteModel

namespace SumsetRanges

theorem ordinary_model_diameter_bound (h k D : ℕ) (hh : 1≤h) (hk : h+1≤k)
    (hD : 1≤D) (hDk : D≤k) (hDh : D≤h^2+2*h+2) :
    D*(h*k^(h*h))*(h*(h*k^(h*h))+1)^(D-1)≤k^(ordinaryExponent h) := by
  let L := h*h
  let M := h*k^L
  have hk1 : 1≤k := by omega
  have hM : 1≤M := by dsimp [M]; have hp := Nat.one_le_pow L k hk1; nlinarith
  have hMk : M≤k^(L+1) := by
    dsimp [M]
    rw [pow_succ]
    exact (Nat.mul_le_mul_right (k^L) (by omega : h≤k)).trans_eq (Nat.mul_comm _ _)
  have hDM : D*M≤k^(L+2) := by
    calc
      D*M ≤ k*k^(L+1) := Nat.mul_le_mul hDk hMk
      _ = k^(L+2) := by simp [pow_succ, Nat.mul_comm]
  have hQ : h*M+1≤k^(L+2) := by
    calc
      h*M+1 ≤ (h+1)*M := by nlinarith
      _ ≤ k*M := Nat.mul_le_mul_right M hk
      _ ≤ k*k^(L+1) := Nat.mul_le_mul_left k hMk
      _ = k^(L+2) := by simp [pow_succ, Nat.mul_comm]
  change D*M*(h*M+1)^(D-1)≤_
  calc
    _ ≤ k^(L+2)*(k^(L+2))^(D-1) := Nat.mul_le_mul hDM (Nat.pow_le_pow_left hQ _)
    _ = k^((L+2)*D) := by
      rw [←pow_mul,←pow_add]
      congr 1
      have he : D-1+1=D := by omega
      nlinarith
    _ ≤ k^(ordinaryExponent h) := by
      apply Nat.pow_le_pow_right hk1
      dsimp [ordinaryExponent,L]
      simpa [pow_two] using Nat.mul_le_mul_left (h*h+2) hDh

end SumsetRanges
