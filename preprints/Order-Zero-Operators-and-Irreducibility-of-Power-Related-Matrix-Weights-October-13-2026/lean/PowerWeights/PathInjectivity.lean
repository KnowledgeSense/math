import PowerWeights.LowerBlock

namespace PowerWeights

/-- The actual path matrix is injective on vectors supported on odd indices.
The proof proceeds from the endpoint and uses every existing edge. -/
theorem path_mul_zero_odd_rows {N : ℕ} (a : ℕ → ℝ)
    (ha : ∀ i, i+1 < N → a i ≠ 0)
    (M : Matrix (Fin N) (Fin N) ℂ) (h : pathMatrix N a*M=0) :
    ∀ (r j : Fin N), r.val%2=1 → M r j=0 := by
  have aux : ∀ n, ∀ hn : n<N, n%2=1 → ∀ j : Fin N, M ⟨n,hn⟩ j=0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hnodd j
      have hnpos : 0<n := by omega
      let r : Fin N := ⟨n,hn⟩
      let p : Fin N := ⟨n-1,by omega⟩
      have hpr : pathMatrix N a p r = (a (n-1) : ℂ) := by
        have hp : p.val%2=0 := by dsimp [p]; omega
        have hval : r.val=p.val+1 := by dsimp [r,p]; omega
        simp [pathMatrix, hp, hval, p]
      have hsum : (pathMatrix N a*M) p j = pathMatrix N a p r*M r j := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_single r
        · intro t _ htr
          by_cases hat : pathMatrix N a p t=0
          · simp [hat]
          · have hs := path_support hat
            have htne : t.val ≠ n := by
              intro ht
              apply htr
              apply Fin.ext
              exact ht
            have htlt : t.val<n := by dsimp [p] at hs; omega
            have hMt := ih t.val htlt t.isLt hs.2.1 j
            have hMt' : M t j=0 := hMt
            simp [hMt']
        · simp
      have hz := congrArg (fun Q : Matrix (Fin N) (Fin N) ℂ => Q p j) h
      rw [hsum, hpr] at hz
      have hane : (a (n-1) : ℂ) ≠ 0 := by
        exact_mod_cast ha (n-1) (by omega)
      exact (mul_eq_zero.mp hz).resolve_left hane
  intro r j hr
  exact aux r.val r.isLt hr j

 theorem lower_times_path_zero {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (ha : ∀ i, i+1 < N → a i ≠ 0)
    (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F))
    (i j : Fin N) (hi : i.val%2=1) : (F*pathMatrix N a) i j=0 := by
  apply path_mul_zero_odd_rows a ha (F*pathMatrix N a) ?_ i j hi
  rw [← mul_assoc]
  exact path_sandwich_zero s a F h

end PowerWeights
