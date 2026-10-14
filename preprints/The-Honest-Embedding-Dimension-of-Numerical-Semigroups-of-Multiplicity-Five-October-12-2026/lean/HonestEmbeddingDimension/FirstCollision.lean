import HonestEmbeddingDimension.TripleJets

namespace HonestEmbeddingDimension

/-- No new value occurs before two nonparameter monomials acquire the same residue. -/
theorem triple_value_below_injective_residues (m a b L : ℕ)
    (hm : m ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (Y Z : PowerSeries ℂ) (hY : Y.order = a) (hZ : Z.order = b)
    (hres : ∀ p q p' q' : ℕ, a*p+b*q < L → a*p'+b*q' < L →
      (a*p+b*q)%m = (a*p'+b*q')%m → p=p' ∧ q=q')
    (n : ℕ) (hn : n < L) (hv : n ∈ polynomialValues (tripleCoordinates m Y Z)) :
    ∃ k p q : ℕ, n = m*k+a*p+b*q := by
  obtain ⟨P,hP⟩ := hv
  obtain ⟨u,hu⟩ := triple_polynomial_jet m a b L hm ha hb Y Z hY hZ P
  have ho := (order_eq_of_jet_eq hu hn).mp hP
  obtain ⟨v,_,k,hk⟩ := order_of_parameter_span Finset.univ m hm u
    (fun v : TripleJetIndex a b L => Y^v.val.1.val * Z^v.val.2.val)
    (fun v => a*v.val.1.val+b*v.val.2.val)
    (by intro v _; simp [PowerSeries.order_mul,PowerSeries.order_pow,hY,hZ,nsmul_eq_mul,mul_comm])
    (by
      intro v _ w _ hvw he
      obtain ⟨h1,h2⟩ := hres v.val.1.val v.val.2.val w.val.1.val w.val.2.val v.property w.property he
      apply hvw
      apply Subtype.ext
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)) n ho
  exact ⟨k,v.val.1.val,v.val.2.val,by simpa only [Nat.add_assoc] using hk⟩

/-- A genuinely new value must lie strictly beyond a collision threshold which is already generated. -/
theorem new_triple_value_gt_collision (m a b L c : ℕ)
    (hm : m ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (Y Z : PowerSeries ℂ) (hY : Y.order = a) (hZ : Z.order = b)
    (hres : ∀ p q p' q' : ℕ, a*p+b*q < L → a*p'+b*q' < L →
      (a*p+b*q)%m = (a*p'+b*q')%m → p=p' ∧ q=q')
    (hL : ∃ k p q : ℕ, L = m*k+a*p+b*q)
    (hc : c ∈ polynomialValues (tripleCoordinates m Y Z))
    (hnew : ¬∃ k p q : ℕ, c = m*k+a*p+b*q) : L < c := by
  have hle : L ≤ c := by
    by_contra hn
    exact hnew (triple_value_below_injective_residues m a b L hm ha hb Y Z hY hZ hres c (by omega) hc)
  have hne : L ≠ c := by intro he; exact hnew (he ▸ hL)
  omega

end HonestEmbeddingDimension
