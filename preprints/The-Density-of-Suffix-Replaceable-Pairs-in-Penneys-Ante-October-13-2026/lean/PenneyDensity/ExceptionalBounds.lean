import PenneyDensity.OverlapCounting

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 theorem probability_false {α : Type*} [Fintype α] :
    probability (fun _ : α => False)=0 := by simp [probability,Nat.card_eq_fintype_card]

 theorem geometric_tail_exact (K n : ℕ) :
    (∑ k ∈ Finset.range n,if K<k then (1/2 : ℝ)^k else 0)=
      if K<n then (1/2 : ℝ)^K-2*(1/2 : ℝ)^n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases hn : K<n
    · have hn' : K<n+1 := by omega
      simp only [hn,hn',ite_true,pow_succ]
      ring
    · by_cases hn' : K<n+1
      · have he : K=n := by omega
        subst n
        simp only [lt_self_iff_false,ite_false,Nat.lt_succ_self,ite_true,pow_succ]
        ring
      · simp only [hn,hn',ite_false,add_zero]

 theorem geometric_tail_bound (K n : ℕ) :
    (∑ k : Fin n,if K<k.val then (1/2 : ℝ)^k.val else 0)≤(1/2 : ℝ)^K := by
  have he := Fin.sum_univ_eq_sum_range (fun k => if K<k then (1/2 : ℝ)^k else 0) n
  rw [he,geometric_tail_exact]
  split
  · have : 0≤(1/2 : ℝ)^n := by positivity
    linarith
  · positivity

 theorem long_overlap_probability_bound (n K : ℕ) :
    probability (fun f : Fin (n+n) → Bool => LongOverlap (pairWords f) K)≤
      4*(1/2 : ℝ)^K := by
  let P : Bool × Bool × Fin n → (Fin (n+n) → Bool) → Prop :=
    fun p f => K<p.2.2.val ∧ properOverlap (pairWords f p.1) (pairWords f p.2.1) p.2.2.val
  have hm : probability (fun f : Fin (n+n) → Bool => LongOverlap (pairWords f) K)≤
      probability (fun f => ∃ p,P p f) := by
    apply probability_mono
    rintro f ⟨b,c,k,hk,ho⟩
    have hkn : k<n := by simpa only [pairWords_length] using ho.2.1
    exact ⟨(b,c,⟨k,hkn⟩),hk,ho⟩
  have hb (p : Bool × Bool × Fin n) : probability (P p)≤
      if K<p.2.2.val then (1/2 : ℝ)^p.2.2.val else 0 := by
    by_cases hk : K<p.2.2.val
    · rw [ite_eq_left hk]
      exact (probability_mono (fun _ hx => hx.2)).trans_eq
        (probability_pair_overlap (by omega) p.2.2.isLt p.1 p.2.1)
    · rw [ite_eq_right hk]
      have he : P p=(fun _ => False) := by funext f; simp only [P,hk,false_and]
      rw [he,probability_false]
  calc
    _ ≤ ∑ p,probability (P p) := hm.trans (probability_exists_le P)
    _ ≤ ∑ p : Bool × Bool × Fin n,if K<p.2.2.val then (1/2 : ℝ)^p.2.2.val else 0 :=
      Finset.sum_le_sum fun p _ => hb p
    _ = 4*∑ k : Fin n,if K<k.val then (1/2 : ℝ)^k.val else 0 := by
      simp only [Fintype.sum_prod_type,Fintype.sum_bool]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (geometric_tail_bound K n) (by norm_num)

 def collisionCoefficient (K : ℕ) : ℝ := (2*(K+1 : ℕ) : ℝ)^2

 theorem block_collision_probability_bound {n K : ℕ} (hn : 2*K<n) :
    probability (fun f : Fin (n+n) → Bool => BlockCollision (pairWords f) n K)≤
      collisionCoefficient K*(1/2 : ℝ)^(n-2*K) := by
  let P : (Bool × Fin (K+1)) × (Bool × Fin (K+1)) → (Fin (n+n) → Bool) → Prop :=
    fun p f => (p.1.1≠p.2.1 ∨ p.1.2.val≠p.2.2.val) ∧
      ((pairWords f p.1.1).drop p.1.2.val).take (n-2*K)=
      ((pairWords f p.2.1).drop p.2.2.val).take (n-2*K)
  have hm : probability (fun f : Fin (n+n) → Bool => BlockCollision (pairWords f) n K)≤
      probability (fun f => ∃ p,P p f) := by
    apply probability_mono
    rintro f ⟨b,c,i,j,hi,hj,hne,he⟩
    exact ⟨((b,⟨i,by omega⟩),(c,⟨j,by omega⟩)),hne,he⟩
  have hb (p : (Bool × Fin (K+1)) × (Bool × Fin (K+1))) :
      probability (P p)≤(1/2 : ℝ)^(n-2*K) := by
    by_cases hne : p.1.1≠p.2.1 ∨ p.1.2.val≠p.2.2.val
    · exact (probability_mono (fun _ hx => hx.2)).trans_eq
        (probability_pair_block_collision p.1.1 p.2.1 (by omega) (by omega) (by omega) (by omega) hne)
    · have he : P p=(fun _ => False) := by funext f; simp only [P,hne,false_and]
      rw [he,probability_false]
      positivity
  calc
    _ ≤ ∑ p,probability (P p) := hm.trans (probability_exists_le P)
    _ ≤ ∑ _p : (Bool × Fin (K+1)) × (Bool × Fin (K+1)),(1/2 : ℝ)^(n-2*K) :=
      Finset.sum_le_sum fun p _ => hb p
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_bool,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,collisionCoefficient]
      ring

end PenneyDensity
