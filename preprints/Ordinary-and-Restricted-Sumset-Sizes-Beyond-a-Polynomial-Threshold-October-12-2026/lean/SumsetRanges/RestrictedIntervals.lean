import SumsetRanges.DenseRestricted

open Finset
namespace SumsetRanges

theorem restrictedSums_mono {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {A B : Finset α} (hAB : A⊆B) (q : ℕ) : restrictedSums A q⊆restrictedSums B q := by
  intro x hx
  obtain ⟨S,hS,hc,rfl⟩ := mem_restrictedSums.mp hx
  exact mem_restrictedSums.mpr ⟨S,hS.trans hAB,hc,rfl⟩

theorem sum_mem_restrictedSums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (q : ℕ) (v : Fin q → α) (hv : ∀i,v i∈A)
    (hinj : Function.Injective v) : (∑i,v i)∈restrictedSums A q := by
  apply mem_restrictedSums.mpr
  refine ⟨univ.image v,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hv i
  · rw [Finset.card_image_of_injective _ hinj]; simp
  · rw [Finset.sum_image]; exact fun _ _ _ _ he => hinj he

theorem restrictedSums_int_bounds (A : Finset ℤ) (a b : ℤ)
    (hA : ∀x∈A,a≤x ∧ x≤b) (q : ℕ) {x : ℤ} (hx : x∈restrictedSums A q) :
    (q:ℤ)*a+q.choose 2≤x ∧ x≤(q:ℤ)*b-q.choose 2 := by
  obtain ⟨S,hS,hc,rfl⟩ := mem_restrictedSums.mp hx
  have hl := Finset.sum_range_le_sum (fun x hx => (hA x (hS hx)).1)
  have hu := Finset.sum_le_sum_range (fun x hx => (hA x (hS hx)).2)
  rw [hc,Finset.sum_add_distrib,sum_range_natCast] at hl
  rw [hc,Finset.sum_sub_distrib,sum_range_natCast] at hu
  simpa [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using And.intro hl hu

/-- Exact restricted sums of an integer interval, including its constructive intermediate values. -/
theorem restrictedSums_int_Icc (a b : ℤ) (q : ℕ) (hab : a≤b)
    (hq : (q:ℤ)≤b-a+1) :
    restrictedSums (Icc a b) q=Icc ((q:ℤ)*a+q.choose 2) ((q:ℤ)*b-q.choose 2) := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr (restrictedSums_int_bounds _ a b
      (fun _ hx => Finset.mem_Icc.mp hx) q hx)
  · intro hx
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hx
    by_cases hq0 : q=0
    · subst q
      have hx0 : x=0 := by simp at hl hu; omega
      simp [hx0]
    have hqp : 0<q := by omega
    let n := (b-a+1).toNat
    have hn : (n:ℤ)=b-a+1 := Int.toNat_of_nonneg (by omega)
    have hqn : q≤n := by exact_mod_cast (show (q:ℤ)≤n by omega)
    let t := (x-(q:ℤ)*a-q.choose 2).toNat
    have ht : (t:ℤ)=x-(q:ℤ)*a-q.choose 2 := Int.toNat_of_nonneg (by omega)
    have htc : t≤q*(n-q) := by
      have he := choose_two_double q
      have he' : 2*(q.choose 2:ℤ)=(q:ℤ)*((q:ℤ)-1) := by
        have hz : (2:ℤ)*(q.choose 2:ℤ)=(q:ℤ)*((q-1:ℕ):ℤ) := by exact_mod_cast he
        simpa [Int.ofNat_sub (show 1≤q by omega)] using hz
      have hsub : ((n-q:ℕ):ℤ)=(n:ℤ)-q := Int.ofNat_sub hqn
      have hi : (t:ℤ)≤(q:ℤ)*((n:ℤ)-q) := by nlinarith
      exact_mod_cast (show (t:ℤ)≤((q*(n-q):ℕ):ℤ) by push_cast; rw [hsub]; exact hi)
    let v : Fin q → ℤ := fun i => a+(balancedPoint q t i:ℤ)
    have hv (i : Fin q) : v i∈Icc a b := by
      have hp := balancedPoint_lt n q t hqp hqn htc i
      apply Finset.mem_Icc.mpr
      dsimp [v]
      have hp' : (balancedPoint q t i:ℤ)<n := by exact_mod_cast hp
      constructor <;> omega
    have hi : Function.Injective v := by
      intro i j he
      have he' : balancedPoint q t i=balancedPoint q t j := by
        dsimp [v] at he
        exact_mod_cast (add_left_cancel he)
      exact (balancedPoint_strictMono q t).injective he'
    have hm := sum_mem_restrictedSums _ q v hv hi
    have hs : (∑i,v i)=x := by
      dsimp [v]
      rw [Finset.sum_add_distrib]
      have hp : (∑i : Fin q,(balancedPoint q t i:ℤ))=(q.choose 2:ℤ)+t := by
        exact_mod_cast sum_balancedPoint q t hqp
      rw [hp]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      omega
    simpa [hs] using hm

end SumsetRanges
