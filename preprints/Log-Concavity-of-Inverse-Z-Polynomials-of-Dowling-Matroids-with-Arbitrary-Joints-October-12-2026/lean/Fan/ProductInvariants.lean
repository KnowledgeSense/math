import ThagomizerTuran.KLIncidence

/-! Product interval evaluation needed for the actual fan restriction components. -/
namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra

variable {α β : Type*} [PartialOrder α] [PartialOrder β]
  [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableEq α] [DecidableEq β] [DecidableLE α] [DecidableLE β]

theorem mu_product (a b : α × β) : IncidenceAlgebra.mu ℤ a b =
    IncidenceAlgebra.mu ℤ a.1 b.1 * IncidenceAlgebra.mu ℤ a.2 b.2 := by
  have h := congrArg (fun f : IncidenceAlgebra ℤ (α × β) => f a b)
    (mu_prod_mu (𝕜:=ℤ) (α:=α) (β:=β))
  exact h.symm

theorem characteristic_product (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) (a b : α × β) (_hab : a ≤ b) :
    characteristic (fun x : α × β => r x.1+s x.2) a b =
      characteristic r a.1 b.1 * characteristic s a.2 b.2 := by
  classical
  simp only [characteristic,Icc_prod_def,sum_product,sum_mul_sum]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  have hxr := hr (mem_Icc.mp hx).2
  have hys := hs (mem_Icc.mp hy).2
  rw [mu_product,map_mul]
  have he : r b.1+s b.2-(r x+s y)=(r b.1-r x)+(s b.2-s y) := by omega
  simp only [he,pow_add]
  ring

omit [DecidableLE α] [DecidableLE β] in
theorem kl_product_high (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) (a b : α × β) (hab : a < b)
    (i : ℕ) (hi : r b.1+s b.2-(r a.1+s a.2) ≤ 2*i) :
    (kl r b.1 a.1 * kl s b.2 a.2).coeff i=0 := by
  have hle := le_of_lt hab
  have h1 := hr hle.1
  have h2 := hs hle.2
  by_cases ha : a.1=b.1
  · have hb : a.2≠b.2 := fun hb => (ne_of_lt hab) (Prod.ext ha hb)
    rw [ha,kl_self,one_mul]
    exact kl_high_coeff s a.2 b.2 hb i (by omega)
  by_cases hb : a.2=b.2
  · rw [hb,kl_self,mul_one]
    exact kl_high_coeff r a.1 b.1 ha i (by omega)
  rw [coeff_mul]
  apply sum_eq_zero
  intro ij hij
  have hij' := mem_antidiagonal.mp hij
  by_cases hi1 : r b.1-r a.1 ≤ 2*ij.1
  · rw [kl_high_coeff r a.1 b.1 ha ij.1 hi1,zero_mul]
  · rw [kl_high_coeff s a.2 b.2 hb ij.2 (by omega),mul_zero]

theorem kl_product (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) (a b : α × β) (hab : a ≤ b) :
    kl (fun x : α × β => r x.1+s x.2) b a = kl r b.1 a.1 * kl s b.2 a.2 := by
  symm
  apply kl_eq_of_characterization (fun x : α × β => r x.1+s x.2)
    (fun a b => kl r b.1 a.1 * kl s b.2 a.2) ?_ ?_ ?_ a b hab
  · intro x
    simp only [kl_self,mul_one]
  · exact kl_product_high r s hr hs
  · intro c d hcd
    have h1 := hr hcd.1
    have h2 := hs hcd.2
    have he : r d.1+s d.2-(r c.1+s c.2)=(r d.1-r c.1)+(s d.2-s c.2) := by omega
    rw [he,reflect_mul _ _ (kl_natDegree_le r c.1 d.1) (kl_natDegree_le s c.2 d.2),
      kl_functional_equation r hr c.1 d.1 hcd.1,
      kl_functional_equation s hs c.2 d.2 hcd.2]
    rw [sum_mul_sum,Icc_prod_def,sum_product]
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro y hy
    rw [characteristic_product r s hr hs c (x,y) ⟨(mem_Icc.mp hx).1,(mem_Icc.mp hy).1⟩]
    ring

theorem klKernel_product (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) :
    klKernel (fun x : α × β => r x.1+s x.2)=(klKernel r).prod (klKernel s) := by
  apply IncidenceAlgebra.ext
  intro a b hab
  exact kl_product r s hr hs a b hab

theorem klInverseKernel_product (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) :
    klInverseKernel (fun x : α × β => r x.1+s x.2)=
      (klInverseKernel r).prod (klInverseKernel s) := by
  apply incidence_leftInverse_unique (klKernel (fun x : α × β => r x.1+s x.2))
  · intro x
    exact kl_self _ x
  · exact klInverseKernel_mul_klKernel _
  · rw [klKernel_product r s hr hs,prod_mul_prod,
      klInverseKernel_mul_klKernel,klInverseKernel_mul_klKernel,one_prod_one]

theorem inverseKL_product (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) (a b : α × β) (hab : a ≤ b) :
    inverseKL (fun x : α × β => r x.1+s x.2) a b =
      inverseKL r a.1 b.1 * inverseKL s a.2 b.2 := by
  have hk := congrArg (fun f : IncidenceAlgebra (Polynomial ℤ) (α × β) => f a b)
    (klInverseKernel_product r s hr hs)
  change klInverse (fun x : α × β => r x.1+s x.2) a b =
    klInverse r a.1 b.1 * klInverse s a.2 b.2 at hk
  have h1 := hr hab.1
  have h2 := hs hab.2
  have he : r b.1+s b.2-(r a.1+s a.2)=(r b.1-r a.1)+(s b.2-s a.2) := by omega
  simp only [inverseKL,he,pow_add,map_mul,hk]
  ring


theorem inverseZ_product (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) (a b : α × β) (_hab : a ≤ b) :
    inverseZ (fun x : α × β => r x.1+s x.2) a b =
      inverseZ r a.1 b.1 * inverseZ s a.2 b.2 := by
  classical
  simp only [inverseZ,Icc_prod_def,sum_product,sum_mul_sum]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  have h1 := hr (mem_Icc.mp hx).2
  have h2 := hs (mem_Icc.mp hy).2
  have he : r b.1+s b.2-(r x+s y)=(r b.1-r x)+(s b.2-s y) := by omega
  rw [inverseKL_product r s hr hs a (x,y) ⟨(mem_Icc.mp hx).1,(mem_Icc.mp hy).1⟩]
  simp only [he,pow_add,mu_product,map_mul]
  ring

end MatroidInverseZ
