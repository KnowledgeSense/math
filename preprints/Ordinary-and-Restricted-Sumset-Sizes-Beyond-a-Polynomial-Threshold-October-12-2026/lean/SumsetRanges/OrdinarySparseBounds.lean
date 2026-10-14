import SumsetRanges.OrdinaryParameters

open Finset
namespace SumsetRanges

@[simp] theorem ordinarySeries_constant {α : Type*} [AddCommMonoid α] [DecidableEq α] (A : Finset α) :
    PowerSeries.constantCoeff (ordinarySeries A)=1 := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff,coeff_ordinarySeries]
  simp [ordinarySums]

@[simp] theorem geometricSeries_constant : PowerSeries.constantCoeff geometricSeries=1 := by
  simp [geometricSeries]

theorem SeriesNonneg.prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ)
    (hf : ∀i∈s,SeriesNonneg (f i)) : SeriesNonneg (∏i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SeriesNonneg.one
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hf a (mem_insert_self _ _)).mul (ih (fun i hi => hf i (mem_insert_of_mem hi)))

theorem SeriesLE.prod {ι : Type*} (s : Finset ι) (f g : ι → PowerSeries ℤ)
    (hf : ∀i∈s,SeriesNonneg (f i)) (hg : ∀i∈s,SeriesNonneg (g i))
    (hfg : ∀i∈s,SeriesLE (f i) (g i)) : SeriesLE (∏i∈s,f i) (∏i∈s,g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact SeriesLE.refl _
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hfg a (mem_insert_self _ _)).mul
        (ih (fun i hi => hf i (mem_insert_of_mem hi)) (fun i hi => hg i (mem_insert_of_mem hi))
          (fun i hi => hfg i (mem_insert_of_mem hi)))
        (SeriesNonneg.prod s f (fun i hi => hf i (mem_insert_of_mem hi))) (hg a (mem_insert_self _ _))

noncomputable def ordinaryCore (h : ℕ) (r u : ℕ → ℕ) : PowerSeries ℤ :=
  ∏m∈Icc 2 (h-1),ordinarySeries (carryG (m+1) (r m))*ordinarySeries (carryH m (u m))

noncomputable def ordinaryOther (h m : ℕ) (r u : ℕ → ℕ) : PowerSeries ℤ :=
  ∏j∈(Icc 2 (h-1)).erase m,ordinarySeries (carryG (j+1) (r j))*ordinarySeries (carryH j (u j))

theorem ordinaryCore_nonneg (h : ℕ) (r u : ℕ → ℕ) : SeriesNonneg (ordinaryCore h r u) :=
  SeriesNonneg.prod _ _ (fun _ _ => (ordinarySeries_nonneg _).mul (ordinarySeries_nonneg _))

theorem ordinaryOther_nonneg (h m : ℕ) (r u : ℕ → ℕ) : SeriesNonneg (ordinaryOther h m r u) :=
  SeriesNonneg.prod _ _ (fun _ _ => (ordinarySeries_nonneg _).mul (ordinarySeries_nonneg _))

@[simp] theorem ordinaryCore_constant (h : ℕ) (r u : ℕ → ℕ) :
    PowerSeries.constantCoeff (ordinaryCore h r u)=1 := by simp [ordinaryCore]

@[simp] theorem ordinaryOther_constant (h m : ℕ) (r u : ℕ → ℕ) :
    PowerSeries.constantCoeff (ordinaryOther h m r u)=1 := by simp [ordinaryOther]

theorem one_le_series_of_constant {A : PowerSeries ℤ} (hA : SeriesNonneg A)
    (h0 : PowerSeries.constantCoeff A=1) : SeriesLE 1 A := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff,h0,map_one] using series_constant_le hA

theorem ordinary_block_bound (m : ℕ) (r u : ℕ → ℕ) (hm : 2≤m) :
    SeriesLE (ordinarySeries (carryG (m+1) (r m))*ordinarySeries (carryH m (u m)))
      (geometricSeries^(2*r m+1+2*u m)) := by
  rw [pow_add]
  exact (ordinary_carryG_series_bound _ _ (by omega)).mul (ordinary_carryH_series_bound m (u m) hm)
    (ordinarySeries_nonneg _) (geometricSeries_nonneg.pow _)

theorem ordinaryCore_bound (h : ℕ) (r u : ℕ → ℕ) :
    SeriesLE (ordinaryCore h r u) (geometricSeries^(ordinaryNonfreeSize h r u)) := by
  unfold ordinaryCore ordinaryNonfreeSize
  rw [←Finset.prod_pow_eq_pow_sum]
  exact SeriesLE.prod _ _ _ (fun _ _ => (ordinarySeries_nonneg _).mul (ordinarySeries_nonneg _))
    (fun _ _ => geometricSeries_nonneg.pow _) (fun m hm => ordinary_block_bound m r u (mem_Icc.mp hm).1)

theorem ordinarySparseSeries_nonneg (h c : ℕ) (r u : ℕ → ℕ) : SeriesNonneg (ordinarySparseSeries h c r u) :=
  (geometricSeries_nonneg.pow _).mul (ordinaryCore_nonneg h r u)

@[simp] theorem ordinarySparseSeries_constant (h c : ℕ) (r u : ℕ → ℕ) :
    PowerSeries.constantCoeff (ordinarySparseSeries h c r u)=1 := by simp [ordinarySparseSeries]

theorem ordinarySparseSeries_lower (h c : ℕ) (r u : ℕ → ℕ) :
    SeriesLE (geometricSeries^(c-ordinaryNonfreeSize h r u)) (ordinarySparseSeries h c r u) := by
  have he := (SeriesLE.refl (geometricSeries^(c-ordinaryNonfreeSize h r u))).mul
    (one_le_series_of_constant (ordinaryCore_nonneg h r u) (ordinaryCore_constant h r u))
    SeriesNonneg.one (geometricSeries_nonneg.pow _)
  simpa only [mul_one,ordinarySparseSeries,ordinaryCore] using he

theorem ordinarySparseSeries_upper (h c : ℕ) (r u : ℕ → ℕ) (hc : ordinaryNonfreeSize h r u≤c) :
    SeriesLE (ordinarySparseSeries h c r u) (geometricSeries^c) := by
  have he := (SeriesLE.refl (geometricSeries^(c-ordinaryNonfreeSize h r u))).mul
    (ordinaryCore_bound h r u) (ordinaryCore_nonneg h r u) (geometricSeries_nonneg.pow _)
  rw [←pow_add,Nat.sub_add_cancel hc] at he
  exact he

end SumsetRanges
