import CokernelPolynomiality.IntervalCokernelLinear

noncomputable section
namespace CokernelPolynomiality

def pairIntervalSource (a b c d e f i : ℕ) : intervalSpace a b i →ₗ[ℂ]
    (intervalSpace c d i × intervalSpace e f i) :=
  (intervalComponent a b c d i).prod (intervalComponent a b e f i)

def pairIntervalQuotient (b c d e f i : ℕ) :
    (intervalSpace c d i × intervalSpace e f i) →ₗ[ℂ]
      (intervalSpace (b+1) d i × intervalSpace (max c e) f i) :=
  ((intervalComponent c d (b+1) d i).comp (LinearMap.fst ℂ _ _)).prod
    (((intervalComponent c d (max c e) f i).comp (LinearMap.fst ℂ _ _))-
      ((intervalComponent e f (max c e) f i).comp (LinearMap.snd ℂ _ _)))

@[simp] theorem pairIntervalSource_fst (a b c d e f i : ℕ) (x : intervalSpace a b i) :
    (pairIntervalSource a b c d e f i x).1.val=if intervalActive c d i then x.val else 0 := by
  exact intervalComponent_val a b c d i x

@[simp] theorem pairIntervalSource_snd (a b c d e f i : ℕ) (x : intervalSpace a b i) :
    (pairIntervalSource a b c d e f i x).2.val=if intervalActive e f i then x.val else 0 := by
  exact intervalComponent_val a b e f i x

@[simp] theorem pairIntervalQuotient_fst (b c d e f i : ℕ)
    (x : intervalSpace c d i × intervalSpace e f i) :
    (pairIntervalQuotient b c d e f i x).1.val=
      if intervalActive (b+1) d i then x.1.val else 0 := by
  exact intervalComponent_val c d (b+1) d i x.1

@[simp] theorem pairIntervalQuotient_snd (b c d e f i : ℕ)
    (x : intervalSpace c d i × intervalSpace e f i) :
    (pairIntervalQuotient b c d e f i x).2.val=
      if intervalActive (max c e) f i then x.1.val-x.2.val else 0 := by
  change (intervalComponent c d (max c e) f i x.1).val-
    (intervalComponent e f (max c e) f i x.2).val=_
  rw [intervalComponent_val,intervalComponent_val]
  split <;> simp_all

theorem pairIntervalQuotient_surjective (b c d e f i : ℕ)
    (hcb : c ≤ b) (heb : e ≤ b) (hbd : b ≤ d) (hdf : d ≤ f) :
    Function.Surjective (pairIntervalQuotient b c d e f i) := by
  rintro ⟨u,v⟩
  by_cases hib : i ≤ b
  · have ht : ¬intervalActive (b+1) d i := by unfold intervalActive; omega
    have hu := intervalSpace_val_zero ht u
    by_cases hm : intervalActive (max c e) f i
    · have hc : intervalActive c d i := by unfold intervalActive at *; omega
      refine ⟨(⟨v.val,by simp [intervalSpace,hc]⟩,0),?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · simp [pairIntervalQuotient_fst,ht,hu]
      · simp [pairIntervalQuotient_snd,hm]
    · have hv := intervalSpace_val_zero hm v
      refine ⟨0,?_⟩
      rw [map_zero]
      apply Prod.ext <;> apply Subtype.ext <;> simp [hu,hv]
  · by_cases hid : i ≤ d
    · have hc : intervalActive c d i := by unfold intervalActive; omega
      have he : intervalActive e f i := by unfold intervalActive; omega
      have ht : intervalActive (b+1) d i := by unfold intervalActive; omega
      have hm : intervalActive (max c e) f i := by unfold intervalActive; omega
      refine ⟨(⟨u.val,by simp [intervalSpace,hc]⟩,⟨u.val-v.val,by simp [intervalSpace,he]⟩),?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · simp [pairIntervalQuotient_fst,ht]
      · simp [pairIntervalQuotient_snd,hm]
    · have ht : ¬intervalActive (b+1) d i := by unfold intervalActive; omega
      have hu := intervalSpace_val_zero ht u
      by_cases hif : i ≤ f
      · have he : intervalActive e f i := by unfold intervalActive; omega
        have hm : intervalActive (max c e) f i := by unfold intervalActive; omega
        refine ⟨(0,⟨-v.val,by simp [intervalSpace,he]⟩),?_⟩
        apply Prod.ext <;> apply Subtype.ext
        · simp [pairIntervalQuotient_fst,ht,hu]
        · simp [pairIntervalQuotient_snd,hm]
      · have hm : ¬intervalActive (max c e) f i := by unfold intervalActive; omega
        have hv := intervalSpace_val_zero hm v
        refine ⟨0,?_⟩
        rw [map_zero]
        apply Prod.ext <;> apply Subtype.ext <;> simp [hu,hv]

theorem pairIntervalQuotient_exact (a b c d e f i : ℕ)
    (hac : a ≤ c) (hae : a ≤ e) (hcb : c ≤ b) (_heb : e ≤ b)
    (hbd : b ≤ d) (_hdf : d ≤ f) :
    Function.Exact (pairIntervalSource a b c d e f i) (pairIntervalQuotient b c d e f i) := by
  intro y
  constructor
  · intro hy
    have h1 := congrArg (fun z => z.1.val) hy
    have h2 := congrArg (fun z => z.2.val) hy
    simp only [pairIntervalQuotient_fst,Prod.fst_zero,ZeroMemClass.coe_zero] at h1
    simp only [pairIntervalQuotient_snd,Prod.snd_zero,ZeroMemClass.coe_zero] at h2
    by_cases hib : i ≤ b
    · by_cases hc : intervalActive c d i
      · have hs : intervalActive a b i := ⟨hac.trans hc.1,hib⟩
        refine ⟨⟨y.1.val,by simp [intervalSpace,hs]⟩,?_⟩
        apply Prod.ext <;> apply Subtype.ext
        · simp [pairIntervalSource_fst,hc]
        · by_cases he : intervalActive e f i
          · have hm : intervalActive (max c e) f i := ⟨max_le hc.1 he.1,he.2⟩
            rw [ite_eq_left hm] at h2
            simpa [pairIntervalSource_snd,he] using sub_eq_zero.mp h2
          · simp [pairIntervalSource_snd,he,intervalSpace_val_zero he y.2]
      · by_cases he : intervalActive e f i
        · have hs : intervalActive a b i := ⟨hae.trans he.1,hib⟩
          refine ⟨⟨y.2.val,by simp [intervalSpace,hs]⟩,?_⟩
          apply Prod.ext <;> apply Subtype.ext
          · simp [pairIntervalSource_fst,hc,intervalSpace_val_zero hc y.1]
          · simp [pairIntervalSource_snd,he]
        · refine ⟨0,?_⟩
          rw [map_zero]
          apply Prod.ext <;> apply Subtype.ext
          · exact (intervalSpace_val_zero hc y.1).symm
          · exact (intervalSpace_val_zero he y.2).symm
    · have hy1 : y.1.val=0 := by
        by_cases hc : intervalActive c d i
        · have ht : intervalActive (b+1) d i := ⟨by omega,hc.2⟩
          rwa [ite_eq_left ht] at h1
        · exact intervalSpace_val_zero hc y.1
      have hy2 : y.2.val=0 := by
        by_cases he : intervalActive e f i
        · have hm : intervalActive (max c e) f i := by unfold intervalActive at *; omega
          rw [ite_eq_left hm,hy1,zero_sub,neg_eq_zero] at h2
          exact h2
        · exact intervalSpace_val_zero he y.2
      refine ⟨0,?_⟩
      rw [map_zero]
      apply Prod.ext <;> apply Subtype.ext
      · exact hy1.symm
      · exact hy2.symm
  · rintro ⟨x,rfl⟩
    by_cases hib : i ≤ b
    · have ht : ¬intervalActive (b+1) d i := by unfold intervalActive; omega
      apply Prod.ext <;> apply Subtype.ext
      · simp [pairIntervalQuotient_fst,ht]
      · by_cases hm : intervalActive (max c e) f i
        · have hc : intervalActive c d i := by unfold intervalActive at *; omega
          have he : intervalActive e f i := by unfold intervalActive at *; omega
          simp [pairIntervalQuotient_snd,hm,pairIntervalSource_fst,pairIntervalSource_snd,hc,he]
        · simp [pairIntervalQuotient_snd,hm]
    · have hs : ¬intervalActive a b i := by unfold intervalActive; omega
      have hx : x=0 := Subtype.ext (intervalSpace_val_zero hs x)
      rw [hx,map_zero,map_zero]

end CokernelPolynomiality
