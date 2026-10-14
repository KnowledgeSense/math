import R34.KernelRun
import R34.Transfer

namespace R34

open Kernel

def gapSite (b : Bool) : Kernel := if b then B else 1
def gapFactor (b : Bool) : Kernel := gapSite b * C
def freeFactor (b : Bool) : Kernel := C * gapSite b

def gapKernel (gap : List Bool) : Kernel := C * (gap.map gapFactor).prod
def gapFreeKernel (gap : List Bool) : Kernel := (gap.map freeFactor).prod
def gapFree (gap : List Bool) : ℝ × ℝ := (gapFreeKernel gap).act (1,1)

theorem kernel_entry_prod (ks : List Kernel) : ks.prod.entry = (ks.map Kernel.entry).prod := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp only [List.prod_cons, List.map_cons, Kernel.entry_mul, ih]

theorem gapKernel_append (gap : List Bool) (b : Bool) :
    gapKernel (gap ++ [b]) = gapKernel gap * gapFactor b := by
  simp [gapKernel, List.map_append, List.prod_append, Kernel.mul_assoc]

theorem gapKernel_contracted (gap : List Bool) :
    Contracted (gap.count true) (gapKernel gap) := by
  induction gap using List.reverseRecOn with
  | nil => simpa [gapKernel] using Contracted.base
  | append_singleton gap b ih =>
    rw [gapKernel_append]
    cases b
    · simpa [gapFactor, gapSite] using ih.right_neutral
    · simpa [gapFactor, gapSite, Kernel.mul_assoc] using ih.right_pair

theorem gapFree_free (gap : List Bool) : Free (gapFree gap) := by
  induction gap with
  | nil => simpa [gapFree, gapFreeKernel, Kernel.act, Kernel.w,
      Kernel.identity, Kernel.instMonoidKernel] using Free.one
  | cons b gap ih =>
    simp only [gapFree, gapFreeKernel, List.map_cons, List.prod_cons, Kernel.act_mul]
    change Free ((freeFactor b).act (gapFree gap))
    cases b
    · simpa [freeFactor, gapSite] using Free.neutral ih
    · simpa [freeFactor, gapSite] using Free.pair ih

theorem gapFactor_transpose (b : Bool) : (gapFactor b).transpose = freeFactor b := by
  cases b <;> simp [gapFactor, freeFactor, gapSite, Kernel.transpose_mul]

theorem kernel_transpose_prod (ks : List Kernel) :
    ks.prod.transpose = ((ks.reverse).map Kernel.transpose).prod := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.prod_cons, Kernel.transpose_mul, ih, List.reverse_cons,
      List.map_append, List.map_singleton, List.prod_append]
    simp

theorem leading_gap_transpose (gap : List Bool) :
    (gap.map gapFactor).prod.transpose = gapFreeKernel gap.reverse := by
  rw [kernel_transpose_prod]
  simp [gapFreeKernel, List.map_reverse, List.map_map, Function.comp_def, gapFactor_transpose]

theorem internal_gap_identity (gap : List Bool) :
    gapFreeKernel gap * C = gapKernel gap := by
  induction gap with
  | nil => simp [gapFreeKernel,gapKernel]
  | cons b gap ih =>
    simp only [gapFreeKernel, gapKernel, List.map_cons, List.prod_cons] at *
    rw [Kernel.mul_assoc, ih]
    simp [freeFactor, gapFactor, Kernel.mul_assoc]

theorem gapKernel_matrix (gap : List Bool) :
    (gapKernel gap).entry = C.entry * ((gap.map fun b => (gapSite b).entry * C.entry)).prod := by
  rw [gapKernel, Kernel.entry_mul, kernel_entry_prod]
  simp [List.map_map,Function.comp_def,gapFactor,Kernel.entry_mul]

theorem gapFree_matrix (gap : List Bool) :
    (gapFreeKernel gap).entry = ((gap.map fun b => C.entry * (gapSite b).entry)).prod := by
  rw [gapFreeKernel,kernel_entry_prod]
  simp [List.map_map,Function.comp_def,freeFactor,Kernel.entry_mul]

/-- The free scalar for a word containing only neutral and contracted sites. -/
def neutralScalar : List Bool → ℝ
  | [] => 1
  | b :: gap => Kernel.pairDot (1,1) ((gapSite b).act (gapFree gap))

theorem neutralScalar_positive (word : List Bool) : 0 < neutralScalar word := by
  cases word with
  | nil => norm_num [neutralScalar]
  | cons b gap =>
    have hf := gapFree_free gap
    cases b
    · have hb := hf.bounds
      simp [neutralScalar,gapSite,Kernel.pairDot,Kernel.act,Kernel.w]
      linarith [hb.1.1,hb.2]
    · have hp := scalar_positive 0 hf
      simpa [neutralScalar,gapSite,cVector,Kernel.pairDot,Kernel.act,B,Kernel.w] using hp

theorem gap_left_row (gap : List Bool) (i : Fin 3) :
    (gapKernel gap).entry 0 i = Kernel.embed (gapFree gap.reverse) i := by
  have he : gapFree gap.reverse = ((gap.map gapFactor).prod).transpose.act (1,1) := by
    rw [gapFree, ← leading_gap_transpose]
  rw [he]
  rw [Kernel.entry_eq_ite, Kernel.embed_eq_ite]
  fin_cases i <;> simp [gapKernel,Kernel.act,Kernel.transpose,Kernel.w,C]

theorem gap_right_row_sum (gap : List Bool) (i : Fin 3) :
    (∑ j, (gapFreeKernel gap).entry i j) = Kernel.embed (gapFree gap) i := by
  simp only [Kernel.entry_eq_ite, Kernel.embed_eq_ite]
  fin_cases i
  · simp [gapFree,Kernel.act,Kernel.w,Fin.sum_univ_succ]
  · simp [gapFree,Kernel.act,Kernel.w,Fin.sum_univ_succ]
  · simp [gapFree,Kernel.act,Kernel.w,Fin.sum_univ_succ]
    ring

namespace GapGrouping

variable {M : Type*} [Monoid M]

def chain (c : M) (sites : List M) : M := (sites.map (fun x => c * x)).prod

def flatten (leading : List M) (blocks : List (M × List M)) : List M :=
  leading ++ blocks.flatMap (fun b => b.1 :: b.2)

def core (c : M) : List (M × List M) → M
  | [] => 1
  | [b] => b.1
  | b :: b' :: bs => b.1 * (chain c b.2 * c) * core c (b' :: bs)

def trailing : List (M × List M) → List M
  | [] => []
  | [b] => b.2
  | _ :: b' :: bs => trailing (b' :: bs)

theorem rotated_product (c : M) (sites : List M) :
    chain c sites * c = c * (sites.map (fun x => x * c)).prod := by
  induction sites with
  | nil => simp [chain]
  | cons x xs ih =>
    simp only [chain, List.map_cons, List.prod_cons] at *
    rw [_root_.mul_assoc, ih]
    simp only [_root_.mul_assoc]

theorem flattened_chain (c : M) (leading : List M) (blocks : List (M × List M)) :
    chain c (flatten leading blocks) = chain c leading *
      (blocks.map (fun b => c * b.1 * chain c b.2)).prod := by
  simp only [flatten, chain, List.map_append, List.prod_append]
  congr 1
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, ih]

theorem block_product (c : M) (blocks : List (M × List M)) (hne : blocks ≠ []) :
    (blocks.map (fun b => c * b.1 * chain c b.2)).prod =
      c * core c blocks * chain c (trailing blocks) := by
  induction blocks with
  | nil => contradiction
  | cons b bs ih =>
    cases bs with
    | nil => simp [core,trailing]
    | cons b' bs =>
      rw [List.map_cons,List.prod_cons,ih (by simp)]
      simp only [core,trailing,_root_.mul_assoc]

/-- Exact grouping of every nonempty charged list with arbitrary gaps. -/
theorem grouping (c : M) (leading : List M) (blocks : List (M × List M))
    (hne : blocks ≠ []) :
    chain c (flatten leading blocks) =
      (chain c leading * c) * core c blocks * chain c (trailing blocks) := by
  rw [flattened_chain,block_product c blocks hne]
  simp only [_root_.mul_assoc]

end GapGrouping

noncomputable section

def liftKernel (K : Kernel) : Transfer.Mat := fun i j => MvPolynomial.C (K.entry i j)

theorem liftKernel_mul (K L : Kernel) : liftKernel (K * L) = liftKernel K * liftKernel L := by
  apply Matrix.ext
  intro i j
  change MvPolynomial.C ((K * L).entry i j) =
    (liftKernel K * liftKernel L) i j
  rw [Kernel.entry_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact map_mul _ _ _

@[simp] theorem liftKernel_one : liftKernel (1 : Kernel) = 1 := by
  apply Matrix.ext
  intro i j
  simp [liftKernel, Kernel.entry_one, Matrix.one_apply]

@[simp] theorem liftKernel_C : liftKernel C = Transfer.compatibility := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | change MvPolynomial.C (1 : ℝ) = (1 : Transfer.Poly)
    | change MvPolynomial.C (0 : ℝ) = (0 : Transfer.Poly)
  all_goals norm_num [map_ofNat]

@[simp] theorem liftKernel_B : liftKernel B = Transfer.contractedPair := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | change MvPolynomial.C (6 : ℝ) = (6 : Transfer.Poly)
    | change MvPolynomial.C (0 : ℝ) = (0 : Transfer.Poly)
    | change MvPolynomial.C (-1 : ℝ) = (-1 : Transfer.Poly)
  all_goals norm_num [map_ofNat]

theorem liftKernel_prod (ks : List Kernel) :
    liftKernel ks.prod = (ks.map liftKernel).prod := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp only [List.prod_cons,List.map_cons,liftKernel_mul,ih]

def gapMatrices (gap : List Bool) : List Transfer.Mat := gap.map (fun b => liftKernel (gapSite b))

theorem chain_gapMatrices (gap : List Bool) :
    GapGrouping.chain Transfer.compatibility (gapMatrices gap) = liftKernel (gapFreeKernel gap) := by
  unfold GapGrouping.chain gapMatrices gapFreeKernel
  rw [liftKernel_prod]
  simp only [List.map_map,Function.comp_def,freeFactor,liftKernel_mul,liftKernel_C]

theorem internal_gap_poly (gap : List Bool) :
    GapGrouping.chain Transfer.compatibility (gapMatrices gap) * Transfer.compatibility =
      liftKernel (gapKernel gap) := by
  rw [chain_gapMatrices, ← liftKernel_C, ← liftKernel_mul,internal_gap_identity]

def mappedBlocks (blocks : List (Transfer.Mat × List Bool)) :
    List (Transfer.Mat × List Transfer.Mat) := blocks.map (fun b => (b.1,gapMatrices b.2))

def collapsedSites (leading : List Bool) (blocks : List (Transfer.Mat × List Bool)) :
    List Transfer.Mat := GapGrouping.flatten (gapMatrices leading) (mappedBlocks blocks)

def lastGap : List (Transfer.Mat × List Bool) → List Bool
  | [] => []
  | [b] => b.2
  | _ :: b' :: bs => lastGap (b' :: bs)

def collapsedCore : List (Transfer.Mat × List Bool) → Transfer.Mat
  | [] => 1
  | [b] => b.1
  | b :: b' :: bs => b.1 * liftKernel (gapKernel b.2) * collapsedCore (b' :: bs)

def collapsedLinks : List (Transfer.Mat × List Bool) → List (Kernel × Transfer.Mat)
  | [] => []
  | [_] => []
  | b :: b' :: bs => (gapKernel b.2,b'.1) :: collapsedLinks (b' :: bs)

theorem collapsedCore_links (b : Transfer.Mat × List Bool)
    (bs : List (Transfer.Mat × List Bool)) :
    collapsedCore (b :: bs) = b.1 *
      ((collapsedLinks (b :: bs)).map (fun e => liftKernel e.1 * e.2)).prod := by
  induction bs generalizing b with
  | nil => simp [collapsedCore,collapsedLinks]
  | cons b' bs ih =>
    simp only [collapsedCore,collapsedLinks,List.map_cons,List.prod_cons]
    rw [ih]
    simp only [_root_.mul_assoc]

theorem collapsedLinks_contracted (blocks : List (Transfer.Mat × List Bool))
    (edge : Kernel × Transfer.Mat) (he : edge ∈ collapsedLinks blocks) :
    ∃ r, Contracted r edge.1 := by
  induction blocks with
  | nil => simp [collapsedLinks] at he
  | cons b bs ih =>
    cases bs with
    | nil => simp [collapsedLinks] at he
    | cons b' bs =>
      simp only [collapsedLinks,List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨b.2.count true,gapKernel_contracted b.2⟩
      · exact ih he

theorem mappedBlocks_core (blocks : List (Transfer.Mat × List Bool)) :
    GapGrouping.core Transfer.compatibility (mappedBlocks blocks) = collapsedCore blocks := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons b' bs =>
      simp only [mappedBlocks,List.map_cons,GapGrouping.core,collapsedCore] at *
      rw [internal_gap_poly,ih]

theorem mappedBlocks_trailing (blocks : List (Transfer.Mat × List Bool)) :
    GapGrouping.trailing (mappedBlocks blocks) = gapMatrices (lastGap blocks) := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons b' bs => exact ih

/-- The grouped matrices are equal to the original transfer product. -/
theorem collapsed_chain (leading : List Bool) (blocks : List (Transfer.Mat × List Bool))
    (hne : blocks ≠ []) :
    Transfer.chain (collapsedSites leading blocks) =
      liftKernel (gapKernel leading) * collapsedCore blocks *
        liftKernel (gapFreeKernel (lastGap blocks)) := by
  change GapGrouping.chain Transfer.compatibility (collapsedSites leading blocks) = _
  rw [collapsedSites,GapGrouping.grouping]
  · rw [internal_gap_poly,mappedBlocks_core,mappedBlocks_trailing,chain_gapMatrices]
  · simpa [mappedBlocks] using hne

theorem collapsed_value (leading : List Bool) (blocks : List (Transfer.Mat × List Bool))
    (hne : blocks ≠ []) :
    Transfer.value (collapsedSites leading blocks) =
      ∑ i, ∑ j, MvPolynomial.C (Kernel.embed (gapFree leading.reverse) i) *
        collapsedCore blocks i j * MvPolynomial.C (Kernel.embed (gapFree (lastGap blocks)) j) := by
  rw [Transfer.value,collapsed_chain leading blocks hne]
  have hL (i : Fin 3) : liftKernel (gapKernel leading) 0 i =
      MvPolynomial.C (Kernel.embed (gapFree leading.reverse) i) := by
    simp only [liftKernel,gap_left_row]
  have hR (i : Fin 3) : (liftKernel (gapFreeKernel (lastGap blocks))).mulVec
      (fun _ => (1 : Transfer.Poly)) i =
      MvPolynomial.C (Kernel.embed (gapFree (lastGap blocks)) i) := by
    simp only [Matrix.mulVec,dotProduct,liftKernel,mul_one]
    rw [← map_sum,gap_right_row_sum]
  calc
    _ = ((liftKernel (gapKernel leading) * collapsedCore blocks *
        liftKernel (gapFreeKernel (lastGap blocks))).mulVec
          (fun _ => (1 : Transfer.Poly))) 0 := by
      simp only [Matrix.mulVec,dotProduct,mul_one]
    _ = _ := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change (∑ i, liftKernel (gapKernel leading) 0 i *
        (∑ j, collapsedCore blocks i j *
          (liftKernel (gapFreeKernel (lastGap blocks))).mulVec
            (fun _ => (1 : Transfer.Poly)) j)) = _
      simp only [hR,hL,Finset.mul_sum,_root_.mul_assoc]

theorem neutralScalar_row (b : Bool) (gap : List Bool) :
    (∑ i, (gapFreeKernel (b :: gap)).entry 0 i) = neutralScalar (b :: gap) := by
  rw [gap_right_row_sum]
  simp only [gapFree,gapFreeKernel,List.map_cons,List.prod_cons,Kernel.act_mul,
    freeFactor,C_act,Kernel.embed_eq_ite,neutralScalar,Kernel.pairDot]
  simp

theorem neutral_value_eq (word : List Bool) :
    Transfer.value (gapMatrices word) = MvPolynomial.C (neutralScalar word) := by
  cases word with
  | nil => simp [gapMatrices,neutralScalar]
  | cons b gap =>
    have hc : Transfer.chain (gapMatrices (b :: gap)) = liftKernel (gapFreeKernel (b :: gap)) :=
      chain_gapMatrices (b :: gap)
    rw [Transfer.value,hc]
    simp only [liftKernel]
    rw [← map_sum,neutralScalar_row]

theorem neutral_value_positive_constant (word : List Bool) :
    ∃ r : ℝ, 0 < r ∧ Transfer.value (gapMatrices word) = MvPolynomial.C r :=
  ⟨neutralScalar word,neutralScalar_positive word,neutral_value_eq word⟩

end

end R34

