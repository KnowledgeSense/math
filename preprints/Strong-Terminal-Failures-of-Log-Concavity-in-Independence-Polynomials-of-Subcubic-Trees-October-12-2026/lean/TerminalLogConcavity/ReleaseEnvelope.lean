import TerminalLogConcavity.PathEnvelope
import TerminalLogConcavity.ReleaseLower

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

noncomputable def releaseEnvelopeWeights (q t : ℕ) : List ℕ :=
  List.replicate (q-1) 1 ++ (List.range q).flatMap (fun i => chainEnvelopeWeights q t (i+1))

@[simp] theorem linearProduct_replicate (n d : ℕ) :
    linearProduct (List.replicate n d) = (1+C d*X)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,linearProduct,ih,pow_succ,mul_comm]

theorem release_common_envelope (q t : ℕ) :
    CoeffLE (pathStateSum (releaseDecorations q t)).1
      (C (2^(q-1)) * linearProduct (releaseEnvelopeWeights q t) *
        ∏ i ∈ Finset.range q, upperChain q t (i+1)) := by
  have hbridge := (pathStateSum_bridge_product_bounds
    ((List.range q).map (fun i => chainDecorations q t (i+1))) Block.leaf.decoration
    (by simp only [Block.decoration_A,Block.A_leaf]; exact CoeffLE.le_add_right _ _)).2
  simp only [Block.decoration_A,Block.decoration_B,Block.A_leaf,Block.B_leaf,List.map_map,
    Function.comp_def,prod_map_range_poly,List.length_map,List.length_range] at hbridge
  have hb : CoeffLE ((1+X)+1 : ℕ[X]) (C 2*(1+X)) := by
    convert CoeffLE.le_add_right ((1+X)+1 : ℕ[X]) X using 1 ; norm_num ; ring
  have hc : CoeffLE (∏ i ∈ Finset.range q, (pathStateSum (chainDecorations q t (i+1))).1)
      (∏ i ∈ Finset.range q, linearProduct (chainEnvelopeWeights q t (i+1))*upperChain q t (i+1)) :=
    CoeffLE.prod (fun i _ => chain_common_envelope q t (i+1))
  apply hbridge.trans
  have h := (hb.pow (q-1)).mul hc
  rw [Finset.prod_mul_distrib,mul_pow,← C_pow] at h
  have he : linearProduct (releaseEnvelopeWeights q t) =
      (1+X)^(q-1) * ∏ i ∈ Finset.range q, linearProduct (chainEnvelopeWeights q t (i+1)) := by
    rw [releaseEnvelopeWeights,linearProduct_append,linearProduct_replicate,linearProduct_flatMap,prod_map_range_poly]
    simp
  rw [he]
  convert h using 1 ; ring

end TerminalLogConcavity
