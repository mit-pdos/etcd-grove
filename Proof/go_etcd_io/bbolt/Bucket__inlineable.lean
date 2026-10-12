module
public import Spec.go_etcd_io.bbolt.Bucket__inlineable
public import Spec.go_etcd_io.bbolt.Bucket__maxInlineBucketSize
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Flags

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

open Classical in
theorem Bucket.inlineable.wp_proof (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hV : Inode.Value.spec (GF := GF) (hG := hG))
    (hF : Inode.Flags.spec (GF := GF) (hG := hG))
    (hMax : Bucket.maxInlineBucketSize.spec (GF := GF) (hG := hG)) :
    Bucket.inlineable.spec (GF := GF) (hG := hG) := by
  intro W bl B dt Hps Hrn
  wp_start as ⟨Hb, Hdb, Hv⟩
  isimp only [bktOwn] at Hb
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  wp_auto
  by_cases Hnull : B.bv.rootNode' = null
  · rw [decide_eq_true Hnull]
    wp_auto
    rw [decide_eq_false (not_inlineableB_nil B W.ps Hnull)]
    iapply HΦ
    unfold bktOwn; iframe
  rw [decide_eq_false Hnull]
  obtain ⟨r, Hr⟩ : ∃ r, B.ns !! B.bv.rootNode' = some r := by
    rcases Hrn with h | h
    · exact absurd h Hnull
    · exact Option.isSome_iff_exists.1 h
  simp only [inlineableB_of_root B r W.ps Hnull Hr]
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
    (show Std.get? B.ns B.bv.rootNode' = some r from Hr)).1 $$ Hns with ⟨Hnd, Hnsback⟩
  isimp only [nodeOwn] at Hnd
  icases Hnd with ⟨Hn0, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hins
  isimp only [wView] at Hv
  icases Hv with ⟨Hdata, #Hpsz, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
  wp_auto
  cases Hleaf : r.nv.isLeaf'
  · wp_auto
    rw [decide_eq_false (fun h : inlineNode r W.ps => by have h1 := h.1; rw [Hleaf] at h1; exact Bool.false_ne_true h1)]
    iapply HΦ
    ihave Hb : bktOwn W bl B $$ [Hbv Hib Hnm Hbm Hpo Hnsback Hn0 Hins Hicap Hents Hch Hchcap Hkey]
    · unfold bktOwn; iframe; iapply Hnsback; unfold nodeOwn; iframe
    iframe
    unfold wView; iframe; iframe #; ipureintro; exact Hlgv
  unfold internal.common.PageHeaderSize internal.common.LeafPageElementSize
  wp_auto
  ihave IH : (∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗ "size" ∷ size_ptr ↦ sizeFrom (W64 16) (W64 16) (r.ins.take (sint.nat j)) ∗
      "Hins" ∷ r.nv.inodes' ↦* r.ins ∗ "Hbv" ∷ bl ↦ B.bv ∗ "b" ∷ b_ptr ↦ bl ∗
      "Hdb" ∷ structFieldRef Tx go!"db" B.bv.tx' ↦{dt} W.dbl ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z r.nv.inodes'.len ∧
        ∀ k it, k < sint.nat j → r.ins[k]? = some it → it.flags' &&& W32 1 = W32 0 ∧
          uint.Z (sizeFrom (W64 16) (W64 16) (r.ins.take (k + 1))) ≤ uint.Z (maxInline W.ps)⌝ :
      IProp GF) $$ [i size Hins Hbv Hdb b]
  · iexists W64 0
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, sizeFrom_nil]
    iframe
    ipureintro
    refine ⟨by word, by word, fun k it hk _ => absurd hk (Nat.not_lt_zero _)⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z r.nv.inodes'.len := Hif
    have Hjn : sint.nat j < r.ins.length := by rw [Hsl.1]; word
    list_elem r.ins (sint.nat j) as it
    rw [ite_cond_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z r.nv.inodes'.len from ⟨Hj.1, Hlt⟩))]
    wp_apply wp_load_slice_index r.nv.inodes' (sint.Z j) r.ins _ it Hj.1 $$ [Hins] with Hins
    · iframe; ipureintro; exact Hit_lookup
    try wp_auto
    wp_apply hK $$ [$inode] as inode
    try wp_auto
    wp_apply hV $$ [$inode] as inode
    try wp_auto
    wp_apply hF $$ [$inode] as inode
    try wp_auto
    rw [← sizeFrom_take_succ r.ins (sint.nat j) it Hit_lookup]
    by_cases Hf : it.flags' &&& W32 1 = W32 0
    · rw [decide_eq_true Hf]
      try wp_auto
      wp_apply hMax bl B.bv (DFrac.own 1) W.dbl dt W.ps Hps $$ [Hbv Hdb] as ⟨Hbv, Hdb⟩
      · iframe; iframe #
      try wp_auto
      by_cases Hs : uint.Z (sizeFrom (W64 16) (W64 16) (r.ins.take (sint.nat j + 1))) ≤
          uint.Z (maxInline W.ps)
      · rw [decide_eq_false (show ¬ (uint.Z (maxInline W.ps) <
            uint.Z (sizeFrom (W64 16) (W64 16) (r.ins.take (sint.nat j + 1)))) by omega)]
        try wp_auto
        wp_for_post
        iframe
        iexists j + W64 1
        have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        rw [hj1]
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        exact inlineIns_step _ r.ins (sint.nat j) it Hit_lookup Hj.2.2 Hf Hs
      · rw [decide_eq_true (show uint.Z (maxInline W.ps) <
            uint.Z (sizeFrom (W64 16) (W64 16) (r.ins.take (sint.nat j + 1))) by omega)]
        try wp_auto
        wp_for_post
        rw [decide_eq_false (fun h : inlineNode r W.ps => Hs (h.2 _ it Hit_lookup).2)]
        iapply HΦ
        ihave Hb : bktOwn W bl B $$ [Hbv Hib Hnm Hbm Hpo Hnsback Hn0 Hins Hicap Hents Hch Hchcap Hkey]
        · unfold bktOwn; iframe; iapply Hnsback; unfold nodeOwn; iframe
        iframe
        unfold wView; iframe; iframe #; ipureintro; exact Hlgv
    · rw [decide_eq_false Hf]
      try wp_auto
      wp_for_post
      rw [decide_eq_false (fun h : inlineNode r W.ps => Hf (h.2 _ it Hit_lookup).1)]
      iapply HΦ
      ihave Hb : bktOwn W bl B $$ [Hbv Hib Hnm Hbm Hpo Hnsback Hn0 Hins Hicap Hents Hch Hchcap Hkey]
      · unfold bktOwn; iframe; iapply Hnsback; unfold nodeOwn; iframe
      iframe
      unfold wView; iframe; iframe #; ipureintro; exact Hlgv
  have Heq : sint.nat j = r.ins.length := by rw [Hsl.1]; word
  have Hin : inlineNode r W.ps := by
    refine ⟨Hleaf, fun k it hk => Hj.2.2 k it ?_ hk⟩
    have := (List.getElem?_eq_some_iff.1 hk).1
    omega
  rw [decide_eq_true Hin]
  iapply HΦ
  ihave Hb : bktOwn W bl B $$ [Hbv Hib Hnm Hbm Hpo Hnsback Hn0 Hins Hicap Hents Hch Hchcap Hkey]
  · unfold bktOwn; iframe; iapply Hnsback; unfold nodeOwn; iframe
  iframe
  unfold wView; iframe; iframe #; ipureintro; exact Hlgv

end proof

end bbolt
end EtcdGrove
end Perennial
