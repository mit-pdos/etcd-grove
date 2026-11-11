/-
`Bucket.rebalance`'s accessors (U8b, `notes/bbolt-proof-plan.md`): a bucket's object out of the
writer's state `wtxW` and back unchanged (`wtxW_bkt_acc`), and from it its `nodes` and `buckets`
fields and maps; the pure facts its loops use (`rblX` without a deficient node is independent of
the bucket named, a bucket's record kept by `rblRel`, a key list's tail).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Rebalance.RblX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- Without a deficient node, `rblX` does not depend on the bucket named. -/
theorem rblX_none (X : WX) (fl : FLPg) (d d' : Loc) (h : rblX X fl d none) : rblX X fl d' none := by
  unfold rblX at h ⊢
  simp only [ite_self] at h ⊢
  exact h

/-- A bucket's record after the steps: the same location, header and bucket cache. -/
theorem rblRel_at (X0 X : WX) (fl0 fl : FLPg) (txid : w64) (h : rblRel X0 fl0 X fl txid)
    (bl : Loc) (B : BRec) (hb : X0.t.bs !! bl = some B) :
    ∃ B', X.t.bs !! bl = some B' ∧ B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.bm = B.bm := by
  have hs := h.2.2.2.2.2.2.2.2.1 bl
  rw [hb] at hs
  obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨B', hB', h.2.2.2.2.2.2.2.2.2.1 bl B B' hb hB'⟩

omit [GooseExts] in
/-- A key past the `i`-th of the list, not the `i`-th, is past the `i+1`-th. -/
theorem mem_drop_succ {K : Type} (keys : List K) (i : Nat) (key x : K) (hk : keys[i]? = some key)
    (hne : x ≠ key) (h : x ∈ keys.drop i) : x ∈ keys.drop (i + 1) := by
  obtain ⟨hi, hki⟩ := List.getElem?_eq_some_iff.1 hk
  rw [← List.getElem_cons_drop hi, hki] at h
  rcases List.mem_cons.1 h with h | h
  · exact absurd h hne
  · exact h

end pure

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A bucket's object, out of `wtxW` and back unchanged.** -/
theorem wtxW_bkt_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢
      objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) ∗
      (objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  icases wtxHeap_bkt_obj_acc tx (DFrac.own 1) X bl B (bobjs_bkt X.t bl B hb) $$ Hh
    with ⟨Ho, Hback⟩
  iframe Ho
  iintro Ho
  ihave Hh := Hback $$ Ho
  iframe; ipureintro; exact Hr

/-- A bucket's `nodes` field, out and back. -/
theorem wtxW_nodes_fld (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢ bl.[Bucket, go!"nodes"] ↦ B.bv.nodes' ∗
      (bl.[Bucket, go!"nodes"] ↦ B.bv.nodes' -∗ wtxW K tx r m X) := by
  iintro Hw
  icases wtxW_bkt_acc K tx r m X bl B hb $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe H6
  iintro H6
  iapply Hback
  simp only [objOwn]
  iframe

/-- A bucket's `buckets` field, out and back. -/
theorem wtxW_buckets_fld (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢ bl.[Bucket, go!"buckets"] ↦ B.bv.buckets' ∗
      (bl.[Bucket, go!"buckets"] ↦ B.bv.buckets' -∗ wtxW K tx r m X) := by
  iintro Hw
  icases wtxW_bkt_acc K tx r m X bl B hb $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe H3
  iintro H3
  iapply Hback
  simp only [objOwn]
  iframe

/-- A bucket of `bs` has a node cache that is not nil (`heapOK`'s third clause). -/
theorem wtxW_bs_nodes_ne (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (hb : X.t.bs !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜B.bv.nodes' ≠ null⌝ := by
  unfold wtxW wtxCore
  iintro ⟨⟨-, -, -, -, Hh, -⟩, -, -⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  ipureintro; exact (Hok.2.2.1 bl B hb).2

/-- A bucket's node cache, out and back. -/
theorem wtxW_nm_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) (p : Loc) (nm : GMap w64 Loc) (hp : B.bv.nodes' = p)
    (hnm : B.nm = nm) :
    wtxW (GF := GF) K tx r m X ⊢ p ↦$ nm ∗ (p ↦$ nm -∗ wtxW K tx r m X) := by
  subst hp hnm
  iintro Hw
  ihave %Hnn := wtxW_bs_nodes_ne K tx r m X bl B hb $$ Hw
  icases wtxW_bkt_acc K tx r m X bl B hb $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  rw [nodesOwn_ne _ _ _ Hnn]
  iframe H8
  iintro H8
  iapply Hback
  simp only [objOwn]
  rw [nodesOwn_ne _ _ _ Hnn]
  iframe

/-- A bucket's bucket cache, out and back. -/
theorem wtxW_bm_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) (p : Loc) (bm : GMap GoString Loc) (hp : B.bv.buckets' = p)
    (hbm : B.bm = bm) :
    wtxW (GF := GF) K tx r m X ⊢ p ↦$ bm ∗ (p ↦$ bm -∗ wtxW K tx r m X) := by
  subst hp hbm
  iintro Hw
  icases wtxW_bkt_acc K tx r m X bl B hb $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe H9
  iintro H9
  iapply Hback
  simp only [objOwn]
  iframe

end heap

end bbolt
end EtcdGrove
end Perennial
