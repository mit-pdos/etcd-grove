/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txWriteBuffer__putInternal.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__putInternal
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBucketBuffer
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__add
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WBufLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.txWriteBuffer.putInternal.wp_proof
    (hNew : backend.newBucketBuffer.spec (GF := GF) (hG := hG))
    (hAdd : backend.bucketBuffer.add.spec (GF := GF) (hG := hG)) :
    backend.txWriteBuffer.putInternal.spec (GF := GF) (hG := hG) := by
  intro txw W b bi k v kb vb Hlen
  wp_start as ⟨HW, #Hb, #Hk, #Hv⟩
  unfold ownWB
  icases HW with ⟨%m, %s, Hbk, Hseq, Hbks, Hs⟩
  icases ownBks_open m W.bks $$ Hbks with ⟨%M, Hm, Hbks⟩
  ihave %Hdom := bksOwn_dom M W.bks $$ Hbks
  unfold isBucket
  icases Hb with ⟨%bo, %Hbo, #HID, #-, #-⟩
  subst Hbo
  wp_auto
  wp_apply HID
  wp_apply wp_map_lookup2 $$ Hm as Hm
  cases hM : M !! bi.id with
  | none =>
    have hB := bksOwn_none Hdom hM
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply hNew as %bb Hbb
    wp_apply HID
    wp_apply wp_mapInsert $$ Hm as Hm
    wp_apply (hAdd bb [] k v kb vb (by simp [bufBound])) $$ [$Hbb $Hk $Hv] as Hbb
    iapply HΦ
    iexists m, s
    iframe Hbk Hseq Hs
    iapply ownBks_close
    iframe Hm
    unfold wbAdd bkOf
    rw [hB, Option.getD_none]
    iapply bksOwn_insert hM $$ [$Hbks $Hbb]
  | some bb =>
    obtain ⟨es, hB⟩ := bksOwn_some Hdom hM
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    wp_auto
    icases bksOwn_acc hM hB $$ Hbks with ⟨Hbb, Hback⟩
    have hl : es.length < bufBound := by unfold bkOf at Hlen; rw [hB] at Hlen; exact Hlen
    wp_apply (hAdd bb es k v kb vb hl) $$ [$Hbb $Hk $Hv] as Hbb
    iapply HΦ
    iexists m, s
    iframe Hbk Hseq Hs
    iapply ownBks_close
    iframe Hm
    unfold wbAdd bkOf
    rw [hB, Option.getD_some]
    iapply Hback $$ Hbb

end proof

end EtcdGrove
end Perennial
