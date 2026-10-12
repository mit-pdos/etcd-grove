/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txReadBuffer__Range.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Range
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BksLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ModelLemmas

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

theorem backend.txReadBuffer.Range.wp_proof
    (hRange : backend.bucketBuffer.Range.spec (GF := GF) (hG := hG)) :
    backend.txReadBuffer.Range.spec (GF := GF) (hG := hG) := by
  intro txr dq m P R b bi key endKey kb eb dk de limit hwf
  wp_start as ⟨Hrb, #Hb, Hkey, Hend⟩
  unfold isBucket
  icases Hb with ⟨%bo, %hb, #Hid, -, -⟩
  subst hb
  unfold rbAt bksAt
  icases Hrb with ⟨Htb, Hver, Hm, Hbbs⟩
  wp_auto
  wp_apply Hid
  icases txBuffer_buckets_acc _ _ _ $$ Htb with ⟨Hbk, Htb⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ Hm as Hm
  ihave Htb := Htb $$ Hbk
  cases hP : P !! bi.id with
  | none =>
    ihave %hB := bbs_lookup_none P R.bks dq bi.id hP $$ Hbbs
    simp only [Option.map_none, Option.getD_none]
    wp_auto
    rw [show bkOf R.bks bi.id = [] by simp [bkOf, hB], bbRange_nil]
    iapply HΦ
    iframe
    iapply kvsOut_nil
  | some x =>
    icases bbs_lookup_acc P R.bks dq bi.id x hP $$ Hbbs with ⟨%es, %hB, Hbb, Hbbs⟩
    ihave %Hnn := bbAt_not_null _ _ _ _ $$ Hbb
    simp only [Option.map_some, Option.getD_some]
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply hRange _ _ _ _ _ _ _ _ _ _ _ (hwf _ _ hB) $$ [$Hbb $Hkey $Hend]
      as %keys %vals ⟨Hbb, Hkey, Hend, Hout⟩
    rw [show bkOf R.bks bi.id = es by simp [bkOf, hB]]
    iapply HΦ
    ihave Hbbs := Hbbs $$ Hbb
    iframe

end proof

end EtcdGrove
end Perennial
