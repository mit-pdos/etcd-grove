/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stm__Del.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Del
public import Spec.go_etcd_io.etcd.client.v3.OpDelete
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMMaps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stm.Del.wp_proof (hDel : EtcdGrove.OpDelete.spec (GF := GF) (hG := hG)) :
    stm.Del.spec (GF := GF) (hG := hG) := by
  intro b pfx writes k
  wp_start as ⟨Hws, %Hpk⟩
  unfold stmWsetOwn
  icases Hws with ⟨%m, %wsMap, Hf, Hm, #Hat⟩
  wp_auto
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hnil := optsAt_nil (GF := GF)
  wp_apply hDel k slice.nil [] $$ [$Hcv $Hnil] as %op #Hop
  · ipureintro; exact deleteOp_not_panics k
  (try wp_auto)
  wp_apply wp_mapInsert $$ Hm as Hm
  iapply HΦ
  iexists m, _
  iframe Hf Hm
  iapply writesAt_insert
  iframe Hat
  unfold writeAt
  isplitr
  · ipureintro; exact ⟨rfl, Hpk⟩
  iexists _
  iframe Hop
  ipureintro; exact stm_deleteOp_txnOpOf k

end proof

end concurrency
end EtcdGrove
end Perennial
