/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/newCloseNotifier.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newCloseNotifier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.newCloseNotifier.wp_proof : rafthttp.newCloseNotifier.spec (GF := GF) (hG := hG) := by
  intro P
  wp_start as -
  imod http.reqTicket_alloc with ⟨%γ, Htok⟩
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %dc %γdn ⟨#Hdcc, %-, Hdco⟩
  imod alloc_broadcast_chan (E := ⊤) (cnQ γ P) γdn dc $$ Hdcc Hdco with Hdb
  icases ownBroadcastChan_open _ _ _ _ $$ Hdb with ⟨%γdch, #Hdint, Hdown⟩
  ihave #Hdunk : ownBroadcastChan dc γdn (cnQ γ P) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γdch
    iframe #
  ihave Hdb := ownBroadcastChan_close dc γdn (cnQ γ P) .Pending γdch $$ [$Hdint $Hdown]
  (try wp_auto)
  wp_alloc n as Hn
  iStructNamed Hn
  irename done => Hdf
  ipersist Hdf
  (try wp_auto)
  iapply HΦ
  iexists γ
  iframe Htok
  isplitr
  · iunfold cnRecv; iexists dc, γdn; iframe #
  iunfold cnClose; iexists dc, γdn; iframe; iframe #

end proof

end EtcdGrove
end Perennial
