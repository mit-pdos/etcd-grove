/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/closeNotifier__closeNotify.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.closeNotifier__closeNotify

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
theorem rafthttp.closeNotifier.closeNotify.wp_proof :
    rafthttp.closeNotifier.closeNotify.spec (GF := GF) (hG := hG) := by
  intro n γ P
  wp_start as #Hr
  iunfold cnRecv at Hr
  icases Hr with ⟨%dc, %γc, #Hdc, #Hdb⟩
  (try wp_auto)
  iapply HΦ
  iexists γc; iexact Hdb

end proof

end EtcdGrove
end Perennial
