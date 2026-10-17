/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ForceSnapshot.lean` (etcd#21574's
`ForceSnapshot`). Lean-first (no Rocq counterpart; 2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Backend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ForceSnapshot

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.ForceSnapshot.wp_proof
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG)) :
    EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as Hbr
  (try wp_auto)
  wp_apply hBk s $$ [Hbr] as %b ⟨Hbr, #Hc⟩
  · iframe #; iframe
  iunfold srvBackendCommits at Hc
  icases Hc with ⟨%bi, %Hbi, #HFC⟩
  subst Hbi
  (try wp_auto)
  wp_apply HFC
  (try wp_auto)
  iapply HΦ
  iexact Hbr

end proof

end EtcdGrove
end Perennial
