/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__GoAttach.lean`. Lean-first (no
Rocq counterpart); see `InvGoAttach.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.GoAttach.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    EtcdServer.GoAttach.spec (GF := GF) (hG := hG) := by
  sorry -- DRAFT revoke-open (GoAttach by levels, `goAttachInv` with pending adds)

end proof

end EtcdGrove
end Perennial
