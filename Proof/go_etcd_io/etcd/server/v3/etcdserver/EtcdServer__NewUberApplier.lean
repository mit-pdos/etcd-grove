/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__NewUberApplier.lean`. Lean-first (no Rocq
counterpart); placed at the server-construction unit's stage N0 (2026-10-16), unit N1's to prove.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__NewUberApplier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.NewUberApplier

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem EtcdServer.NewUberApplier.wp_proof
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hNU : apply.NewUberApplier.spec (GF := GF) (hG := hG)) :
    EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
