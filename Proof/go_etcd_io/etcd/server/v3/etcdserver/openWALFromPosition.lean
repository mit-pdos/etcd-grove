/-
The trust boundary: `openWALFromPosition` (etcd-io/etcd#19693's pr-verify, 2026-10-17). Its body
is `wal.Open` and `WAL.ReadAll` (the `wal` package is translated names-only), `wal.Repair` and
`zap.Logger.Fatal`; the spec states what `ReadAll` returns when it succeeds
(`InvBootWALFromBackend.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.openWALFromPosition

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom openWALFromPosition.wp_proof : openWALFromPosition.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
