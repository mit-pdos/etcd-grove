/-
The trust boundary: `(*EtcdServer).RaftHandler()` (names-only). Lean-first (no Rocq counterpart);
D21 stage M5 (2026-10-19, the user's (A)): why the statement is true of the Go code is in its spec's
docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom EtcdServer.RaftHandler.wp_proof : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
