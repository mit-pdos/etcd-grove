/-
The trust boundary: `(*rafthttp.Transport).AddPeer(id, urls)` (names-only). Lean-first (no Rocq counterpart); the
server-construction unit, an axiom since unit N4 (2026-10-17, D14d/D14e): why the statement is
true of the Go code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddPeer

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

axiom rafthttp.Transport.AddPeer.wp_proof : rafthttp.Transport.AddPeer.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
