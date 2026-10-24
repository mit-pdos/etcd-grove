/-
The trust boundary: `(*rafthttp.Transport).RemoveAllPeers()` (names-only). Lean-first (no Rocq
counterpart); D22 receiver epochs, S8c (2026-10-24), an axiom: why the statement is true of the Go
code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__RemoveAllPeers

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

axiom rafthttp.Transport.RemoveAllPeers.wp_proof : rafthttp.Transport.RemoveAllPeers.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
