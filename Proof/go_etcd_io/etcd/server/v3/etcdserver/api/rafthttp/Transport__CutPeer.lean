/-
The trust boundary: `(*rafthttp.Transport).CutPeer(id)` (names-only). Lean-first (no Rocq counterpart);
the partition plan's stage S1 (2026-10-20): why the statement is true of the Go code is in its
spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__CutPeer

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

axiom rafthttp.Transport.CutPeer.wp_proof : rafthttp.Transport.CutPeer.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
