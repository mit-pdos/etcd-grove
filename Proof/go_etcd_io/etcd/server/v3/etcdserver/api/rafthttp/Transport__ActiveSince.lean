/-
The trust boundary: `(*rafthttp.Transport).ActiveSince(…)` (rafthttp stage 6d, 2026-10-24). Lean-first; why
the statement is true of the Go code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__ActiveSince

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

axiom rafthttp.Transport.ActiveSince.wp_proof : rafthttp.Transport.ActiveSince.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
