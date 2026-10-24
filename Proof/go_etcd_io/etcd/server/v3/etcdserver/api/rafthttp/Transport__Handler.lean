/-
`(*rafthttp.Transport).Handler()` (rafthttp stage 6d, 2026-10-24): proved over its callees'
specs (`rafthttp.Transport.Handler_full`, `TransportFull.lean`); an axiom until rafthttp's
functions are linked (stage 6f), which replaces it by `Handler_full`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Handler

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

axiom rafthttp.Transport.Handler.wp_proof : rafthttp.Transport.Handler.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
