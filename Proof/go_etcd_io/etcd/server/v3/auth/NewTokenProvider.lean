/-
The trust boundary: `auth.NewTokenProvider(lg, opts, indexWaiter, ttl)` (`store.go`): names-only.
Lean-first (no Rocq counterpart); the server-construction unit, settled at unit N1 (2026-10-17),
for `NewServer`: why the statement is true of the Go code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.NewTokenProvider

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

axiom auth.NewTokenProvider.wp_proof : auth.NewTokenProvider.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
