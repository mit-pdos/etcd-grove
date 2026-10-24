/-
The trust boundary: `(*auth.authStore).Recover(be)` (names-only). Lean-first (no Rocq
counterpart); D22 receiver epochs, S8c (2026-10-24), an axiom: why the statement is true of the Go
code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Recover

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

axiom auth.authStore.Recover.wp_proof : auth.authStore.Recover.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
