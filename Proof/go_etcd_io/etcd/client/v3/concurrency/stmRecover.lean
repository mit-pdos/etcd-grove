/-
The trust boundary: `stmRecover` (`Spec/go_etcd_io/etcd/client/v3/concurrency/stmRecover.lean`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmRecover

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **The trust boundary**: `recover()` returns nil where a verified execution reaches it (no panic
in flight: the STM's aborts do not return, `stmPanic.wp_proof`; every other panic is stuck). See
`decisions.md`, "STM". -/
axiom stmRecover.wp_proof : stmRecover.spec (GF := GF) (hG := hG)

end proof

end concurrency
end EtcdGrove
end Perennial
