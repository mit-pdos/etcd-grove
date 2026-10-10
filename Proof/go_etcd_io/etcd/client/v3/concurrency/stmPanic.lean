/-
The trust boundary: `stmPanic` (`Spec/go_etcd_io/etcd/client/v3/concurrency/stmPanic.lean`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmPanic

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

/-- **The trust boundary**: the STM's abort, `panic(stmError{err})` with a non-nil `err`, does not
return (Perennial models no `panic` but a stuck one, and no `recover`); `runSTM`'s deferred function
recovers it into `NewSTM`'s error. See `decisions.md`, "STM". -/
axiom stmPanic.wp_proof : stmPanic.spec (GF := GF) (hG := hG)

end proof

end concurrency
end EtcdGrove
end Perennial
