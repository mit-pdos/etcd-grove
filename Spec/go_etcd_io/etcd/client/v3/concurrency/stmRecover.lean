/-
`recover()` in `runSTM`'s deferred function (`client/v3/concurrency/stm.go`), the trust
boundary. Lean-first (no Rocq counterpart); see
`InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`recover()` returns nil** where a verified execution reaches it: no panic is then in flight
(Perennial's panics are stuck, and the STM's aborts never return, `stmPanic.spec`). The trust
boundary (an axiom); see `decisions.md`. -/
abbrev stmRecover.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! go.recover)) (Val #())) {{ RET #interface.nil; True }}

end spec

end concurrency
end EtcdGrove
end Perennial
