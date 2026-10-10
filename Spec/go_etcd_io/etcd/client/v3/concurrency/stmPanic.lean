/-
The STM's abort: `panic(stmError{err})` (`client/v3/concurrency/stm.go`), the trust
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

/-- **The STM's abort does not return**: `panic(stmError{err})` for a non-nil `err` (what
`stm.fetch` and the commits do on a client error) satisfies any postcondition. Perennial's
`panic` is stuck (a verified program never panics) and Perennial has no `recover`; this panic is
recovered by `runSTM`'s deferred function, which sends `(nil, err)`: `NewSTM` returns an error,
which its spec allows with no further promise. The trust boundary (an axiom); see
`decisions.md`. -/
abbrev stmPanic.spec : Prop :=
  ∀ (err : GoInterface) (Φ : val → IProp GF), err ≠ GoInterface.nil →
    ⊢ WP (App (Val (@! go.panic)) (Val #(interface.mkOk stmError.ty #(stmError.mk err)))) {{ Φ }}

end spec

end concurrency
end EtcdGrove
end Perennial
