/-
`concurrency.WithPrefetch(keys...)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `WithPrefetch(keys...)`: an option appending `keys` (read-only) to the keys to prefetch. -/
abbrev WithPrefetch.spec : Prop :=
  ∀ (sl : GoSlice) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ sl ↦*□ ks }}
    (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.WithPrefetch)) (Val #sl))
  {{ (f : GoFunc), RET #f; stmOptSpec f (withPrefetchM ks) }}

end spec

end concurrency
end EtcdGrove
end Perennial
