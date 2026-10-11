/-
`concurrency.WithTTL(ttl)` (`client/v3/concurrency/session.go`). Lean-first (no Rocq counterpart); see
`InvSession.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSession

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `WithTTL(ttl)`: an option setting the TTL to `ttl` if it is positive (otherwise the option
logs a warning and keeps the TTL). -/
abbrev WithTTL.spec : Prop :=
  ∀ (ttl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }}
    (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.WithTTL)) (Val #ttl))
  {{ (f : GoFunc), RET #f; sessionOptSpec f (withTTLM ttl) }}

end spec

end concurrency
end EtcdGrove
end Perennial
