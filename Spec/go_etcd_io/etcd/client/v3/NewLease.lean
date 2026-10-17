/-
`clientv3.NewLease(c)` (`client/v3`, names only; item 5: `newClient` calls it). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewLease(c)` of a client `New` builds (its connection, call options, configuration and
logger, read-only: `clientCoreAt`): some value (the client's API, unused by the results). -/
abbrev NewLease.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCoreAt c }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewLease)) (Val #c))
  {{ (v : GoInterface), RET #v; True }}

end spec

end EtcdGrove
end Perennial
