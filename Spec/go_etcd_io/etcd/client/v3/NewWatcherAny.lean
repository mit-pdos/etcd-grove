/-
`clientv3.NewWatcher(c)` (pr-verify etcd#21714: what `clientv3.newClient` needs of it: the call returns, for a client
whose connection is any; the function's own spec, `Spec/go_etcd_io/etcd/client/v3/NewWatcher.lean`, is
for a connection to an etcd server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvNewClient

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

/-- `clientv3.NewWatcher(c)` of a dialed client (`clientConnAt`) returns some interface value. -/
abbrev NewWatcherAny.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ clientConnAt c }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewWatcher)) (Val #c))
  {{ (v : GoInterface), RET #v; True }}

end spec

end EtcdGrove
end Perennial
