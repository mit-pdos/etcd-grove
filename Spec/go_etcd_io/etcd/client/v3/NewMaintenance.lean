/-
`clientv3.NewMaintenance(c)` (`client/v3`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvNewClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewMaintenance(c)` of a dialed client (`clientConnAt`) returns some interface value (a `*maintenance` over the client's connection, call options and logger). -/
abbrev NewMaintenance.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientConnAt c }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewMaintenance)) (Val #c))
  {{ (v : GoInterface), RET #v; True }}

end spec

end EtcdGrove
end Perennial
