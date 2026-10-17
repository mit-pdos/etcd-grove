/-
`c.Close()` (`client/v3/client.go`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
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

/-- `c.Close()` of a built client (`clientBuiltAt`) returns some error (it cancels the client's context,
closes its watcher, lease and connection). -/
abbrev Client.Close.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientBuiltAt c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
