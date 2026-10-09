/-
`clientv3.Client.Ctx()` (`client/v3/client.go`, translated for `client/v3/concurrency`). Lean-first (no
Rocq counterpart); see `InvClient.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `client.Ctx()`: the client's context (its `ctx` field, read-only). -/
abbrev Client.Ctx.spec : Prop :=
  ∀ (cl : Loc) (c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦□ c }}
    (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Ctx")) (Val #()))
  {{ RET #c; True }}

end spec

end EtcdGrove
end Perennial
