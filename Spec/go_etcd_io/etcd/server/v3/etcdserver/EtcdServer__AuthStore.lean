/-
`s.AuthStore()` (`server.go`): the auth store field. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.AuthStore()` returns the `authStore` field. -/
abbrev EtcdServer.AuthStore.spec : Prop :=
  ∀ (s : Loc) (st : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ st }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthStore")) (Val #()))
  {{ RET #st; True }}

end spec

end EtcdGrove
end Perennial
