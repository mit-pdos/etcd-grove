/-
`(*EtcdServer).hasPublishedAttributes()` (`server.go`; new in etcd-io/etcd#22525): whether the
applied membership holds this member's current attributes, `publishV3`'s snapshot check. With its
body. Lean-first (no Rocq counterpart); see `InvPublish.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvPublish

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.hasPublishedAttributes()` (the member `id`, the cluster `c`, the attributes `a` with client
URLs `cus`, all read-only) returns `true` only if the cluster's membership held exactly `a`'s
name and client URLs (in order) for `id`. -/
abbrev EtcdServer.hasPublishedAttributes.spec : Prop :=
  ∀ (s c : Loc) (id : w64) (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes)
    (cus : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvMemberAttrs s c id a cus }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"hasPublishedAttributes"))
      (Val #()))
  {{ (b : Bool), RET #b; ⌜b = true → membership.attrsHeld c id a.Name' cus⌝ }}

end spec

end EtcdGrove
end Perennial
