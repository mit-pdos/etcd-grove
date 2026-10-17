/-
`EtcdServer.downgradeValidate` (`v3_server.go`; unchanged by etcd#22589, which changes the manager's `DowngradeValidate` it calls). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/BaseDowngrade.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseDowngrade

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- **`s.downgradeValidate(ctx, v)`** (`Downgrade`'s `VALIDATE`). No panic. A target that does not
convert gives `ErrWrongDowngradeVersionFormat` first; a `nil` cluster version (here or in the
manager) `ErrClusterVersionUnavailable`; the manager's other errors are returned; else a response
and `nil`. It proposes nothing: it holds neither proposal right (`EP`, `CP`). -/
abbrev EtcdServer.downgradeValidate.spec : Prop :=
  ∀ (s l : Loc) (EP CP : IProp GF) (ctx : GoInterface) (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvDowngradeOk s l EP CP ∗ srvLgReader s }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"downgradeValidate")) (Val #ctx)) (Val #v))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLgReader s ∗ dgValidatePost v resp err }}

end spec

end EtcdGrove
end Perennial
