/-
`version.Manager.DowngradeValidate` (`server/v3/etcdserver/version/version.go`; pr-verify etcd#22589). Lean-first (no Rocq
counterpart); the vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/version/Base.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.version

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

/-- **`m.DowngradeValidate(ctx, tv)`** (a non-nil target `tv`, as `convertToClusterVersion` gives; a
manager whose `Server` is `vs`, `version.isServer`): it returns, for every cluster version the
server reports, `nil` included (no panic), an error as `version.validateOutcome` describes: a
`nil` cluster version gives `ErrClusterVersionUnavailable`. It proposes nothing (`EP`, `CP` are
not needed). -/
abbrev version.Manager.DowngradeValidate.spec : Prop :=
  ∀ (m : Loc) (vs : GoInterface) (RE : GoInterface → IProp GF) (CVR : Loc → IProp GF)
    (EP CP : IProp GF) (ctx : GoInterface) (tv : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗ version.versionFacts ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.version.Manager go!"s" m ↦□ vs ∗ version.isServer vs RE CVR EP CP ∗
      ⌜tv ≠ null⌝ }}
    (App (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.version.Manager.ty @!! go!"DowngradeValidate")) (Val #ctx)) (Val #tv))
  {{ (err : GoInterface), RET #err; version.validateOutcome RE CVR err }}

end spec

end EtcdGrove
end Perennial
