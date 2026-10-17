/-
`version.Manager.DowngradeEnable` (`server/v3/etcdserver/version/version.go`; pr-verify etcd#22589). Lean-first (no Rocq
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

/-- **`m.DowngradeEnable(ctx, tv)`**: `DowngradeValidate`, then, only if it returned `nil`, the
server's `DowngradeEnable` (which consumes `EP`). Either validation failed, with
`DowngradeValidate`'s error (`version.validateOutcome`, not `nil`) and nothing proposed (`EP` given
back: in particular a `nil` cluster version proposes nothing), or the proposal was made after the
read succeeded and a non-nil cluster version was seen (its error, any, is returned). -/
abbrev version.Manager.DowngradeEnable.spec : Prop :=
  ∀ (m : Loc) (vs : GoInterface) (RE : GoInterface → IProp GF) (CVR : Loc → IProp GF)
    (EP CP : IProp GF) (ctx : GoInterface) (tv : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗ version.versionFacts ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.version.Manager go!"s" m ↦□ vs ∗ version.isServer vs RE CVR EP CP ∗
      ⌜tv ≠ null⌝ ∗ EP }}
    (App (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.version.Manager.ty @!! go!"DowngradeEnable")) (Val #ctx)) (Val #tv))
  {{ (err : GoInterface), RET #err;
      (⌜err ≠ GoInterface.nil⌝ ∗ version.validateOutcome RE CVR err ∗ EP) ∨
      (∃ cv : Loc, ⌜cv ≠ null⌝ ∗ RE GoInterface.nil ∗ CVR cv) }}

end spec

end EtcdGrove
end Perennial
