/-
`version.Manager.DowngradeCancel` (`server/v3/etcdserver/version/version.go`; pr-verify etcd#22589). Lean-first (no Rocq
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

/-- **`m.DowngradeCancel(ctx)`** (unchanged by the PR): the linearizable read, then the downgrade
info (`GetDowngradeInfo`, non-nil by the contract: the code does not check), then, only if a
downgrade is enabled, the server's `DowngradeCancel` (which consumes `CP`). Either the read failed
(its error, `CP` given back), or no downgrade was enabled (`ErrNoInflightDowngrade`, `CP` given
back), or the cancel was proposed (its error, any). It does not read the cluster version. -/
abbrev version.Manager.DowngradeCancel.spec : Prop :=
  ∀ (m : Loc) (vs : GoInterface) (RE : GoInterface → IProp GF) (CVR : Loc → IProp GF)
    (EP CP : IProp GF) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗ version.versionFacts ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.version.Manager go!"s" m ↦□ vs ∗ version.isServer vs RE CVR EP CP ∗ CP }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.version.Manager.ty @!! go!"DowngradeCancel")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      (⌜err ≠ GoInterface.nil⌝ ∗ RE err ∗ CP) ∨
      (dgErrIs ErrNoInflightDowngrade err ∗ RE GoInterface.nil ∗ CP) ∨
      RE GoInterface.nil }}

end spec

end EtcdGrove
end Perennial
