/-
`version.allowedDowngradeVersion` (`server/v3/etcdserver/version/downgrade.go`; pr-verify etcd#22589). Lean-first (no Rocq
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

/-- **`allowedDowngradeVersion(ver)`** (`ver` not nil: it calls `ver.Major()` and `ver.Minor()`, value-receiver methods, which panic on a nil pointer: the panic the PR removes from `DowngradeValidate`) returns a version, not nil (`semver.New`). -/
abbrev version.allowedDowngradeVersion.spec : Prop :=
  ∀ (ver : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗ ⌜ver ≠ null⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.version.allowedDowngradeVersion)) (Val #ver))
  {{ (r : Loc), RET #r; ⌜r ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
