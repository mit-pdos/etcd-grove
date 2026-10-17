/-
`allowedDowngradeVersion(ver)` (`downgrade.go`). Lean-first (the downgrade API,
etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Defs

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

/-- `allowedDowngradeVersion(ver)`, `ver` not nil (it calls `ver.Major()` and `ver.Minor()`, which
dereference it: the panic of etcd-io/etcd#22574 on `ENABLE` before the cluster version is known),
returns a version, not nil (`semver.New(major, minor-1, 0, "", "")`). -/
abbrev version.allowedDowngradeVersion.spec : Prop :=
  ∀ (ver : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗ ⌜ver ≠ null⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.version.allowedDowngradeVersion)) (Val #ver))
  {{ (v : Loc), RET #v; ⌜v ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
