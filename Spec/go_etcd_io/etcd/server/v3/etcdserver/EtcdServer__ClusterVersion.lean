/-
`s.ClusterVersion()` (`server.go`): `nil` without a cluster, else `s.cluster.Version()`.
Lean-first (no Rocq counterpart); srvBuildGap's rows (2026-10-17): `start`'s `clusterVersionOk`
from the cluster's `Version` contract (`clusterVersionMono`, `bootstrap`'s).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart

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

/-- `s.ClusterVersion()`, its `cluster` field `cl` (read-only) meeting `clusterVersionMono`:
`nil` until the version is known, non-`nil` from then on. -/
abbrev EtcdServer.ClusterVersion.spec : Prop :=
  ∀ (s cl : Loc) (γcv : GName) (known : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvClusterAddr s ↦□ cl ∗ clusterVersionMono cl γcv ∗
      (if known then monoNatLbOwn γcv 1 else True) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ClusterVersion")) (Val #()))
  {{ (v : Loc), RET #v; ⌜v = null ∧ known = false⌝ ∨ ⌜v ≠ null⌝ ∗ monoNatLbOwn γcv 1 }}

end spec

end EtcdGrove
end Perennial
