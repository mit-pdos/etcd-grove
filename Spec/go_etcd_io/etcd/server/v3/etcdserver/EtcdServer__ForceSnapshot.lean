/-
`s.ForceSnapshot()` (`server.go`): `s.forceDiskSnapshot = true`.
Lean-first (no Rocq counterpart); D14i (2026-10-17): the applier's `SnapshotServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.ForceSnapshot()` sets `s.forceDiskSnapshot`, the apply thread's (`srvFS`). -/
abbrev EtcdServer.ForceSnapshot.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvFS s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ForceSnapshot")) (Val #()))
  {{ RET #(); srvFS s }}

end spec

end EtcdGrove
end Perennial
