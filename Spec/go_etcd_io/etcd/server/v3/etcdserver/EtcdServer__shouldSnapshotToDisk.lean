/-
`s.shouldSnapshotToDisk(ep)` (`server.go`). Lean-first (no Rocq counterpart); the request path's
unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

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

/-- `s.shouldSnapshotToDisk(ep)`: whether a disk snapshot is due (forced and not at the applied
index, or more than `SnapshotCount` entries since the last; some boolean: the apply loop's proof
needs no more). -/
abbrev EtcdServer.shouldSnapshotToDisk.spec : Prop :=
  ∀ (s ep : Loc) (f : Bool) (ai d sc : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvForceSnapAddr s ↦ f ∗ epAppliedIAddr ep ↦ ai ∗ epDiskSnapAddr ep ↦ d ∗
      srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"shouldSnapshotToDisk")) (Val #ep))
  {{ (r : Bool), RET #r;
      srvForceSnapAddr s ↦ f ∗ epAppliedIAddr ep ↦ ai ∗ epDiskSnapAddr ep ↦ d }}

end spec

end EtcdGrove
end Perennial
