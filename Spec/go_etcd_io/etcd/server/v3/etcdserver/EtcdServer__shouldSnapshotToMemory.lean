/-
`s.shouldSnapshotToMemory(ep)` (`server.go`). Lean-first (no Rocq counterpart); the request path's
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

/-- `s.shouldSnapshotToMemory(ep)`: whether more than `memorySnapshotCount` entries were applied
since the last in-memory snapshot (some boolean: the apply loop's proof needs no more). -/
abbrev EtcdServer.shouldSnapshotToMemory.spec : Prop :=
  ∀ (s ep : Loc) (ai m : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      epAppliedIAddr ep ↦ ai ∗ epMemSnapAddr ep ↦ m }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"shouldSnapshotToMemory")) (Val #ep))
  {{ (r : Bool), RET #r;
      epAppliedIAddr ep ↦ ai ∗ epMemSnapAddr ep ↦ m }}

end spec

end EtcdGrove
end Perennial
