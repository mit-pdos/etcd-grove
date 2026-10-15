/-
`s.applySnapshot(ep, ap)` (`server.go`), under raft's contract that a `toApply` carries no
snapshot (`rnApP`: `ap.snapshot = nil`). Lean-first (no Rocq counterpart); the request path's
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

/-- `s.applySnapshot(ep, ap)` with no snapshot (`ap.snapshot = nil`, raft's contract): it returns
at once (`raft.IsEmptySnap(nil)`). -/
abbrev EtcdServer.applySnapshot.spec : Prop :=
  ∀ (s ep ap : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      taSnapshotAddr ap ↦□ (null : Loc) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applySnapshot")) (Val #ep))
      (Val #ap))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
