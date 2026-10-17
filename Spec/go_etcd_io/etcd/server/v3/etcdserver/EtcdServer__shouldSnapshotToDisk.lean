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

/-- **The disk-snapshot test of etcd#21574's code**, as the PR wrote it:
`(ep.appliedi != ep.diskSnapshotIndex) || (ep.appliedi-ep.diskSnapshotIndex > s.Cfg.SnapshotCount)`.
The PR removed `s.forceDiskSnapshot` but kept its disjunct without the flag, so the result is true
whenever anything was applied since the last disk snapshot, whatever `SnapshotCount` is (the
`SnapshotCount` disjunct is then redundant). The result is stated exactly; the apply loop's proof uses
none of it (the old spec, "some boolean", is `spec_old` in the proof file, and follows). What the
PR appears to intend (the snapshot count alone, `shouldSnapshotToDisk.intended`, in the proof file)
differs from this value whenever `d < ai ≤ d + sc` (`shouldSnapshotToDisk.pr_ne_intended`). -/
abbrev EtcdServer.shouldSnapshotToDisk.spec : Prop :=
  ∀ (s ep : Loc) (ai d sc : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      epAppliedIAddr ep ↦ ai ∗ epDiskSnapAddr ep ↦ d ∗
      srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"shouldSnapshotToDisk")) (Val #ep))
  {{ (r : Bool), RET #r;
      ⌜r = (decide (ai ≠ d) || decide (uint.Z sc < uint.Z (ai - d)))⌝ ∗
      epAppliedIAddr ep ↦ ai ∗ epDiskSnapAddr ep ↦ d }}

end spec

end EtcdGrove
end Perennial
