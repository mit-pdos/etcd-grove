/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__shouldSnapshotToDisk.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13); etcd#21574's code (2026-10-17): the result
stated exactly, the old spec (without the removed field) derived, and the PR's value compared with
the snapshot-count rule.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__shouldSnapshotToDisk

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.shouldSnapshotToDisk.wp_proof :
    EtcdServer.shouldSnapshotToDisk.spec (GF := GF) (hG := hG) := by
  intro s ep ai d sc
  wp_start as ⟨Hai, Hd, #Hsc⟩
  wp_auto
  by_cases hd : ai = d
  · simp only [hd, decide_true]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp
  · simp only [hd, decide_false]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp [hd]

/-- The spec on `lean` (some boolean, the force flag framed), without the flag the PR removed:
what the apply loop's proof uses. -/
abbrev EtcdServer.shouldSnapshotToDisk.spec_old : Prop :=
  ∀ (s ep : Loc) (ai d sc : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      epAppliedIAddr ep ↦ ai ∗ epDiskSnapAddr ep ↦ d ∗
      srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"shouldSnapshotToDisk")) (Val #ep))
  {{ (r : Bool), RET #r; epAppliedIAddr ep ↦ ai ∗ epDiskSnapAddr ep ↦ d }}

theorem EtcdServer.shouldSnapshotToDisk.spec_implies_old :
    EtcdServer.shouldSnapshotToDisk.spec (GF := GF) (hG := hG) →
      EtcdServer.shouldSnapshotToDisk.spec_old (GF := GF) (hG := hG) := by
  intro h s ep ai d sc
  iintro %Φ Hpre HΦ
  iapply (h s ep ai d sc) $$ [Hpre]
  · iexact Hpre
  inext
  iintro %r ⟨%-, Hai, Hd⟩
  iapply HΦ
  iframe

end proof

/-- **The test the PR appears to intend** (its title, "Cleanup snapshot force", and the removed
field's TODO, "Replace with flush db in v3.7 assuming v3.6 bootstraps from db file": the forced
snapshot goes, `SnapshotCount` alone decides): a disk snapshot is due once more than `sc` entries
were applied since the last one. This is also the old code's value when no snapshot is forced
(`forceDiskSnapshot = false`). It is not safe either (`notes/pr-verify/etcd-21574.md`): with it, a
downgrade leaves no WAL snapshot record after the downgrade entry, and a v3.6 member restarted on
that data replays the earlier `ClusterVersionSet` naming 3.7 and panics (`MustDetectDowngrade`). -/
def EtcdServer.shouldSnapshotToDisk.intended (ai d sc : w64) : Bool :=
  decide (uint.Z sc < uint.Z (ai - d))

/-- **The PR's value is not the intended one**: whenever an entry was applied since the last disk
snapshot but no more than `SnapshotCount` (`d < ai ≤ d + sc`), the PR's code asks for a disk
snapshot and the snapshot-count rule does not. So, with the PR, the apply loop takes a disk
snapshot (a backend commit with its fsync, a WAL snapshot record with its fsync, a WAL release;
raft-log compaction already ran every `memorySnapshotCount` = 100 entries) after every batch of
entries it applies. -/
theorem EtcdServer.shouldSnapshotToDisk.pr_ne_intended (ai d sc : w64)
    (hlt : uint.Z d < uint.Z ai) (hle : uint.Z ai ≤ uint.Z d + uint.Z sc) :
    (decide (ai ≠ d) || decide (uint.Z sc < uint.Z (ai - d))) = true ∧
      EtcdServer.shouldSnapshotToDisk.intended ai d sc = false := by
  unfold EtcdServer.shouldSnapshotToDisk.intended
  have hne : ai ≠ d := by intro h; subst h; omega
  have hsub : uint.Z (ai - d) = uint.Z ai - uint.Z d := by word
  refine ⟨by simp [hne], ?_⟩
  simp only [decide_eq_false_iff_not, Int.not_lt]
  omega

end EtcdGrove
end Perennial
