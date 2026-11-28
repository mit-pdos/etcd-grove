/-
(hraft_robust R3) The spec of `disk.FreshSnaps` (`snap.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.SinkDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

/-- `FreshSnaps(dir)` from any state of the file: a `*Snaps` of a fresh generation `g` with no snapshot, its crash
token and the client view; the caller's `Wf` is held by the invariant while the write may not have survived a
crash (`snapsCrash`'s third case) and comes back. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.FreshSnaps.spec : Prop :=
  ∀ (γd : DurFs.DurGS) (f : DurFs.DFile) (R : Fs.Roots) (qc : Qp) (dir : GoString)
    (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (st : DurFs.DurSt),
  f.Ok → f.name = dir ++ go!"/snap" →
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk -∗
    Fs.osInv -∗ Fs.osSharedInv R -∗ DurFs.durInv γd f -∗ DurFs.durSt γd st -∗
    DurFs.durHandle γd f R -∗ Fs.osCallPerm (Fs.callKey R f.d) qc -∗ Wf -∗
    (∀ (g : SnapGen) (s : Loc), ⌜g.γd = γd ∧ g.f = f ∧ g.R = R⌝ -∗ isSnaps g s Qc Wf -∗ token g.γk -∗
      snapsOwn g none -∗ Wf -∗ Φ #s) -∗
    WP (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.FreshSnaps)) (Val #dir)) {{ Φ }}

end sec

end Perennial
