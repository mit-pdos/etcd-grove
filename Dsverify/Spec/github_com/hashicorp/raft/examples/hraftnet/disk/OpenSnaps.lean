/-
(hraft_robust R3) The spec of `disk.OpenSnaps` (`snap.go`).
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

/-- `OpenSnaps(dir)` on a file holding `v` with `snapHolds v lat svs` (durable's state `⟨v, none⟩`, as `durBoot`
leaves it; what `snapsCrash` gives): a `*Snaps` of a fresh generation `g` (its invariant idle, the caller's
`Qc`, `Wf`), the crash token, and the client view at `lat'`, which is `lat` up to its configuration's servers
slice (a fresh slice holding the old servers `svs`: `latEquiv`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.OpenSnaps.spec : Prop :=
  ∀ (γd : DurFs.DurGS) (f : DurFs.DFile) (R : Fs.Roots) (qc : Qp) (dir : GoString)
    (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (v : Option GoString) (lat : SnapLatest)
    (svs : List Server),
  f.Ok → f.name = dir ++ go!"/snap" → snapHolds v lat svs →
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk -∗
    Fs.osInv -∗ Fs.osSharedInv R -∗ DurFs.durInv γd f -∗ DurFs.durSt γd ⟨v, none⟩ -∗
    DurFs.durHandle γd f R -∗ Fs.osCallPerm (Fs.callKey R f.d) qc -∗
    (∀ (g : SnapGen) (s : Loc) (lat' : SnapLatest), ⌜g.γd = γd ∧ g.f = f ∧ g.R = R⌝ -∗ isSnaps g s Qc Wf -∗
      token g.γk -∗ snapsOwn g lat' -∗ latEquiv lat lat' svs -∗ Φ (PairV #s #interface.nil)) -∗
    WP (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.OpenSnaps)) (Val #dir)) {{ Φ }}

end sec

end Perennial
