/-
(hraft_robust R3) The spec of `disk.Open` (`disk.go`): the `*Disk` of a generation started from the image `dir/raft` holds.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Inv

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

/-- `Open(dir)` on a file holding `v` with `imgHolds v D` (durable's state `⟨v, none⟩`, as `durBoot` leaves it):
a `*Disk` of a fresh generation `g` (its invariant idle, the caller's window families), the crash token, and the
client views at `D.crash` (nothing staged). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Open.spec : Prop :=
  ∀ (γd : DurFs.DurGS) (f : DurFs.DFile) (R : Fs.Roots) (qc : Qp) (dir : GoString)
    (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) (v : Option GoString) (D : DiskAbs),
  f.Ok → f.name = dir ++ go!"/raft" → imgHolds v D →
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk -∗
    Fs.osInv -∗ Fs.osSharedInv R -∗ DurFs.durInv γd f -∗ DurFs.durSt γd ⟨v, none⟩ -∗
    DurFs.durHandle γd f R -∗ Fs.osCallPerm (Fs.callKey R f.d) qc -∗
    (∀ (g : DiskGen) (d : Loc), ⌜g.γd = γd ∧ g.f = f ∧ g.R = R⌝ -∗ isDisk g d Wl Ws Wf -∗ token g.γk -∗
      diskOwnL g D.crash.L -∗ diskOwnS g D.crash.S -∗ Φ (PairV #d #interface.nil)) -∗
    WP (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.Open)) (Val #dir)) {{ Φ }}

end sec

end Perennial
