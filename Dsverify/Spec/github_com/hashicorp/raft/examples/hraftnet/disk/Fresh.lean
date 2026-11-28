/-
(hraft_robust R3) The spec of `disk.Fresh` (`disk.go`): the first start's empty `*Disk`, written to `dir/raft` whatever it held.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.BootLemmas

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

/-- `Fresh(dir)` from any state of the file: a `*Disk` of a fresh generation `g` at the empty state, its
crash token and the client views; the caller's `Wf` is held by the invariant while the write may not have
survived a crash (`diskCrash`'s third case) and comes back. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Fresh.spec : Prop :=
  ∀ (γd : DurFs.DurGS) (f : DurFs.DFile) (R : Fs.Roots) (qc : Qp) (dir : GoString)
    (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) (s : DurFs.DurSt),
  f.Ok → f.name = dir ++ go!"/raft" →
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk -∗
    Fs.osInv -∗ Fs.osSharedInv R -∗ DurFs.durInv γd f -∗ DurFs.durSt γd s -∗
    DurFs.durHandle γd f R -∗ Fs.osCallPerm (Fs.callKey R f.d) qc -∗ Wf -∗
    (∀ (g : DiskGen) (d : Loc), ⌜g.γd = γd ∧ g.f = f ∧ g.R = R⌝ -∗ isDisk g d Wl Ws Wf -∗ token g.γk -∗
      diskOwnL g LogAbs.empty -∗ diskOwnS g ⟨∅, ∅⟩ -∗ Wf -∗ Φ #d) -∗
    WP (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.Fresh)) (Val #dir)) {{ Φ }}

end sec

end Perennial
