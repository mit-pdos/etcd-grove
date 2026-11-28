/-
(hraft_robust R3) The spec of `disk.(*Disk).StageCommitIndex` (`disk.go`): `staged := idx`, atomically.
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

/-- `d.StageCommitIndex(idx)`: atomically, `staged := idx`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StageCommitIndex.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) (idx : w64),
  ⊢ ∀ Φ : val → IProp GF,
    isDisk g d Wl Ws Wf -∗
    (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, diskOwnL g A ∗
      (diskOwnL g { A with staged := idx } ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
    WP (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"StageCommitIndex")) (Val #idx)) {{ Φ }}

end sec

end Perennial
