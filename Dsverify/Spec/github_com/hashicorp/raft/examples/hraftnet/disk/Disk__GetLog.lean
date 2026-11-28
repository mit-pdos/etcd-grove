/-
(hraft_robust R3) The spec of `disk.(*Disk).GetLog` (`disk.go`): a copy of the entry, or `ErrLogNotFound`, atomically.
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

/-- `d.GetLog(idx, ptr)`: atomically, `getLogPost`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetLog.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (idx : w64) (ptr : Loc) (lv0 : Log),
  ⊢ ∀ Φ : val → IProp GF,
    isDisk g d Wl Ws Wf -∗ ptr ↦ lv0 -∗
    (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, diskOwnL g A ∗
      (diskOwnL g A ={∅,⊤ \ ↑storeN}=∗ ∀ err : GoInterface, getLogPost ptr (uint.nat idx) A.m err -∗ Φ #err)) -∗
    WP (App (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"GetLog")) (Val #idx)) (Val #ptr)) {{ Φ }}

end sec

end Perennial
