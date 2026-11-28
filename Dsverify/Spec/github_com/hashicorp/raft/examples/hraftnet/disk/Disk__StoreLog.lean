/-
(hraft_robust R3) The spec of `disk.(*Disk).StoreLog` (`disk.go`): `StoreLogs` of one entry.
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

/-- `d.StoreLog(p)`: the entry `e` (at `p`) stored at `first` and `staged` written, durably. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLog.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (p : Loc) (first : Nat) (e : Entry),
  ⊢ ∀ Φ : val → IProp GF,
    ⌜1 ≤ first ∧ first < 2 ^ 64⌝ -∗ isDisk g d Wl Ws Wf -∗ logPtr p first e -∗ Wl (.store first [e]) -∗
    (Wl (.store first [e]) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, diskOwnL g A ∗
      (diskOwnL g (A.store first [e]) ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
    WP (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"StoreLog")) (Val #p)) {{ Φ }}

end sec

end Perennial
