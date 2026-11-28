/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__restoreSnapshot.lean (241f27e).
-/
/-
`raft.(*Raft).restoreSnapshot`'s spec (API-internal): restores the snapshot store's latest snapshot, if any (hraft_robust R5).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftRec
public import Dsverify.Proof.github_com.hashicorp.raft.SnapDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).restoreSnapshot` (`NewRaft`'s, hraft_robust R5): restores the snapshot store's latest `lat` (read
twice, `List` then `Open`, through the caller's accessor `P`: the boot pin's view of the store), if any, into
the FSM (`tryRestoreSingleSnapshot`), and sets `lastApplied` and the last snapshot (in `lastLock`, whose
effective last entry becomes the snapshot's if the last log entry `n` is below it) to its index and term and both
configurations to its configuration; returns nil. Before it, `lastApplied` is `0` and the last snapshot none (so
`lastLock`'s ghost is the last log entry). -/
abbrev github_com.hashicorp.raft.Raft.restoreSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (i : SID) (rc : RCtx GF) (c : Config) (x fx : GoInterfaceOk) (eof : GoInterface)
    (lat : SnapLatest) (P : IProp GF) (n t : Nat) (c0 l0 : Configuration) (i0 li0 : w64) (p0 : Loc) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     sync.atomic.ownValue (r.[Raft, go!"conf"]) DFrac.discard (interface.mkOk Config.ty #c) ∗
     ⌜c.NoSnapshotRestoreOnStart' = false⌝ ∗
     r.[Raft, go!"snapshots"] ↦□ (GoInterface.ok x) ∗ isSnapStore x rc.ownSS eof (snapWin γ rc i) ∗
     globalAddr io.EOF ↦□ eof ∗
     r.[Raft, go!"fsm"] ↦□ (GoInterface.ok fx) ∗ isFSM fx γ i rc.fsmOwn rc.respP rc.snapP ∗
     P ∗ □ (P -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old, rc.ownSS old ∗ ⌜old = lat⌝ ∗
        (rc.ownSS old ={∅, ⊤ \ ↑storeN}=∗ P)) ∗ latFacts γ rc i lat ∗
     appliedCell r rc ∗ monoNatAuthOwn rc.dur.applied (1 : Qp).half 0 ∗
     sync.isMutex (r.[Raft, go!"raftState"].[raftState, go!"lastLock"]) (lastLockInv r γ rc i) ∗
     ghostVar rc.names.lastLog (1 : Qp).half (n, t) ∗
     r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 l0 li0 ∗
     sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p0 ∗
     rc.fsmOwn 0 ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"restoreSnapshot")) (Val #()))
  {{ RET #interface.nil; P ∗ rtok tid ∗
      match lat with
      | none => monoNatAuthOwn rc.dur.applied (1 : Qp).half 0 ∗ ghostVar rc.names.lastLog (1 : Qp).half (n, t) ∗
          r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 l0 li0 ∗
          sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p0 ∗
          rc.fsmOwn 0
      | some (m, _) => monoNatAuthOwn rc.dur.applied (1 : Qp).half (uint.nat m.Index') ∗
          ghostVar rc.names.lastLog (1 : Qp).half
            (if n < uint.nat m.Index' then (uint.nat m.Index', uint.nat m.Term') else (n, t)) ∗
          r.[Raft, go!"configurations"] ↦ configurations.mk m.Configuration' m.ConfigurationIndex'
            m.Configuration' m.ConfigurationIndex' ∗
          (∃ (p : Loc) (c' : Configuration) (ss : List Server),
            sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p ∗
            p ↦□ c' ∗ c'.Servers' ↦* ss ∗ m.Configuration'.Servers' ↦*□ ss) ∗
          (∃ (k0 : Nat) (res : GoInterface), rc.fsmOwn k0 ∗ ⌜k0 ≤ uint.nat m.Index'⌝ ∗
            noCmdBetween γ k0 (uint.nat m.Index' + 1) ∗ (⌜k0 = 0⌝ ∨ rc.respP k0 res)) }}

end spec

end Perennial
