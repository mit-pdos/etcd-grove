/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__restoreSnapshot.lean (241f27e).
-/
/-
`raft.(*Raft).restoreSnapshot`'s spec (API-internal): restores the snapshot store's latest snapshot, if any (hraft_robust R5).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftBoot
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

/-- `(*Raft).restoreSnapshot` (`NewRaft`'s, hraft_robust R5): during the boot (the raw crash invariant, the boot pin
`bootV` at the stores' arm-time state, the main goroutine's views), restores the snapshot store's latest `lat`, if
any, into the FSM (`tryRestoreSingleSnapshot`), and sets `lastApplied` (to the snapshot's index: with both halves of
its authority, the main goroutine's in the crash state while a discard is pending), the last snapshot (in
`lastLock`, its fields pinned by `NewRaft`'s half of `llb`, R5 Q8: the last log entry `(li, lt)` and no snapshot
before) and both configurations to the snapshot's; returns nil, with what the crash state keeps about the latest
(`latFacts`). -/
abbrev github_com.hashicorp.raft.Raft.restoreSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (i : SID) (rc : RCtx GF) (c : Config) (x fx : GoInterfaceOk) (eof : GoInterface)
    (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend) (dp : Option DiscPend)
    (li lt : w64) (c0 l0 : Configuration) (i0 li0 : w64) (p0 : Loc) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     sync.atomic.ownValue (r.[Raft, go!"conf"]) DFrac.discard (interface.mkOk Config.ty #c) ∗
     ⌜c.NoSnapshotRestoreOnStart' = false⌝ ∗
     r.[Raft, go!"snapshots"] ↦□ (GoInterface.ok x) ∗ isSnapStore x rc.ownSS eof (snapWin γ rc i) ∗
     globalAddr io.EOF ↦□ eof ∗
     r.[Raft, go!"fsm"] ↦□ (GoInterface.ok fx) ∗ isFSM fx γ i rc.fsmOwn rc.respP rc.snapP ∗
     srvDurInvRaw γ rc i ∗ bootV rc A lat ∗
     ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗ srvVP rc s tp dp ∗
     appliedCell r rc ∗ (monoNatAuthOwn rc.dur.applied (1 : Qp).half 0 ∨ ⌜∃ d, dp = some d⌝) ∗
     sync.isMutex (r.[Raft, go!"raftState"].[raftState, go!"lastLock"]) (lastLockInv r γ rc i) ∗
     dghostVar rc.names.llb (DFrac.own (1 : Qp).half) (some (li, lt, W64 0, W64 0)) ∗
     r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 l0 li0 ∗
     sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p0 ∗
     rc.fsmOwn 0 ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"restoreSnapshot")) (Val #()))
  {{ RET #interface.nil; bootV rc A lat ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗ srvVP rc s tp dp ∗
      rtok tid ∗ latFacts γ rc i lat ∗
      match lat with
      | none => (monoNatAuthOwn rc.dur.applied (1 : Qp).half 0 ∨ ⌜∃ d, dp = some d⌝) ∗
          dghostVar rc.names.llb (DFrac.own (1 : Qp).half) (some (li, lt, W64 0, W64 0)) ∗
          r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 l0 li0 ∗
          sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p0 ∗
          rc.fsmOwn 0
      | some (m, _) =>
          (monoNatAuthOwn rc.dur.applied (1 : Qp).half (uint.nat m.Index') ∨ ⌜∃ d, dp = some d⌝) ∗
          applLb rc (uint.nat m.Index') ∗
          dghostVar rc.names.llb (DFrac.own (1 : Qp).half) (some (li, lt, m.Index', m.Term')) ∗
          r.[Raft, go!"configurations"] ↦ configurations.mk m.Configuration' m.ConfigurationIndex'
            m.Configuration' m.ConfigurationIndex' ∗
          (∃ (p : Loc) (c' : Configuration) (ss : List Server),
            sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p ∗
            p ↦□ c' ∗ c'.Servers' ↦* ss ∗ m.Configuration'.Servers' ↦*□ ss) ∗
          (∃ (k0 : Nat) (res : GoInterface), rc.fsmOwn k0 ∗ ⌜k0 ≤ uint.nat m.Index'⌝ ∗
            noCmdBetween γ k0 (uint.nat m.Index' + 1) ∗ (⌜k0 = 0⌝ ∨ rc.respP k0 res)) }}

end spec

end Perennial
