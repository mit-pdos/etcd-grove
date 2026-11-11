/-
**Two pieces of `run`'s premise** (`server.go`), Lean-first: the restart-only `srvWinPend` (R2d'a A7,
`isServerRunC`'s `Hwpend`) and the disk snapshot's storage from the snapshot bundle
(`srvSnapDisk_of_RO`). Until 2026-11-07 this file held `isServerRun`, `run`'s mode-off premise,
deleted with `RunOn.lean`'s `isServerRunOn` once `isServerRunC` (`AuthCompRows.lean`) stopped
using them (R2d'a swap batch 5; the hub owner's call). The vocabulary (`applyRes`, `applyStart`,
`srvMetaSnap`, ...) is `InvRunRes.lean`'s, the lease subsystem's premise (`lease.runCfg`)
`LeaseRun.lean`'s (2026-11-04, the lease-expiry plan's Part C, option (a)).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 in
/-- (R2d'a A7, `Hwpend`; A10 item 5, 2026-11-06; DRAFT, approved by 82 as hub owner, the narrowed
text) **No merged snapshot sent at a new raft term while the replay window is pending**, a
restart-only premise: a token `γwp` held while the window is open, and with it, for a batch's raft
term `rt` above the restored `HardState` term `γn.t0` (`rnRtOk`) and a log of length `n` inside the
restart point's backend log `γn.a0`, the `MsgSnap` this member sent and the bag hands `applyAll` is
not at `rt` (`server.go:1018-1020`'s guard fails, so no merge inside the window).

What it was meant to exclude: the restarted incarnation elected at a term `T' > T₀` while raft is
still handing out the replay, then sending a `MsgSnap` at `T'`. **What it excludes (corrected
2026-11-07, `notes/decisions.md`, "R2d'a's disclosure corrected (2026-11-07)"): every `MsgSnap`
this member sends at a committed term above `T₀`, at any time in the incarnation**: `n` is free
(`n = 0` meets the guard) and the token is never consumed. So it is false of every restarted run
(`a0 ≠ []`) in which the member is later elected and snapshots a lagging follower. R2d'b restates
it with `n` tied to the replay; R2s REMOVES it by following the merged snapshot in the ghost. The
runs below, found first (review of R2d'a, finding 3), are a small part of the false ones. The trace: a replay over 1 MB is split into several `Ready`s by
`MaxCommittedSizePerReady` (unset in etcd, so `MaxSizePerMsg`, 1 MB); a snapshot inside the window
compacts the raft log (e.g. the forced one a replayed `ClusterVersionSet` triggers, at Go's applied
index above `SnapshotCatchUpEntries`); the member is elected above `t0` mid-replay; a lagging
follower gets a `MsgSnap` at the new term, which `server.go:1018` merges inside the window. Go is
correct there; the premise is a scope restriction of the proof model. The Go probe
(`notes/restart-probe/`: 0 runs with etcd's drained handout, 2-3% with a slow one) understates it:
its handout is by entry count, not bytes, so it never splits a replay the way 1 MB does
(`notes/restart-plan.md`, "Hwpend: the Go probe and the narrowing"). A batch at `rt ≤ T₀` needs no
premise: this incarnation's `MsgSnap`s are above `T₀` (`rnSnapMsg`). **R2e's closed theorem must
not carry it**; it gets an `axiom`-skill attack before R2d'b's Freeze (target: a former leader that
sent a `MsgSnap` at `rt` and restarted with its first window batch at `rt`; `sentMsg` is persistent
and keyed by member id, not incarnation). **At a first start (`γn.a0 = []`) it is free**: the guard
`n < |a0|` never holds, so a token gives it (`srvWinPend_first`). -/
def srvWinPend (s : Loc) (γr : ReadNames) (γn : RNNames) : IProp GF :=
  letI := srvStor (GF := GF) γr.raft.raft
  iprop(∃ γwp : GName, token γwp ∗
    □ (∀ (rt : w64) (n : Nat), token γwp -∗ ⌜n < γn.a0.length ∧ uint.Z γn.t0 < uint.Z rt⌝ -∗
        rnRtOk γn rt n -∗
        ∀ (id : w64) (m : Loc) (st : MsgSt),
          srvMemberIDAddr s ↦□ id -∗ msgOwn m (DFrac.own 1) st -∗
            sentMsg γr.raft.raft.cl srvClusterN id st -∗
            ⌜st.msg.Type' = MsgSnap → st.msg.Term' ≠ rt⌝ ∗ msgOwn m (DFrac.own 1) st ∗ token γwp))

/-- (R2d'a A10 item 5) **At a first start `srvWinPend` is free**: with the backend's log empty the
guard `n < |a0|` never holds, so any token gives it (`NewServer` allocates one). -/
theorem srvWinPend_first (s : Loc) (γr : ReadNames) (γn : RNNames) (h : γn.a0 = []) (γwp : GName) :
    token γwp ⊢ srvWinPend (GF := GF) s γr γn := by
  iintro Ht
  iunfold srvWinPend
  iexists γwp
  iframe Ht
  imodintro
  iintro %rt %n - %hn
  exfalso
  rw [h] at hn
  exact Nat.not_lt_zero _ hn.1

end defs

section snapDisk
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (2026-10-31, #11) **The disk snapshot's storage, from the snapshot path's bundle and the raft
wrapper**: the bundle's storage over the snapshotter (`srvSnapRO`) is the wrapper's, whose WAL
contract is `isRaftNode`'s (`isRNWal`); a snapshot at `j` is removable once `j + 1` is applied
(`srvSnapRm`'s right disjunct). -/
theorem srvSnapDisk_of_RO (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γt : GName)
    (Er : RNEnv GF) (γn : RNNames) :
    srvSnapRO (GF := GF) s ci E γr γt ∗ isRaftNode Er γn (srvRAddr s) ⊢ srvSnapDisk s γr := by
  iintro ⟨#Hro, #Hrn⟩
  iunfold srvSnapRO at Hro
  icases Hro with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al, %ast, %lp, %cl, %ps, %dir, %d, %Hp,
    #HL, #Hzl, #HD, #HF, #HFg, #Hvo, #HQ, #HW, #HSs, #HSi, #HH, #HHi, #HSt, #HM, #Hinv, -⟩
  iunfold isRaftNode at Hrn
  iNamed Hrn
  icombine HSt Hst gives %Heq
  iunfold srvSnapDisk
  iexists stp, ss, γd, srvImageM γr.raft.raft.authOn γr.raft.raft, srvSnapRm γt γr
  iframe HSt Hinv
  isplitr
  · ipureintro; exact Hp.2.1
  isplitr
  · rw [Heq]; iexact Hsti
  iintro !> %j #Hj
  iunfold srvSnapRm
  iright; iexact Hj

end snapDisk

end EtcdGrove
end Perennial
