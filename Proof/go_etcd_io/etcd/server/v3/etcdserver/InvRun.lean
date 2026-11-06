/-
**What `run` needs, `isServerRun`** (`server.go`): the construction premise of `run`'s spec. Lean-first.
The vocabulary it is written in (the log raft hands the apply side, the apply thread's resources
`applyRes`, `applyStart`, `srvMetaSnap`, ...) is `InvRunRes.lean`'s, the lease subsystem's premise
(`lease.runCfg`) `LeaseRun.lean`'s (2026-11-04, the lease-expiry plan's Part
C, option (a): split from this file so that the sealed `lease.runCfg` sits below `isServerRun`).
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

What it excludes, plainly: **the restarted incarnation is elected at a term `T' > T₀` while raft
is still handing out the replay, and then sends a `MsgSnap` at `T'`** (the Go probe,
`/shared/tmp/winpend-probe`: 0 runs with etcd's drained handout, 2-3% with a slow one;
`notes/restart-plan.md`, "Hwpend: the Go probe and the narrowing"). A batch at `rt ≤ T₀` needs no
premise: this incarnation's `MsgSnap`s are above `T₀` (`rnSnapMsg`). **R2s discharges it; R2e's
closed theorem must not carry it**; it gets an `axiom`-skill attack before R2d'b's Freeze (target: a
former leader that sent a `MsgSnap` at `rt` and restarted with its first window batch at `rt`;
`sentMsg` is persistent and keyed by member id, not incarnation). At a first start (`γn.a0 = []`)
the wand is vacuous (`srvWinPend_first`). -/
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

/-- **What `run` needs** (see `Spec/.../EtcdServer__run.lean`; named conjuncts): the apply
thread's view, `applyAll`'s, the raft wrapper (its node contract over the server's `E.C`), `run`'s
fields, the ticks; the snapshot's contract once; the raft wrapper's loop, apply and done tokens
at the empty log; the committed index's writer half; the right to close `done` (whose close
announces `DQ`: `True` by default; R2b-2, 2026-11-02: the stopped server's image, escrowed,
`srvDoneInv`, for `run.spec`) and `stopping`; the stop requests' predicate `SP`
(`srvRunFieldsAt`'s);
the apply thread's resources at the start; `run`'s own logger slot; the write budget (D19b: the
receipt-backed `srvWTPool`, until then `N` write tokens). -/
def isServerRun (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (SP : IProp GF := iprop(False)) (DQ : IProp GF := iprop(True)) : IProp GF :=
  iprop("#Hsrv" ∷ isServer s γ ci TM E ρ γr ∗
    "#Hsa" ∷ isServerApplyAll s γr ∗
    -- (J8b, 2026-11-01) the server's member id is the raft node's (`isServerBuilt`'s)
    "#Hmid" ∷ srvMemberIDAddr s ↦□ γn.id ∗
    -- (J8b, 2026-11-01) the meta reads of the backends a snapshot opens (`bootOk`'s `#HmetaSnap`)
    "#HmetaSnap" ∷ srvMetaSnap γ ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    -- (D43 M3, 2026-10-25) in raft's dynamic mode a fresh start: no entry replayed
    "%HEr" ∷ ⌜Er.C = srvC ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0) ∧
      -- (R2d'a A6, DRAFT) a first start: the restart point's backend log `γn.a0` empty
      γn.a0 = []⌝ ∗
    -- (R2d'a A7, A10 item 5, 2026-11-06; DRAFT, approved by 82) no merged snapshot sent at a new
    -- raft term while the replay window is pending (`srvWinPend`; a restart-only premise, R2s's
    -- target; free at a first start, `srvWinPend_first`)
    "Hwpend" ∷ srvWinPend s γr γn ∗
    -- (2026-10-30, the repair) the apply side's half of the node's running token
    "Hrunh" ∷ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗
    -- (2026-10-31) the WAL's open token: the apply side's half (its disk snapshot's `SaveSnap`, which
    -- `run` gives the raft loop with `raftNode.stop`) and the loop's (`raftNode.start`'s); the disk
    -- cooperating (`storage.diskOk`, `NewServer`'s premise)
    "Hwth" ∷ rnWalTokA γn (srvRAddr s) (1 : Qp).half ∗ "Hwtl" ∷ rnWalTokL γn (srvRAddr s) ∗
    "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
    -- (2026-11-02, the lease-grant plan's D2) in a cluster that grants leases, the open
    -- cases (`srvGrantOpen`, `NewServer`'s precondition); (2026-11-04, the lease-expiry plan's
    -- Part C) as the lease subsystem's sealed premise at some mode (`lease.runCfg`)
    "%Hslg" ∷ ⌜∃ m : lease.Mode, lease.runCfg (GF := GF) γr.kv.lm m⌝ ∗
    -- (2026-10-31, #11) the KV the snapshot commits (`start`'s `srvReadBuilt`)
    "#Hkvf" ∷ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
    "#Hrf" ∷ srvRunFieldsAt s γr γg γcx v SP ∗
    -- (revoke-open, 2026-11-06) the revocation's bundle (`run`'s expiry arm, revocable mode)
    "#Hrvk" ∷ srvRevokeCtx s E ρ γr γg ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce γn.node.reg γn.node.cl γn.key ms γn.γs ai₀ at₀) ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hdc" ∷ ownBroadcastChan v.done γd DQ .Pending ∗
    "Hclose" ∷ token γg.close ∗
    "Hstart" ∷ applyStart s γ ci b E γr ai₀ c₀ x₀ ρ.wait ∗
    "Hlr" ∷ srvLgReader s ∗
    -- (2026-10-19, D21 M3) with its counter, the apply thread's tokens taken through `ai₀`
    -- (H2, 2026-11-05) and its register at `GoAttach`'s receipts' name (`start` set it)
    "#HWB" ∷ (∃ γp : WTNames, srvWTPool E γp ∗ srvWTAt γp.cnt ai₀ ∗
      dghostVar γp.reg DFrac.discard (some γg.run)) ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`): its
    -- persistent bundle; (D22 J1b, 2026-10-31) the counter's authority and the stocks in `applyStart`
    "#Hsnapb" ∷ (∃ γt : GName, srvSnapRO s ci E γr γt) ∗
    -- (J8a-3, 2026-11-01) the two configuration fields `start` writes, read-only from then on:
    -- with `srvSnapRO`'s rebuild, the whole configuration read-only (`specSnap`'s `srvCfgAddr s ↦□`)
    "#Hsncfg" ∷ (∃ sc scu : w64, srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc ∗
      srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu))

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
    #HL, #HD, #HF, #HFg, #HQ, #HW, #HSs, #HSi, #HH, #HHi, #HSt, #HM, #Hinv, -⟩
  iunfold isRaftNode at Hrn
  iNamed Hrn
  icombine HSt Hst gives %Heq
  iunfold srvSnapDisk
  iexists stp, ss, γd, srvImageM γr.raft.raft.authOn γr.raft.raft, srvSnapRm γt γr
  iframe HSt Hinv
  isplitr
  · ipureintro; exact Hp.2.2.1
  isplitr
  · rw [Heq]; iexact Hsti
  iintro !> %j #Hj
  iunfold srvSnapRm
  iright; iexact Hj

end snapDisk

end EtcdGrove
end Perennial
