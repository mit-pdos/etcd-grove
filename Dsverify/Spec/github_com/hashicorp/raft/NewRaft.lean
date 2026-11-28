/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/NewRaft.lean (241f27e).
-/
/-
`raft.NewRaft`'s spec (raft-internal interface, notes/raft-iface.md). Builds server `i` of protocol `γ` for one generation, from its armed and recovered crash state (hraft_robust R5); starts `run`, `runFSM`, `runSnapshots` (each through `goFunc`); returns `r` with `isRaft` and no error.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftRec

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

/-- `NewRaft`: Builds server `i` of protocol `γ` from its stores, for one generation `rc` of the server
(hraft_robust R5, R1 §6): the generation's crash state `X` is armed (`raft_arm`: the crash invariant
`srvDurInvRaw` with the boot pin at the arm-time stores, the main goroutine's views at `X`, the `lastApplied` authority at `0`, the compaction
frontier's at `X.c`, the pending-install and pending-write records empty) and recovered (`RecOk X`: a fresh server's genesis state, `freshDur`, or a restarted one's); restores the latest snapshot
(`restoreSnapshot`, into the FSM), finishes an interrupted install's discard (fix 2), scans the log after
the snapshot for configurations (fix 1, upstream #728); starts `run`, `runFSM`, `runSnapshots` (each
through `goFunc`); returns `r` with `isRaft` (for `rc` with the generation's raft-local names) and no
error. Needs the thread bound `2 ^ 28` (its `RWMutex` thread pools). The stores' contracts are over
raft's window families (`logWin`, `stWin`, `snapWin`) of `rc`. (Stage 4) The protocol's decoding of a
configuration's voters is `DecodeConfiguration`'s (`γ.cv = cfgDec γ.srvs`; `isRaft` keeps it).
(`RestoreCommittedLogs` is still `false`, `cfgOk`: REQUESTS.md Q5.) A store holding a snapshot gives
`FirstIndex` as its smallest key (`isLogStoreFirst`, for fix 2). -/
abbrev github_com.hashicorp.raft.NewRaft.spec : Prop :=
  ThreadBoundLe GF (2 ^ 28) →
  ∀ (cp : Loc) (c : Config) (fsmI logsI stableI snapsI transI : GoInterfaceOk) (rpcCh : Loc)
    (γ : GNames) (i : SID) (rc : RCtx GF) (eof : GoInterface) (X : SrvDur) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ cp ↦ c ∗ ⌜cfgOk c i⌝ ∗
     isFSM fsmI γ i rc.fsmOwn rc.respP rc.snapP ∗ ⌜fsmNotBatching fsmI⌝ ∗
     isLogStore logsI rc.ownL (logWin γ rc i) ∗ ⌜go.typeSetContains logsI.ty MonotonicLogStore.ty = false⌝ ∗
     isStableStore stableI rc.ownS (stWin γ rc i) ∗ isSnapStore snapsI rc.ownSS eof (snapWin γ rc i) ∗
     globalAddr io.EOF ↦□ eof ∗
     isTransport transI γ rc.snapP i rpcCh ∗ ⌜go.typeSetContains transI.ty WithPreVote.ty = true⌝ ∗
     Inv γ ∗ isSrv γ i ∗ srvDurInvRaw γ rc i ∗
     srvVP rc X.s X.tp X.dp ∗ stVS rc X.D X.A.staged ∗ termV rc X.s.term ∗ cidxV rc X.s.cidx ∗
     monoNatAuthOwn rc.dur.applied 1 0 ∗ monoNatAuthOwn rc.dur.comp (1 : Qp).half X.c ∗
     ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
     ghostVar rc.dur.pw 1 (none : Option Pend) ∗
     dghostVar rc.dur.boot (DFrac.own (1 : Qp).half) (some (X.A, X.lat)) ∗
     ⌜RecOk X⌝ ∗ (⌜X.lat = none⌝ ∨ isLogStoreFirst logsI rc.ownL) ∗
     ⌜γ.cv = cfgDec γ.srvs ∧ ∃ ss, srvsOk γ ss ∧ γ.g = genesisOf ss⌝ ∗ rc.fsmOwn 0 ∗ rtok tid }}
    (App (App (App (App (App (App (Val (@! github_com.hashicorp.raft.NewRaft)) (Val #cp)) (Val #(GoInterface.ok fsmI))) (Val #(GoInterface.ok logsI))) (Val #(GoInterface.ok stableI))) (Val #(GoInterface.ok snapsI))) (Val #(GoInterface.ok transI)))
  {{ (r : Loc), RET (PairV #r #interface.nil);
      (∃ names : RNames, isRaft r γ { rc with names := names } i) ∗ cp ↦ c ∗ rtok tid }}

end spec

end Perennial
