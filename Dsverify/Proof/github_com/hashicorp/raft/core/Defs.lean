/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/core/Defs.lean (241f27e).
-/
/-
Raft-internal interface (notes/raft-iface.md, notes/raft-iface-lean.md): the predicates shared by
raft's subsystems (core, api, main, repl, fsm).

* `RNames`: the ghost names of one server's raft-local ghost state; `RCtx`: those and the client
  predicates fixed at `NewRaft` (the log/stable store handles, the FSM state and responses).
* `cfgOk`, `cfgVal`, `cfgAtIs`, `cfgOpt` (stage 4; stage 3: `cfgIs`, the bootstrap configuration):
  the `Config` and the `Configuration` values (a valid configuration; the configuration entry at an
  index of a log; the latest configuration cell's);
* the cells (`termCell`, `cidxCell`, `stateCell`, `appliedCell`, ...), the crash invariant
  (hraft_robust L0: `srvDurInv`, which replaces `logCell` and `snapCell`), the locks
  (`lastLockInv`, `rwLock`), the routines group (`rgOk`);
* futures: `deferResp`/`deferDone` (the responder side of a `deferError`), `futQ` (what a
  client's future answers), `applyP` (a future on `applyCh`), `futResp` (a dispatched future),
  `futureOwn`/`futDone`/`futResponse` (the client's side);
* the FSM batch channel: `fsmBatchP`, `fsmP`, `batchEnd`, `fsmProd` (the producer's state);
* observers: `obsArg`, `filterOk`, `obsOk`;
* `isRaft` (sealed, persistent), `mainOwn`, `leaderStateAny`, `leaderOwn`, `commitInv`,
  `isCommitment`, `replMain`, `replOwn`.

Elimination laws are in `core/Laws.lean`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net
public import Dsverify.Proof.github_com.hashicorp.raft.iface.FSM
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Ops
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Cfg
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Proof.sync.RWMutexThreads
public import Perennial.Proof.sync.WaitGroupDefs
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.TokSet
public import Perennial.Proof.ThreadPool
public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QPool
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

/-! ## Ghost names and the per-server context -/

/-- The ghost names of one server's raft-local ghost state. -/
structure RNames where
  /-- `ghostVar RaftState`: the `state` cell's value (cell ½, main goroutine ½). -/
  state : GName
  /-- `ghostVar (Nat × Nat)`: `lastLogIndex/Term` (`lastLock` ½, main goroutine ½). -/
  lastLog : GName
  /-- (hraft_robust, R5 Q8) `dghostVar (Option (w64 × w64 × w64 × w64))`: `lastLock`'s fields pinned
  during `NewRaft` (`some`, ½ the lock's invariant, ½ `NewRaft`); then `none`, discarded (in `raftCells`). -/
  llb : GName
  /-- the FSM batch channel `fsmMutateCh` (SPSC: main goroutine → FSM goroutine). -/
  fsmCh : SpscNames
  /-- `ghostMap Nat Nat` (persistent elements): batch `n` of `fsmMutateCh` ends at index `k`. -/
  batch : GName
  /-- (stage 2) `ghostMap (Loc × SID) Unit`: the vote tokens of registered verify futures (one per
  future and voter, exclusive; authority held by the main goroutine). -/
  vtok : GName
  /-- (stage 2) `ghostMap Loc (Nat × Snap)` with persistent elements: each registered verify
  future's registration (its leader's term and the registration snapshot, `vregIs`). -/
  vreg : GName
  /-- (stage 2) `ghostMap Loc Unit`: the registered verify futures not yet received back from
  `vote` (`backTok`, exclusive: it travels with the voted future; authority: main goroutine). -/
  vlive : GName
  /-- (stage 2) `ghostMap Loc Unit`: the registered futures in the leader's notify set (`nmTok`,
  held by its entries; authority: main goroutine). -/
  vnm : GName

/-- (hraft_robust L0, R1 §1.3) **The ghost names of one generation's crash state**, allocated
before the generation runs (`raft_arm`, at boot: the crash wand is built before `NewRaft`), so that
`srvDurInv` (and hence `isRaft`) can name them. (The names `applied`, `comp` and `pend` moved here
from `RNames`, since `durBody` mentions them.)
* `sv`, `st`: `ghostVar (SState × Option TermPend × Option DiscPend)`, `ghostVar StableAbs`: the main
  goroutine's views of its protocol state (with the pending term step and discard, `srvVP`; none
  outside those phases, `srvV`) and of the stable store's contents with the log store's staged commit
  index (`stV`, `stVS`: `ghostVar (StableAbs × w64)`; ½ each, the other ½ in `durBody`);
* `tv`, `cv`: `ghostVar Nat`: the `currentTerm` and `commitIndex` atomics' views (`termV`,
  `cidxV`; ½ in `termCell`/`cidxCell`, ½ in `durBody`);
* `applied`: `mono_nat`, the `lastApplied` cell's value (authority: cell ½, main goroutine ½; lower
  bounds `applLb`);
* `comp`: `mono_nat`, the compaction frontier (authority: ½ the main goroutine's, ½ `durBody`'s, at
  `X.c`, so a compaction's `compLb x` bounds `x ≤ X.c`, below a pending discard's index: R4b Q4);
* `pend`: `ghostVar (Option (Nat × Nat × GoString))`, the install pending between the install's
  `sink.Close()` and the restore's answer (½ `durBody`, ½ the main goroutine, lent to the restore);
* `tok`: the crash token of `srvDurInv` (`srvCrashTok`, `ghostVar tok 1 ()`, held by the crash
  wand). -/
structure DurNames where
  sv : GName
  st : GName
  tv : GName
  cv : GName
  applied : GName
  comp : GName
  pend : GName
  tok : GName
  /-- (hraft_robust, R2 req. 2) `ghostVar (Option Pend)`: the main goroutine's pending write (`none`
  between writes; `some p` from a write's start to its commit, ½ lent in its window `winRes`). -/
  pw : GName
  /-- (hraft_robust, R5 Q0) `dghostVar (Option (LogAbs × SnapLatest))`: the boot pin. From the arm to the
  end of `NewRaft`, `some (A, lat)` (½ `durBody`, ½ `NewRaft`): the stores' state the restore reads is the
  arm-time one; then `none`, discarded (`bootOver`, in `srvDurInv`). -/
  boot : GName
  /-- (hraft_robust, R4b) `mono_nat`: the latest snapshot's index (`latIdxD`; authority in `durBody`,
  lower bounds `latLb`: a closed own snapshot's index, which its compaction then lends). -/
  lat : GName

/-- One server's context: its ghost names and the client predicates fixed at `NewRaft`. -/
structure RCtx [GooseExts] (GF : BundledGFunctors) where
  /-- the log store's handle (`isLogStore _ ownL`; stage 3: over a partial map, `LogAbs`) -/
  ownL : LogAbs → IProp GF
  /-- (stage 3) the snapshot store's handle (`isSnapStore _ ownSS`) -/
  ownSS : SnapLatest → IProp GF
  /-- (stage 3) the meaning of a snapshot's bytes (`isFSM`; the same at every server) -/
  snapP : Nat → List w8 → IProp GF
  /-- the stable store's handle (`isStableStore _ ownS`) -/
  ownS : StableAbs → IProp GF
  /-- the FSM's state, by the index of the last applied command (`isFSM`) -/
  fsmOwn : Nat → IProp GF
  /-- the meaning of a command's response (`isFSM`) -/
  respP : Nat → GoInterface → IProp GF
  names : RNames
  /-- (hraft_robust L0) this generation's crash-state names (`srvDurInv`) -/
  dur : DurNames

/-! ## Namespaces -/

def raftN : Namespace := nroot.@"raft"
def termN : Namespace := raftN.@"term"
def cidxN : Namespace := raftN.@"cidx"
def logN : Namespace := raftN.@"log"
def snapN : Namespace := raftN.@"snap"
/-- (hraft_robust L0) `srvDurInv`'s namespace (replaces `logN`'s and `snapN`'s cells). -/
def durN : Namespace := raftN.@"dur"
def stateN : Namespace := raftN.@"state"
def appliedN : Namespace := raftN.@"applied"
def cftN : Namespace := raftN.@"cft"
def ltipN : Namespace := raftN.@"ltip"
def nextIdxN : Namespace := raftN.@"nextIndex"
def stopN : Namespace := raftN.@"stop"
def rgN : Namespace := raftN.@"rg"
def leaderLockN : Namespace := raftN.@"leaderLock"
def lastContactLockN : Namespace := raftN.@"lastContactLock"
def observersLockN : Namespace := raftN.@"observersLock"
def peerLockN : Namespace := raftN.@"peerLock"
def replContactLockN : Namespace := raftN.@"replContactLock"

/-! ## Pure data: configurations -/

section pure
variable [GooseExts]

-- (stage 3) `le64`, `encodeServers`, `srvsOk` moved to `iface/Net.lean` (the install request
-- carries the encoded bootstrap configuration).

/-- The genesis entry of the bootstrap servers `ss`. -/
def genesisOf (ss : List Server) : Entry := ⟨1, kConfig, encodeServers ss⟩

/-- (stage 4) The IDs of the servers of the latest configuration entry of `L` (a configuration over the
servers `S`; `[]` without one): the
replication goroutines a leader with log `L` runs (`startStopReplication`, with its own ID left
out). -/
def cfgIdsOf (S : List SID) (L : RLog) : List SID :=
  match ent L (lastCfgIdx L) with
  | some e => srvIds (cfgServers S e.data)
  | none => []

/-- The Raft state values. -/
def stFollower : w32 := W32 0
def stCandidate : w32 := W32 1
def stLeader : w32 := W32 2

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The `Config` the server runs with (what `ValidateConfig` accepts, and the choices of the
verified scope): protocol version 3, local id `i`, no notify channel, no batched apply channel,
pre-vote on, startup not skipped, no restore of committed logs, no snapshot restore at start,
`1 ≤ MaxAppendEntries ≤ 64`, timeouts as `ValidateConfig` wants. (Stage 3: any
`SnapshotThreshold` and `TrailingLogs`: servers snapshot and compact.) (Stage 4) A removed server keeps
running (`ShutdownOnRemove` off: a leader removed from the configuration steps down to `Follower`). -/
def cfgOk (c : Config) (i : SID) : Prop :=
  c.ProtocolVersion' = W64 3 ∧ c.LocalID' = i ∧ i ≠ [] ∧ c.NotifyCh' = chan.nil ∧
  c.BatchApplyCh' = false ∧ c.PreVoteDisabled' = false ∧ c.skipStartup' = false ∧
  c.RestoreCommittedLogs' = false ∧ c.NoSnapshotRestoreOnStart' = false ∧
  1 ≤ uint.nat c.MaxAppendEntries' ∧ uint.nat c.MaxAppendEntries' ≤ 64 ∧
  5000000 ≤ sint.Z c.HeartbeatTimeout' ∧ sint.Z c.HeartbeatTimeout' ≤ sint.Z c.ElectionTimeout' ∧
  1000000 ≤ sint.Z c.CommitTimeout' ∧ 5000000 ≤ sint.Z c.SnapshotInterval' ∧
  5000000 ≤ sint.Z c.LeaderLeaseTimeout' ∧
  sint.Z c.LeaderLeaseTimeout' ≤ sint.Z c.HeartbeatTimeout' ∧
  sint.Z c.ElectionTimeout' < 2 ^ 61 ∧ sint.Z c.HeartbeatTimeout' < 2 ^ 61 ∧
  sint.Z c.CommitTimeout' < 2 ^ 61 ∧ sint.Z c.SnapshotInterval' < 2 ^ 61 ∧
  c.ShutdownOnRemove' = false

/-- (stage 4; stage 3: `cfgIs γ c`, the bootstrap configuration) **The `Configuration` value `c` is the
valid configuration `ss`** of protocol `γ` (`srvsOk`; its servers' slice read-only). -/
def cfgVal (γ : GNames) (c : Configuration) (ss : List Server) : IProp GF :=
  iprop(c.Servers' ↦*□ ss ∗ ⌜srvsOk γ ss⌝)

instance cfgVal_persistent γ c ss : Persistent (cfgVal (GF := GF) γ c ss) := by
  unfold cfgVal; infer_instance

/-- (stage 4) **`c` is the configuration at index `p` of the log `L`** (persistent): `p = 0` and `c` has
no servers (a log without a configuration entry: a non-member's), or the configuration entry at
`p ≥ 1` of `L` encodes the valid configuration of `c` (`DecodeConfiguration` of its data). What the
main goroutine's `configurations` hold (`mainOwnAt`). -/
def cfgAtIs (γ : GNames) (L : RLog) (p : Nat) (c : Configuration) : IProp GF :=
  iprop((⌜p = 0⌝ ∗ c.Servers' ↦*□ ([] : List Server)) ∨
    ∃ (ss : List Server) (e : Entry), cfgVal γ c ss ∗
      ⌜1 ≤ p ∧ ent L p = some e ∧ e.kind = kConfig ∧ e.data = encodeServers ss⌝)

instance cfgAtIs_persistent γ L p c : Persistent (cfgAtIs (GF := GF) γ L p c) := by
  unfold cfgAtIs; infer_instance

/-- (stage 4) The configuration `c` has no servers or is a valid one (persistent): the latest
configuration cell's value (a non-member's is empty until it learns one), `GetConfiguration`'s. -/
def cfgOpt (γ : GNames) (c : Configuration) : IProp GF :=
  iprop(∃ ss : List Server, c.Servers' ↦*□ ss ∗ ⌜ss = [] ∨ srvsOk γ ss⌝)

instance cfgOpt_persistent γ c : Persistent (cfgOpt (GF := GF) γ c) := by
  unfold cfgOpt; infer_instance

/-- `DefaultConfig()`'s value. -/
def defaultConfig : Config :=
  Config.mk (W64 3) (W64 1000000000) (W64 1000000000) (W64 50000000) (W64 64) false true
    (W64 10240) (W64 120000000000) (W64 8192) (W64 500000000) [] chan.nil false false false false
    false

/-- The `RaftState` value `Leader` as an observation's `Data`. -/
def leaderObs : GoInterface := interface.mkOk RaftState.ty #stLeader

/-- An `atomic.Value` read-only forever is persistent. -/
instance ownValue_discard_persistent (u : Loc) (x : GoInterface) :
    Persistent (sync.atomic.ownValue (GF := GF) u DFrac.discard x) := by
  rw [sync.atomic.ownValue_unseal]; unfold sync.atomic.ownValueDef; infer_instance

/-! ## Cells (atomics with invariants) -/

/-- (hraft_robust L0, R1 §2.3) A term step made durable (`SetUint64(CurrentTerm)` synced) but not yet
taken (the `currentTerm` atomic's store, where `setTerm_upd`/`electTerm_upd` fire): adopt `t`, or
start an election (`electSelf`, the term `s.term + 1`). -/
inductive TermPend where
  | set (t : Nat)
  | elect
  deriving DecidableEq

instance termPend_countable : Pos.Countable TermPend :=
  Pos.Countable.ofInjective
    (fun p => match p with | .set t => Pos.Countable.encode (some t) | .elect => Pos.Countable.encode (none : Option Nat))
    (by
      intro a b h
      cases a <;> cases b <;> simp only at h <;> first | rfl | (have h := Pos.encode_inj h; simp_all))

/-- (hraft_robust L0, R1 §6.2, fix 2) An install's discard pending: the snapshot `(x, st)` from the
leader `ℓ` is durable (its sink closed), the log not yet discarded (`installDiscard_upd`). -/
structure DiscPend where
  x : Nat
  st : Nat
  ℓ : SID
  deriving DecidableEq

instance discPend_countable : Pos.Countable DiscPend :=
  Pos.Countable.ofInjective (fun d => Pos.Countable.encode (d.x, d.st, d.ℓ))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3; rfl)

/-- (hraft_robust L0) **The main goroutine's view of its protocol state** `s` (½; `durBody` holds the
other half, at the crash state's `X.s`). Replaces `srvOwn` in `mainOwnAt`: `srvOwn` itself lives in
`srvDurInv`, which survives a crash. -/
def srvV (rc : RCtx GF) (s : SState) : IProp GF :=
  ghostVar rc.dur.sv (1 : Qp).half (s, (none : Option TermPend), (none : Option DiscPend))

/-- (hraft_robust L0) The main goroutine's view inside a pending phase: its state `s`, with the term
step `tp` (`setCurrentTerm`, between `SetUint64` and the atomic store) and the discard `dp` (an install,
between its sink's `Close` and its log discard) pending. `srvV rc s` is `srvVP rc s none none`. -/
def srvVP (rc : RCtx GF) (s : SState) (tp : Option TermPend) (dp : Option DiscPend) : IProp GF :=
  ghostVar rc.dur.sv (1 : Qp).half (s, tp, dp)

/-- (hraft_robust L0) The main goroutine's view of the stable store's contents (½; the other half in
`durBody`). Replaces `rc.ownS` in `mainOwnAt`. -/
def stV (rc : RCtx GF) (D : StableAbs) : IProp GF :=
  iprop(∃ g : w64, ghostVar rc.dur.st (1 : Qp).half (D, g))

/-- (hraft_robust L0, R4b Q1) `stV` with the log store's staged commit index `g` (`LogAbs.staged`):
only the main goroutine stages (`StageCommitIndex`), so its view pins it; a `StoreLogs` writes it
(`ci := staged`), whose atomic update must then show it durable (`durBody`'s `ci ≤ dur`). -/
def stVS (rc : RCtx GF) (D : StableAbs) (g : w64) : IProp GF := ghostVar rc.dur.st (1 : Qp).half (D, g)

/-- (hraft_robust L0) The `currentTerm` atomic's view of the protocol's term (½; the other half in
`durBody`, at `X.s.term`, where `termCouple` lives). -/
def termV (rc : RCtx GF) (t : Nat) : IProp GF := ghostVar rc.dur.tv (1 : Qp).half t

/-- (hraft_robust L0) The `commitIndex` atomic's view of the protocol's `cidx` (½; the other half in
`durBody`, at `X.s.cidx`, where `cidxCouple` lives). -/
def cidxV (rc : RCtx GF) (c : Nat) : IProp GF := ghostVar rc.dur.cv (1 : Qp).half c

/-- The `currentTerm` atomic, coupled with the protocol's term of `i` (hraft_robust L0: through the
view `termV`; `termCouple` is in `srvDurInv`). -/
def termCell (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  inv termN iprop(∃ t : w64,
    r.[Raft, go!"raftState"].[raftState, go!"currentTerm"] ↦ t ∗ termV rc (uint.nat t))

/-- The `commitIndex` atomic, coupled with the protocol's `cidx` of `i` (hraft_robust L0: through the
view `cidxV`; `cidxCouple` is in `srvDurInv`). -/
def cidxCell (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  inv cidxN iprop(∃ c : w64,
    r.[Raft, go!"raftState"].[raftState, go!"commitIndex"] ↦ c ∗ cidxV rc (uint.nat c))

/-- (stage 3) The compaction frontier is at least `c` (persistent). -/
def compLb (rc : RCtx GF) (c : Nat) : IProp GF := monoNatLbOwn rc.dur.comp c

instance compLb_persistent rc c : Persistent (compLb (GF := GF) rc c) := by
  unfold compLb; infer_instance

-- (hraft_robust L0) `logCell` (the log store's coupling invariant) is gone: its body is
-- `durBody`'s (`logOk`), in `srvDurInv`; the leader's pending appends (`ps`, `logPend`) are gone with
-- it (`leaderAppend*` fire at `StoreLogs`' commit point).

/-- The `state` atomic (the main goroutine holds the other half of the ghost variable). -/
def stateCell (r : Loc) (rc : RCtx GF) : IProp GF :=
  inv stateN iprop(∃ st : w32,
    r.[Raft, go!"raftState"].[raftState, go!"state"] ↦ st ∗
    ghostVar rc.names.state (1 : Qp).half st ∗
    ⌜st = stFollower ∨ st = stCandidate ∨ st = stLeader⌝)

/-- The `lastApplied` atomic (the main goroutine holds the other half of the authority). -/
def appliedCell (r : Loc) (rc : RCtx GF) : IProp GF :=
  inv appliedN iprop(∃ a : w64,
    r.[Raft, go!"raftState"].[raftState, go!"lastApplied"] ↦ a ∗
    monoNatAuthOwn rc.dur.applied (1 : Qp).half (uint.nat a))

/-- (stage 3) `lastApplied` is at least `x` (persistent). -/
def applLb (rc : RCtx GF) (x : Nat) : IProp GF := monoNatLbOwn rc.dur.applied x

instance applLb_persistent rc x : Persistent (applLb (GF := GF) rc x) := by
  unfold applLb; infer_instance

/-- (stage 3) **A snapshot `(s, st)` installed while `i` followed the term `t`** (persistent): the
install was valid in `t` (`aeValid γ t s st [] s`), sent by `t`'s leader `ℓ ≠ i`, and `i` reached `t`.
A later leader `i` of `T` can send it (`gprot.snapValid_follow`). -/
def snapFollow (γ : GNames) (i : SID) (s st : Nat) : IProp GF :=
  iprop(∃ (t : Nat) (ℓ : SID), aeValid γ t s st [] s ∗ leaderIs γ t ℓ ∗ termLb γ i t ∗
    ⌜ℓ ≠ i ∧ 1 ≤ s⌝)

instance snapFollow_persistent γ i s st : Persistent (snapFollow (GF := GF) γ i s st) := by
  unfold snapFollow; infer_instance

/-- `candidateFromLeadershipTransfer` holds some bool (stage 2: `timeoutNow` stores `true`,
`runCandidate` resets it). It skips the pre-vote, sets the `RequestVote`'s `LeadershipTransfer`,
and makes a candidate *not* step down on a valid AppendEntries of its own term (`appendEntries`):
the candidate then stores entries while staying Candidate, which `appendEntries`' and
`processRPC`'s posts admit (with the term's other leader, so `runCandidate` cannot win after its
log changed). No invariant of the cell's value is needed. -/
def cftCell (r : Loc) : IProp GF :=
  inv cftN iprop(∃ b : Bool,
    sync.atomic.ownBool (r.[Raft, go!"candidateFromLeadershipTransfer"]) (DFrac.own 1) b)

/-- `leaderState.leadershipTransferInProgress` holds some value (stage 2: the leader loop's
leadership transfer stores `1`, its goroutine `0`; readers compare it with `1`, no fact needed). -/
def ltipCell (r : Loc) : IProp GF :=
  inv ltipN iprop(∃ v : w32,
    r.[Raft, go!"leaderState"].[leaderState, go!"leadershipTransferInProgress"] ↦ v)

instance termCell_persistent r γ rc i : Persistent (termCell (GF := GF) r γ rc i) := by
  unfold termCell; infer_instance
instance cidxCell_persistent r γ rc i : Persistent (cidxCell (GF := GF) r γ rc i) := by
  unfold cidxCell; infer_instance
instance stateCell_persistent r rc : Persistent (stateCell (GF := GF) r rc) := by
  unfold stateCell; infer_instance
instance appliedCell_persistent r rc : Persistent (appliedCell (GF := GF) r rc) := by
  unfold appliedCell; infer_instance
instance cftCell_persistent r : Persistent (cftCell (GF := GF) r) := by
  unfold cftCell; infer_instance
instance ltipCell_persistent r : Persistent (ltipCell (GF := GF) r) := by
  unfold ltipCell; infer_instance

/-! ## Locks -/

/-- The `lastLock` invariant: the last log entry (with the lock's half of `γr.lastLog`); (stage 3)
the last snapshot `(si, st)` (`setLastSnapshot`: by the snapshot goroutine after its sink closed, by
the install after `setLastApplied`): none, or a committed entry (`CIdx`) at most `lastApplied`
(`applLb`), durable at `i` (the snapshot goroutine's: from the configurations answer) or installed while
`i` followed (the install's: `snapFollow`; its durable prefix reaches `si` at the install's log step,
after this store). So `si ≤ lastApplied ≤ dur ≤ |log|` for the main goroutine (`mainOwnAt`), and
`getLastEntry`/`getLastIndex` return the last log entry (review T1-1, check N1). -/
def lastLockInv (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop(∃ li lt si st : w64,
    r.[Raft, go!"raftState"].[raftState, go!"lastLogIndex"] ↦ li ∗
    r.[Raft, go!"raftState"].[raftState, go!"lastLogTerm"] ↦ lt ∗
    r.[Raft, go!"raftState"].[raftState, go!"lastSnapshotIndex"] ↦ si ∗
    r.[Raft, go!"raftState"].[raftState, go!"lastSnapshotTerm"] ↦ st ∗
    ghostVar rc.names.lastLog (1 : Qp).half (uint.nat li, uint.nat lt) ∗
    (⌜si = W64 0⌝ ∨ ∃ e : Entry, CIdx γ (uint.nat si) e ∗ ⌜e.term = uint.nat st⌝ ∗
      applLb rc (uint.nat si) ∗
      (durLb γ i (uint.nat si) ∨ snapFollow γ i (uint.nat si) (uint.nat st))) ∗
    (dghostVar rc.names.llb DFrac.discard (none : Option (w64 × w64 × w64 × w64)) ∨
      dghostVar rc.names.llb (DFrac.own (1 : Qp).half) (some (li, lt, si, st))))

/-- A `sync.RWMutex` at `rw` guarding the fractional `P`: writers use the persistent guard,
readers borrow a reader token from a quarter thread pool (namespace `N`) with their quarter
thread token `rtok tid` (`HrVerify/Proof/Threads/QPool.lean`, decision D15). -/
def rwLock (N : Namespace) (rw : Loc) (P : Qp → IProp GF) : IProp GF :=
  iprop(∃ γp : GName, sync.isRWMutexGuard rw P ∗
    qpool.isQPool N γp (sync.ownRWMutex rw P))

instance rwLock_persistent N rw P : Persistent (rwLock (GF := GF) N rw P) := by
  unfold rwLock; infer_instance

/-- `leaderLock`'s resource: `leaderAddr`, `leaderID` (no facts). -/
def leaderLockP (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (a : ServerAddress) (id : ServerID),
    r.[Raft, go!"leaderAddr"] ↦{DFrac.own q} a ∗ r.[Raft, go!"leaderID"] ↦{DFrac.own q} id)

/-- `lastContactLock`'s resource: `lastContact` (no facts). -/
def lastContactP (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ t : time.Time, r.[Raft, go!"lastContact"] ↦{DFrac.own q} t)

/-! ## The routines group -/

/-- The routines group's invariant: the `WaitGroup` counter `n` is the number of goroutines started
by `goFunc` and not done; the quarter bank `γb` (`HrVerify/Proof/Threads/QBank.lean`) holds one
quarter thread token per such goroutine (its caller's, between `Add` and the `go` statement; then
one of the goroutine's fresh slot, until its `Done`; each goroutine holds the slip for it). With
the caller's own quarter, `n + 1 ≤ 4 * (threadBound GF - 1)` (decision D15; hub request CORE-1). -/
def rgInv (γwg : sync.WaitGroupNames) (γb : GName) : IProp GF :=
  iprop(∃ n : Nat,
    sync.ownWaitGroup γwg (W32 n) ∗ sync.ownWaitGroupWaiters γwg 0 ∗ qbank γb n)

/-- The routines group `r.routinesGroup` (and the thread bound `2^28` its counter needs). -/
def rgOk (r : Loc) : IProp GF :=
  iprop(∃ (γwg : sync.WaitGroupNames) (γb : GName),
    sync.isWaitGroup (r.[Raft, go!"raftState"].[raftState, go!"routinesGroup"]) γwg (rgN.@"wg") ∗
    inv (rgN.@"inv") (rgInv γwg γb) ∗ ⌜threadBound GF ≤ 2 ^ 28⌝)

instance rgOk_persistent r : Persistent (rgOk (GF := GF) r) := by
  unfold rgOk; infer_instance

/-! ## Channels -/

/-- A channel that is never sent on and never closed (a bag with predicate `False`). -/
def deadChan (V : Type) [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] (ch : Loc) :
    IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag (V := V) γc ch (fun _ => iprop(False)))

instance deadChan_persistent V [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] ch :
    Persistent (deadChan (GF := GF) V ch) := by
  unfold deadChan; infer_instance

/-- A notification channel (`chan struct{}`, a bag with no content). -/
def notifyChan (ch : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag (V := Unit) γc ch (fun _ => iprop(True)))

instance notifyChan_persistent ch : Persistent (notifyChan (GF := GF) ch) := by
  unfold notifyChan; infer_instance

/-! ## Futures -/

/-- **The responder side** of the `deferError` at `de`, whose answer must satisfy `Q`: its
`errCh` (read-only), and, if it is a channel (`init` was called), the right to send on it once
(an SPSC channel whose first value satisfies `Q`) and the `responded` flag. A `nil` `errCh`
(a future made without `init`, e.g. the leader's no-op) makes `respond` a no-op. -/
def deferResp (de : Loc) (Q : GoInterface → IProp GF) : IProp GF :=
  iprop(∃ ch : Loc, de.[deferError, go!"errCh"] ↦□ ch ∗
    (⌜ch = chan.nil⌝ ∨
     ∃ γe : SpscNames, ⌜ch ≠ chan.nil⌝ ∗
       isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
       spscProducer γe ([] : List GoInterface) ∗ de.[deferError, go!"responded"] ↦ false))

/-- The responder side after `respond`. -/
def deferDone (de : Loc) : IProp GF :=
  iprop(∃ ch : Loc, de.[deferError, go!"errCh"] ↦□ ch ∗
    (⌜ch = chan.nil⌝ ∨ de.[deferError, go!"responded"] ↦ true))

/-- **The client side** of the `deferError` at `de` with answer predicate `Q`: the right to
receive the answer once (`Error()`), its `err` field (still nil) and its `ShutdownCh` (nil:
`ApplyLog` does not set it; stage 3: or the never-closed `shutdownCh`, which the install's restore
future and takeSnapshot's configurations future set; either way the shutdown branch of `Error()`'s
select never fires). -/
def deferWait (de : Loc) (Q : GoInterface → IProp GF) : IProp GF :=
  iprop(∃ (ch : Loc) (γe : SpscNames), de.[deferError, go!"errCh"] ↦□ ch ∗ ⌜ch ≠ chan.nil⌝ ∗
    isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
    spscConsumer γe ([] : List GoInterface) ∗
    de.[deferError, go!"err"] ↦ interface.nil ∗
    (∃ sc : Loc, de.[deferError, go!"ShutdownCh"] ↦□ sc ∗ (⌜sc = chan.nil⌝ ∨ deadChan Unit sc)))

/-- **What a client's future answers** (the future `f` of command data `d`, whose operation token
is `opTok γ d n`):
* `ErrNotLeader` / `ErrLeadershipTransferInProgress`: the command was never dispatched; the token
  comes back;
* `nil`: the FSM applied it at index `k` (a committed command with data `d`) with response `r`,
  and the future's `response` field (holding `r`) goes to the client;
* `ErrLeadershipLost`: it was dispatched (it may still commit); nothing. -/
def futQ (γ : GNames) (rc : RCtx GF) (f : Loc) (d : List w8) (n : Nat) (err : GoInterface) :
    IProp GF :=
  iprop(((isRaftErr .notLeader err ∨ isRaftErr .leadershipTransferInProgress err) ∗ opTok γ d n) ∨
    (⌜err = interface.nil⌝ ∗ ∃ (k : Nat) (e : Entry) (r : GoInterface),
      CIdx γ k e ∗ ⌜e.kind = kCommand ∧ e.data = d⌝ ∗ rc.respP k r ∗
      f.[logFuture, go!"response"] ↦ r) ∨
    isRaftErr .leadershipLost err)

/-- (stage 2) **What a barrier's leader knows at dispatch** (persistent): the leader `i` of `T`
appended the barrier `e` (of term `T`) at `b`, past `T`'s election part (`len0 T = n0 < b`) and
after the client's snapshot `sc` (`llog T` was shorter than `b` at `sc`), while in `T` at a
snapshot `st` after `sc`; (API-1) the client's snapshot `sc` itself (`histLb`, for
`gprot.barrier_bound`). -/
def barrierDisp (γ : GNames) (i : SID) (sc : Snap) (b : Nat) (e : Entry) : IProp GF :=
  iprop(∃ (n0 : Nat) (st : Snap), leaderIs γ e.term i ∗ len0Is γ e.term n0 ∗ histLb γ st ∗
    histLb γ sc ∗ ⌜n0 < b ∧ sc.llen e.term < b ∧ snapLe sc st ∧ st.term i = e.term⌝)

/-- (stage 2) **What a barrier's `Error()` returning `nil` means** (`Raft.Barrier`, the client's
snapshot `sc` taken before the call): `i` led `T` (in `T` at a snapshot after `sc`), its barrier
at `b` (past `T`'s election part, `len0 T = n0 < b`) was appended after `sc` and committed, every
voter's durable prefix at `sc` is below `b` (`gprot.barrier_bound`), and the FSM had processed
`s ≥ b` (`fsmAt`: the FSM goroutine answers a barrier after applying every entry before it). -/
def barrierOk (γ : GNames) (rc : RCtx GF) (i : SID) (sc : Snap) : IProp GF :=
  iprop(∃ (T n0 b s : Nat) (st : Snap), leaderIs γ T i ∗ len0Is γ T n0 ∗ histLb γ st ∗
    ⌜snapLe sc st ∧ st.term i = T ∧ n0 < b ∧ b ≤ s ∧ ∀ i' ∈ γ.srvs, sc.dur i' < b⌝ ∗
    fsmAt γ rc.respP i s)

/-- (stage 2) A barrier future's answer: an error (no facts) or `nil` with `barrierOk`. -/
def barrierQ (γ : GNames) (rc : RCtx GF) (i : SID) (sc : Snap) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ barrierOk γ rc i sc)

/-- **A client's future on `applyCh`** (`applyP`), as `ApplyLog` sends it: its fields (the `log`
a `LogCommand` with data `d` and its extensions, read-only, index and term still to be set by the
dispatch), the responder side of its `deferError` answering `futQ`, and the operation token; or
(stage 2) as `Barrier` sends it: a `LogBarrier` with no data, answering `barrierQ` for the
client's snapshot `sc`. -/
def applyP (γ : GNames) (rc : RCtx GF) (i : SID) (f : Loc) : IProp GF :=
  iprop((∃ (d : List w8) (n : Nat) (lv : Log) (t : time.Time),
    (f.[logFuture, go!"log"]) ↦ lv ∗ ⌜lv.Type' = W8 0⌝ ∗ lv.Data' ↦*□ d ∗
    (∃ x : List w8, lv.Extensions' ↦*□ x) ∗
    f.[logFuture, go!"response"] ↦ interface.nil ∗ f.[logFuture, go!"dispatch"] ↦ t ∗
    deferResp (f.[logFuture, go!"deferError"]) (futQ γ rc f d n) ∗ opTok γ d n) ∨
   (∃ (lv : Log) (t : time.Time) (sc : Snap),
    (f.[logFuture, go!"log"]) ↦ lv ∗ ⌜lv.Type' = W8 4⌝ ∗ lv.Data' ↦*□ ([] : List w8) ∗
    (∃ x : List w8, lv.Extensions' ↦*□ x) ∗
    f.[logFuture, go!"response"] ↦ interface.nil ∗ f.[logFuture, go!"dispatch"] ↦ t ∗
    histLb γ sc ∗ deferResp (f.[logFuture, go!"deferError"]) (barrierQ γ rc i sc)))

/-- (stage 4) **What a configuration change future's `Error()` answers** (`AddVoter`, `AddNonvoter`,
`DemoteVoter`, `RemoveServer`; persistent): `nil` (the change committed and the FSM goroutine
processed it), a raft error (`ErrNotLeader`, `ErrLeadershipLost`, `ErrLeadershipTransferInProgress`,
`ErrEnqueueTimeout`, ...) or an error value with a callable `Error()` (`nextConfiguration`'s:
`checkConfiguration` refuses a change leaving no voter), an `errors.New` leaf (`*errors.errorString`:
`fmt.Errorf`'s model; API-S4-1). The configuration client (hr3's `reconfigure`) only compares it with
`ErrNotLeader` (`==` on interfaces steps on a pointer value only). -/
def cfgChangeQ (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (∃ c : RaftErr, isRaftErr c err) ∨
    (errOk err ∗ ⌜∃ x : Loc, err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝))

/-- (stage 4) **A configuration change request in scope** (`configurationChangeRequest`): `AddVoter`,
`AddNonvoter`, `DemoteVoter` or `RemoveServer` (no `Promote`: no staging servers) of one of the
servers `γ.srvs`, added with its own ID as its address; any `prevIndex`; (hub LH1) the ID non-empty and
shorter than `2^63`, fewer than `2^32` servers (what `nextConfiguration` needs to keep a valid
configuration when it adds the server). -/
def cfgReqOk (γ : GNames) (rq : configurationChangeRequest) : Prop :=
  (rq.command' = W8 0 ∨ rq.command' = W8 1 ∨ rq.command' = W8 2 ∨ rq.command' = W8 3) ∧
  (rq.serverID' : List w8) ∈ γ.srvs ∧
  ((rq.command' = W8 0 ∨ rq.command' = W8 1) → rq.serverAddress' = rq.serverID') ∧
  ((rq.serverID' : List w8) ≠ [] ∧ rq.serverID'.length < 2 ^ 63 ∧ γ.srvs.length < 2 ^ 32)

/-- (stage 4) **A configuration change future** as `requestConfigChange` sends it on
`configurationChangeCh`: its request (in scope, `cfgReqOk`), its `logFuture`'s fields (the leader's
`appendConfigurationEntry` sets the `log`, `dispatchLogs` the `dispatch`, the FSM goroutine the
`response`) and the responder side answering `cfgChangeQ`. -/
def ccfP (γ : GNames) (f : Loc) : IProp GF :=
  iprop(∃ (rq : configurationChangeRequest) (lv : Log) (t : time.Time) (v : GoInterface),
    f.[configurationChangeFuture, go!"req"] ↦ rq ∗ ⌜cfgReqOk γ rq⌝ ∗
    (f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"log"] ↦ lv ∗
    (f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"response"] ↦ v ∗
    (f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"dispatch"] ↦ t ∗
    deferResp ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"])
      cfgChangeQ)

/-- **A dispatched future** at index `k` with entry `e` (in the leader `i`'s `inflight`, then in a
batch to the FSM): its `log` field is the entry (read-only from now on), its `response` field is
the responder's to write, and its `deferError` is either a client's (a command with data `d`,
answering `futQ`; the token already went to the protocol at dispatch), the leader's no-op (answer
anything; its `errCh` is nil), or (stage 2) a client's barrier (answering `barrierQ` for the
client's snapshot `sc`, with what the leader knew at dispatch, `barrierDisp`), or (stage 4) a
configuration change future's (a configuration entry, answering `cfgChangeQ`). -/
def futResp (γ : GNames) (rc : RCtx GF) (i : SID) (f : Loc) (k : Nat) (e : Entry) : IProp GF :=
  iprop(logPtr (f.[logFuture, go!"log"]) k e ∗ (∃ v : GoInterface, f.[logFuture, go!"response"] ↦ v) ∗
    ((⌜e.kind = kNoop⌝ ∗ deferResp (f.[logFuture, go!"deferError"]) (fun _ => iprop(True))) ∨
     (∃ (d : List w8) (n : Nat), ⌜e.kind = kCommand ∧ e.data = d⌝ ∗
        deferResp (f.[logFuture, go!"deferError"]) (futQ γ rc f d n)) ∨
     (∃ sc : Snap, ⌜e.kind = kBarrier⌝ ∗ barrierDisp γ i sc k e ∗
        deferResp (f.[logFuture, go!"deferError"]) (barrierQ γ rc i sc)) ∨
     (⌜e.kind = kConfig⌝ ∗ deferResp (f.[logFuture, go!"deferError"]) cfgChangeQ)))

/-- What `Error()` returned on a client's future (an interface value `fi`, the `ApplyFuture`
returned by `Apply`), with the client's token for not-taken errors, or the committed command's
facts and the response for `nil`. -/
def futDone (γ : GNames) (rc : RCtx GF) (fi : GoInterface) (d : List w8) (n : Nat)
    (err : GoInterface) : IProp GF :=
  iprop(((isRaftErr .notLeader err ∨ isRaftErr .leadershipTransferInProgress err ∨
        isRaftErr .enqueueTimeout err) ∗ opTok γ d n) ∨
    (⌜err = interface.nil⌝ ∗ ∃ (f : Loc) (k : Nat) (e : Entry) (r : GoInterface),
      ⌜fi = interface.mkOk (go.GoType.PointerType logFuture.ty) #f⌝ ∗
      CIdx γ k e ∗ ⌜e.kind = kCommand ∧ e.data = d⌝ ∗ rc.respP k r ∗
      f.[logFuture, go!"response"] ↦ r) ∨
    isRaftErr .leadershipLost err)

/-- **The client's future** `fi` returned by `Apply` for command data `d` with token
`opTok γ d n`: an `errorFuture{ErrEnqueueTimeout}` (never sent; the token stays with the client),
or a `*logFuture` whose answer the client may wait for once (`Error()`). -/
def futureOwn (γ : GNames) (rc : RCtx GF) (fi : GoInterface) (d : List w8) (n : Nat) :
    IProp GF :=
  iprop((∃ e : GoInterface,
      ⌜fi = interface.mkOk errorFuture.ty #(errorFuture.mk e)⌝ ∗ isRaftErr .enqueueTimeout e ∗
      opTok γ d n) ∨
    (∃ f : Loc, ⌜fi = interface.mkOk (go.GoType.PointerType logFuture.ty) #f⌝ ∗
      deferWait (f.[logFuture, go!"deferError"]) (futQ γ rc f d n)))

/-- (stage 2) **A client's future** `fi` (a `Future` interface value: `Barrier`'s, `VerifyLeader`'s,
`LeadershipTransfer`'s) whose `Error()` the client may call once and gets an answer satisfying
`Q`: an `errorFuture` whose error satisfies `Q`, or a `*logFuture`, `*verifyFuture`,
`*leadershipTransferFuture`, (stage 3, `Snapshot`'s) `*userSnapshotFuture` or (stage 4, the
configuration changes') `*configurationChangeFuture` whose `deferError` answers `Q`. -/
def futWait (fi : GoInterface) (Q : GoInterface → IProp GF) : IProp GF :=
  iprop((∃ e : GoInterface, ⌜fi = interface.mkOk errorFuture.ty #(errorFuture.mk e)⌝ ∗ Q e) ∨
    (∃ f : Loc, ⌜fi = interface.mkOk (go.GoType.PointerType logFuture.ty) #f⌝ ∗
      deferWait (f.[logFuture, go!"deferError"]) Q) ∨
    (∃ f : Loc, ⌜fi = interface.mkOk (go.GoType.PointerType verifyFuture.ty) #f⌝ ∗
      deferWait (f.[verifyFuture, go!"deferError"]) Q) ∨
    (∃ f : Loc, ⌜fi = interface.mkOk (go.GoType.PointerType leadershipTransferFuture.ty) #f⌝ ∗
      deferWait (f.[leadershipTransferFuture, go!"deferError"]) Q) ∨
    (∃ f : Loc, ⌜fi = interface.mkOk (go.GoType.PointerType userSnapshotFuture.ty) #f⌝ ∗
      deferWait (f.[userSnapshotFuture, go!"deferError"]) Q) ∨
    (∃ f : Loc, ⌜fi = interface.mkOk (go.GoType.PointerType configurationChangeFuture.ty) #f⌝ ∗
      deferWait ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) Q))

/-! ## Verify futures (stage 2) -/

/-- **What the leader knows when it hands a verify future to the FSM goroutine** (persistent,
leaderLoop's quorum case): `i` led `T` (in `T` at a snapshot `st` after the client's `sc`), and every
voter's durable prefix at `sc` is at most `len0 T` or at most `a`, what the leader had handed to
its FSM (`gprot.read_bound_upd`, with `pubOwn`'s bound `≤ lastApplied`). -/
def verifyItem (γ : GNames) (i : SID) (sc : Snap) (a : Nat) : IProp GF :=
  iprop(∃ (T n0 : Nat) (st : Snap), leaderIs γ T i ∗ len0Is γ T n0 ∗ histLb γ st ∗
    ⌜snapLe sc st ∧ st.term i = T ∧ ∀ i' ∈ γ.srvs, sc.dur i' ≤ n0 ∨ sc.dur i' ≤ a⌝)

/-- (stage 2) **What a verify future's `Error()` returning `nil` means** (`Raft.VerifyLeader`, the
client's snapshot `sc` taken before the call): the leader's facts at the quorum (`verifyItem`) for
some `s`, and the FSM had processed `s` (`fsmAt`: the FSM goroutine answers the future after the
batches sent before it, fix `ea6e596`). -/
def verifyOk (γ : GNames) (rc : RCtx GF) (i : SID) (sc : Snap) : IProp GF :=
  iprop(∃ s : Nat, verifyItem γ i sc s ∗ fsmAt γ rc.respP i s)

/-- (stage 2) A verify future's answer: an error (no facts) or `nil` with `verifyOk`. -/
def verifyQ (γ : GNames) (rc : RCtx GF) (i : SID) (sc : Snap) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ verifyOk γ rc i sc)

/-- (stage 2) **A fresh verify future** as `VerifyLeader` sends it on `verifyCh`: its fields
(`quorumSize = 0` marks it fresh), the client's snapshot `sc` and the responder side answering
`verifyQ`. (Stage 4: no voter count; stage 3 had `2 ≤ |voters|`, since with one voter `verifyLeader`
answered at once without the FSM wait; fix `0c7aa12` sends that case through `fsmMutateCh` too.) -/
def verifyNew (γ : GNames) (rc : RCtx GF) (i : SID) (v : Loc) : IProp GF :=
  iprop(∃ sc : Snap, histLb γ sc ∗
    v.[verifyFuture, go!"notifyCh"] ↦ (chan.nil : Loc) ∗ v.[verifyFuture, go!"quorumSize"] ↦ W64 0 ∗
    v.[verifyFuture, go!"votes"] ↦ W64 0 ∗ v.[verifyFuture, go!"voteLock"] ↦ (zero_val sync.Mutex) ∗
    deferResp (v.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc))

/-- (stage 2) The vote token of voter `j` for the verify future `v` (exclusive: each voter votes
once, its replication goroutine's `heartbeat` having taken `v` out of its notify set). -/
def voteTok (rc : RCtx GF) (v : Loc) (j : SID) : IProp GF := (v, j) ↪[rc.names.vtok] ()

/-- (stage 2) **The registration of a verify future** (persistent, agreeing: `vregIs_agree`): `v`
was registered by the leader loop of term `T` at the snapshot `sv`. -/
def vregIs (rc : RCtx GF) (v : Loc) (T : Nat) (sv : Snap) : IProp GF :=
  v ↪[rc.names.vreg]□ (T, sv)

/-- (stage 2) The token of a registered future not yet received back from `vote` (exclusive). -/
def backTok (rc : RCtx GF) (v : Loc) : IProp GF := v ↪[rc.names.vlive] ()

/-- (stage 2) The token of a registered future in the leader's notify set (exclusive). -/
def nmTok (rc : RCtx GF) (v : Loc) : IProp GF := v ↪[rc.names.vnm] ()

/-- (stage 2) **The vote lock's invariant** of the verify future `v`, registered by the leader `i`
of `T` at the snapshot `sv` with the leader log's prefix `L` (`verifyLeader`), whose notify channel is
`vch` (`verifyCh`): until it is notified, `notifyCh = vch`, it holds the future's back token, and the
votes counted are those of distinct voters `Q` of `L`'s latest configuration (stage 4, fixes `6c3454c`,
`4bb3955`: the leader's own only if it is one, then first; stage 3: the fixed voters, the leader
always), each with its token and its witness of being in `T` after `sv` (`respWit`); once notified
(`notifyCh = nil`), the votes and the back token went with the future on `verifyCh`. -/
def voteInv (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (sv : Snap) (L : RLog) (vch : Loc)
    (v : Loc) : IProp GF :=
  iprop(∃ nc : Loc, v.[verifyFuture, go!"notifyCh"] ↦ nc ∗
    (⌜nc = chan.nil⌝ ∨
     ⌜nc = vch⌝ ∗ backTok rc v ∗ ∃ (n : w64) (Q : List SID), v.[verifyFuture, go!"votes"] ↦ n ∗
       ⌜uint.nat n = Q.length ∧ Q.Nodup ∧ ∀ j ∈ Q, j ∈ cfgOfC γ.cv L⌝ ∗
       ([∗list] j ∈ Q, voteTok rc v j ∗ respWit γ j T sv)))

/-- (stage 2) **A registered verify future** (persistent): registered by the leader `i` of `T` at
the snapshot `sv` (`vregIs`; the leader's own witness of being in `T` there, `respWit`; stage 4: the
leader's log `L` then, a prefix of `llog T` of length `sv.llen T` past `T`'s election part,
`llogPre`), its quorum size `q` (read-only; stage 4: `≥ 1`, a majority of the voters of `L`'s latest
configuration, `quorumSize`; stage 3: `≥ 2`, of the fixed voters), its vote lock. What
`gprot.read_bound_upd` takes at a quorum. -/
def verifyReg (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (sv : Snap) (L : RLog) (vch : Loc)
    (v : Loc) : IProp GF :=
  iprop(∃ q : w64, vregIs rc v T sv ∗ v.[verifyFuture, go!"quorumSize"] ↦□ q ∗
    llogPre γ T L ∗ respWit γ i T sv ∗ (∃ n0 : Nat, len0Is γ T n0 ∗ ⌜n0 < L.length⌝) ∗
    ⌜L.length = sv.llen T ∧ 1 ≤ uint.nat q ∧ (cfgOfC γ.cv L).length < 2 * uint.nat q ∧
      uint.nat q < 2 ^ 63⌝ ∗
    sync.isMutex (v.[verifyFuture, go!"voteLock"]) (voteInv γ rc i T sv L vch v))

/-- (stage 2) **A voted verify future** as `vote` sends it back on `verifyCh` (once: it carries the
back token): registered (`T`, `sv` through `vregIs`; the leader's witness, so a leader of a later term
`T2` that receives a stale voted future knows `T ≤ T2`), its votes (now the receiver's) either short of
the quorum (a voter answered `false`) or from a quorum of distinct voters of `L`'s latest
configuration in `T` after `sv` (stage 4; stage 3: of the fixed voters, the leader among them). -/
def verifyVoted (γ : GNames) (rc : RCtx GF) (i : SID) (vch : Loc) (v : Loc) : IProp GF :=
  iprop(∃ (T : Nat) (sv : Snap) (L : RLog) (n q : w64), verifyReg γ rc i T sv L vch v ∗ backTok rc v ∗
    v.[verifyFuture, go!"quorumSize"] ↦□ q ∗ v.[verifyFuture, go!"votes"] ↦ n ∗
    (⌜uint.nat n < uint.nat q⌝ ∨
     ∃ Q : List SID, ⌜uint.nat q ≤ Q.length ∧ Q.Nodup ∧ ∀ j ∈ Q, j ∈ cfgOfC γ.cv L⌝ ∗
       [∗list] j ∈ Q, respWit γ j T sv))

/-- (stage 2) **The `verifyCh` element** of server `i` (`vch`): a fresh future from `VerifyLeader`
or a voted one from `vote`. -/
def verifyP (γ : GNames) (rc : RCtx GF) (i : SID) (vch : Loc) (v : Loc) : IProp GF :=
  iprop(verifyNew γ rc i v ∨ verifyVoted γ rc i vch v)

/-- (stage 2) **A registered verify future in a follower's notify set** (`followerReplication.notify`,
`verifyLeader` adds it, `heartbeat` takes it): its registration, the follower `j`'s vote token, and
(stage 4, fix `6c3454c`) that `j` is a voter of the registration's configuration. -/
def notifyEntry (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (vch : Loc) (j : SID) (v : Loc) :
    IProp GF :=
  iprop(∃ (sv : Snap) (L : RLog), histLb γ sv ∗ verifyReg γ rc i T sv L vch v ∗ voteTok rc v j ∗
    ⌜j ∈ cfgOfC γ.cv L⌝)

/-- (stage 2) **A registered verify future in the leader's notify set** (`leaderState.notify`): its
registration (of the leader's term `T`) and its notify-set token. Its responder side is in the
main goroutine's registry (`verifyRegistry`). -/
def leaderNotifyEntry (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (vch : Loc) (v : Loc) :
    IProp GF :=
  iprop(∃ (sv : Snap) (L : RLog), histLb γ sv ∗ verifyReg γ rc i T sv L vch v ∗ nmTok rc v)

/-- (stage 2) **The responder state of a registered verify future** not yet received back: pending
(the client's snapshot `sc ≤ sv` and the responder side, answering `verifyQ`; only while it is in
the leader's notify set, `inNM`) or already answered (`deferDone`: the leader stepped down and
answered it, or a `false` vote did; a later `respond` is a no-op). -/
def vregState (γ : GNames) (rc : RCtx GF) (i : SID) (v : Loc) (sv : Snap) (inNM : Prop) : IProp GF :=
  iprop((∃ sc : Snap, histLb γ sc ∗ ⌜snapLe sc sv ∧ inNM⌝ ∗
      deferResp (v.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
    deferDone (v.[verifyFuture, go!"deferError"]))

/-- (stage 2) **The main goroutine's registry of verify futures**: the vote tokens' authority; the
registrations `R` (each with a non-zero, read-only quorum size); the futures not yet received back
(`Live ⊆ R`, each with its responder state); the leader's notify set (`NMs ⊆ Live`; half of its
authority: the other half is `leaderOwn`'s, where it is the domain of `leaderState.notify`, or
`leaderStateAny`'s at `∅` outside `runLeader`); a pending future is in it (the leader steps down
answering everything in it, `deferDone`). A voted future brings its back token (so it is live: its
responder state is here), a notify-set entry its token (so it is live). -/
def verifyRegistry (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop(∃ (V : GMap (Loc × SID) Unit) (R : GMap Loc (Nat × Snap)) (Live NMs : GMap Loc Unit),
    ghostMapAuth rc.names.vtok 1 V ∗ ghostMapAuth rc.names.vreg 1 R ∗
    ghostMapAuth rc.names.vlive 1 Live ∗ ghostMapAuth rc.names.vnm (1 : Qp).half NMs ∗
    ⌜(∀ p, (V.lookup p).isSome → (R.lookup p.1).isSome) ∧
      (∀ v, (Live.lookup v).isSome → (R.lookup v).isSome) ∧
      (∀ v, (NMs.lookup v).isSome → (Live.lookup v).isSome)⌝ ∗
    ([∗map] v ↦ _x ∈ R, ∃ q : w64, v.[verifyFuture, go!"quorumSize"] ↦□ q ∗ ⌜q ≠ W64 0⌝) ∗
    ([∗map] v ↦ _u ∈ Live, ∃ (T : Nat) (sv : Snap), ⌜R.lookup v = some (T, sv)⌝ ∗
      vregState γ rc i v sv ((NMs.lookup v).isSome)))

/-! ## Leadership transfer futures (stage 2) -/

/-- (stage 2) **A leadership transfer future** as `initiateLeadershipTransfer` sends it on
`leadershipTransferCh`: no target (`LeadershipTransfer`: the leader picks one) or a server `j ≠ i` (stage 4; stage 3: a voter)
as both its `ID` and `Address` (read-only), and the responder side (answer anything, once). -/
def ltfP (γ : GNames) (i : SID) (f : Loc) : IProp GF :=
  iprop(∃ idp ap : Loc, f.[leadershipTransferFuture, go!"ID"] ↦ idp ∗
    f.[leadershipTransferFuture, go!"Address"] ↦ ap ∗
    (⌜idp = null ∧ ap = null⌝ ∨
     ∃ j : SID, idp ↦□ (j : ServerID) ∗ ap ↦□ (j : ServerAddress) ∗ isSrv γ j ∗ ⌜j ≠ i⌝) ∗
    deferResp (f.[leadershipTransferFuture, go!"deferError"]) (fun _ => iprop(True)))

/-! ## The FSM batch channel `fsmMutateCh` -/

/-- One tuple of a batch: index `k`, entry `e`, the tuple `tp`, its log pointer `lp` and future
`fp`. -/
structure BatchItem where
  k : Nat
  e : Entry
  tp : Loc
  lp : Loc
  fp : Loc

/-- **A batch** sent to the FSM, covering the indexes `(k0, k1]` of the server's committed log:
a `[]*commitTuple` (boxed in an `interface{}`) of the commands and configuration entries in the
range, in increasing index order, the last at `k1`; each tuple read-only, its log the committed
entry (`CIdx`, `durLb`), its future `nil` or a dispatched future of that entry (`futResp`, whose
`log` field is the tuple's log); every index of the range that has no tuple holds no command. -/
def fsmBatchP (γ : GNames) (rc : RCtx GF) (i : SID) (k0 k1 : Nat) (v : GoInterface) :
    IProp GF :=
  iprop(∃ (sl : GoSlice) (items : List BatchItem),
    ⌜v = interface.mkOk (go.GoType.SliceType (go.GoType.PointerType commitTuple.ty)) #sl⌝ ∗
    sl ↦*□ items.map BatchItem.tp ∗
    ⌜items ≠ [] ∧ (items.map BatchItem.k).Pairwise (· < ·) ∧
      (∀ it ∈ items, k0 < it.k ∧ it.k ≤ k1) ∧ (items.getLast?.map BatchItem.k = some k1)⌝ ∗
    ([∗list] it ∈ items,
      it.tp ↦□ commitTuple.mk it.lp it.fp ∗ logPtr it.lp it.k it.e ∗ CIdx γ it.k it.e ∗
      durLb γ i it.k ∗ ⌜it.e.kind = kCommand ∨ it.e.kind = kConfig ∨ it.e.kind = kBarrier⌝ ∗
      (⌜it.fp = null⌝ ∨ (⌜it.lp = (it.fp.[logFuture, go!"log"])⌝ ∗ futResp γ rc i it.fp it.k it.e))) ∗
    ([∗list] x ∈ List.range' (k0 + 1) (k1 - k0),
      ⌜x ∈ items.map BatchItem.k⌝ ∨ ∃ e' : Entry, CIdx γ x e' ∗ ⌜e'.kind ≠ kCommand⌝))

/-- Batch `n` of `fsmMutateCh` ends at index `k` (persistent; the producer owns the map). -/
def batchEnd (rc : RCtx GF) (n k : Nat) : IProp GF := n ↪[rc.names.batch]□ k

instance batchEnd_persistent rc n k : Persistent (batchEnd (GF := GF) rc n k) := by
  unfold batchEnd; infer_instance

/-- Batch `n` starts after index `k0`: the previous batch's end (`0` for the first batch). -/
def batchStart (rc : RCtx GF) (n k0 : Nat) : IProp GF :=
  iprop(⌜n = 0 ∧ k0 = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ batchEnd rc m k0)

/-- (stage 2) **A verify future handed to the FSM goroutine** (`v`, boxed in an `interface{}`)
after the batches ending at `k0`: the leader had handed `a ≥ k0` to its FSM (no command in
`(k0, a]`, `a` durable) and knew `verifyItem` for `a`; the FSM goroutine answers it (`nil`, with
`fsmAt _ _ i a` once it processed the batches before). Or a stale voted future (registered in an
earlier term, answered when its leader stepped down) forwarded by a later leader term: already
answered (`deferDone`; the FSM's `respond(nil)` is a no-op). -/
def fsmVerifyP (γ : GNames) (rc : RCtx GF) (i : SID) (k0 : Nat) (v : GoInterface) : IProp GF :=
  iprop(∃ vf : Loc, ⌜v = interface.mkOk (go.GoType.PointerType verifyFuture.ty) #vf⌝ ∗
    ((∃ (sc : Snap) (a : Nat), ⌜k0 ≤ a⌝ ∗
      noCmdBetween γ k0 (a + 1) ∗ durLb γ i a ∗ verifyItem γ i sc a ∗
      deferResp (vf.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
     deferDone (vf.[verifyFuture, go!"deferError"])))

/-- (stage 3) **The answer of a restore future**: nil (the restore never fails: the snapshot is
still the store's latest, `snapCell`'s pending install, and the FSM's `Restore` returns nil), with
the main goroutine's half of the pending-install record back. -/
def restoreQ (rc : RCtx GF) (s st : Nat) (id : GoString) (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∗ ghostVar rc.dur.pend (1 : Qp).half (some (s, st, id)))

/-- (stage 3) **A restore future handed to the FSM goroutine** (`v`, boxed in an `interface{}`;
installSnapshot, after the batches ending at `k0 ≤ s`): the snapshot `(s, st)` closed in the store
with the sink id `id` (the future's `ID`), the main goroutine's half of the pending-install record
(so the FSM's `Open(id)` finds it the latest), and the responder side answering `restoreQ`. The
batch chain continues after it at `s` (the restore item's `batchEnd` is `s`). -/
def fsmRestoreP (γ : GNames) (rc : RCtx GF) (k0 s : Nat) (v : GoInterface) : IProp GF :=
  iprop(∃ (f : Loc) (id : GoString) (st : Nat),
    ⌜v = interface.mkOk (go.GoType.PointerType restoreFuture.ty) #f ∧ k0 ≤ s⌝ ∗
    f.[restoreFuture, go!"ID"] ↦□ id ∗ (∃ e : Entry, CIdx γ s e ∗ ⌜e.term = st⌝) ∗
    ghostVar rc.dur.pend (1 : Qp).half (some (s, st, id)) ∗
    deferResp (f.[restoreFuture, go!"deferError"]) (restoreQ rc s st id))

/-- The SPSC predicate of `fsmMutateCh`: the `n`-th value sent is a batch covering
`(start, end]` of batch `n`, or (stage 2) a verify future (an empty batch: it ends where the
previous one ended), or (stage 3) a restore future (it ends at the snapshot's index). -/
def fsmP (γ : GNames) (rc : RCtx GF) (i : SID) (n : Int) (v : GoInterface) : IProp GF :=
  iprop(∃ k0 k1 : Nat, ⌜0 ≤ n⌝ ∗ batchStart rc n.toNat k0 ∗ batchEnd rc n.toNat k1 ∗
    (fsmBatchP γ rc i k0 k1 v ∨ ⌜k1 = k0⌝ ∗ fsmVerifyP γ rc i k0 v ∨ fsmRestoreP γ rc k0 k1 v))

/-- **The FSM producer's state** (the main goroutine's; `processLogs` and (stage 3)
`installSnapshot` use it): the items sent so far, the end `e` of the last one, (stage 3) every item's
end at most `e`, and the facts that the indexes `(e, a]` (handed to the FSM but in no batch:
non-commands at the end of a `processLogs` call) hold no command. -/
def fsmProd (γ : GNames) (rc : RCtx GF) (a : Nat) : IProp GF :=
  iprop(∃ (sent : List GoInterface) (M : GMap Nat Nat) (e : Nat),
    spscProducer rc.names.fsmCh sent ∗ ghostMapAuth rc.names.batch 1 M ∗
    ⌜(∀ m, (M.lookup m).isSome ↔ m < sent.length) ∧ e ≤ a ∧
      (∀ m k, M.lookup m = some k → k ≤ e)⌝ ∗
    (⌜sent = [] ∧ e = 0⌝ ∨ batchEnd rc (sent.length - 1) e) ∗
    noCmdBetween γ e (a + 1))

/-- **The FSM consumer's initial state** (given to `runFSM` by `NewRaft`). -/
def fsmCons (rc : RCtx GF) : IProp GF :=
  iprop(spscConsumer rc.names.fsmCh ([] : List GoInterface) ∗ rc.fsmOwn 0)

/-! ## Snapshots (stage 3) -/

/-- (stage 3) **What raft keeps about its snapshot store's latest snapshot** `(m, b)`: the committed
log has an entry of its term at its index `≥ 1` (`CIdx`), its bytes are a snapshot of its index
(`snapP`), its configuration and configuration index are the committed log's at its index (stage 4,
`snapCfg`; stage 3: the bootstrap one at index 1), version 1, `Size = |b|`, no `Peers`. -/
def latestOk (γ : GNames) (rc : RCtx GF) (lat : SnapLatest) : IProp GF :=
  match lat with
  | none => iprop(True)
  | some (m, b) => iprop((∃ e : Entry, CIdx γ (uint.nat m.Index') e ∗
        ⌜e.term = uint.nat m.Term' ∧ 1 ≤ uint.nat m.Index'⌝) ∗
      rc.snapP (uint.nat m.Index') b ∗
      (∃ ss : List Server, cfgVal γ m.Configuration' ss ∗
        snapCfg γ (uint.nat m.Index') (uint.nat m.ConfigurationIndex') ss) ∗
      ⌜m.Version' = W64 1 ∧ uint.nat m.Size' = b.length ∧
        b.length < 2 ^ 63 ∧ m.Peers' = slice.nil⌝)

/-! ## The crash-surviving state (hraft_robust L0, R1 §1.3, §2, §3) -/

/-- (hraft_robust L0) The stable store's last vote is the protocol's: `LastVoteTerm` always;
`LastVoteCand` when voted in the current term (R1 §5: with `persistVote` writing `LastVoteCand`
first, a torn vote leaves a candidate of a term below the current one, `s.vterm < s.term`). (Was:
`LastVoteCand` whenever voted.) -/
def voteMatches (sst : StableAbs) (s : SState) : Prop :=
  uint.nat ((sst.ints.lookup (go!"LastVoteTerm" : List w8)).getD (W64 0)) = s.vterm ∧
  (s.vterm = 0 ∨ s.vterm < s.term ∨ sst.bytes.lookup (go!"LastVoteCand" : List w8) = some s.vcand)

/-- (hraft_robust L0) **The log store holds the protocol log** `L` (was `logCell`'s body): only entries
of `L`, and every entry of `L` from `lo` on. -/
def logOk (A : LogAbs) (L : RLog) (lo : Nat) : Prop :=
  (∀ k e, A.m.lookup k = some e → ent L k = some e) ∧
  (∀ k, lo ≤ k → k ≤ L.length → A.m.lookup k = ent L k)

/-- (hraft_robust L0) The stored `CurrentTerm` against the protocol's term and the pending term step. -/
def termDurOk (D : StableAbs) (s : SState) (tp : Option TermPend) : Prop :=
  let dt := uint.nat ((D.ints.lookup (go!"CurrentTerm" : List w8)).getD (W64 0))
  (tp = none ∧ dt = s.term) ∨ (∃ t, tp = some (.set t) ∧ dt = t ∧ s.term ≤ t) ∨
    (tp = some .elect ∧ dt = s.term + 1)

/-- (hraft_robust L0) What firing the pending term step `tp` at a crash needs (`setTerm_upd`'s
`termOk`, `electTerm_upd`'s receipt). -/
def tpRes (γ : GNames) (tp : Option TermPend) : IProp GF :=
  match tp with
  | none => iprop(True)
  | some (.set t) => termOk γ t
  | some .elect => receipt 1

/-- (hraft_robust L0) What the pending discard `dp` needs (`installDiscard_upd`'s premises, over the
protocol state `s`). -/
def dpRes (γ : GNames) (i : SID) (s : SState) (dp : Option DiscPend) : IProp GF :=
  match dp with
  | none => iprop(True)
  | some d => iprop(aeValid γ s.term d.x d.st [] d.x ∗ leaderIs γ s.term d.ℓ ∗
      ⌜d.ℓ ≠ i ∧ 1 ≤ d.x ∧ ¬ prevMatch s.log d.x d.st⌝)

/-- (hraft_robust L0) **What raft keeps about its snapshot store across a crash** (was `snapCell`'s
body; R1 §1.5): the latest (`latestOk`), and, with no install pending, the latest's index durable at
`i` or installed while `i` followed; an install pending (from the install's `sink.Close()` to its
`setLastApplied(s)`), with the main goroutine's half of the `lastApplied` authority at `a < s`.
(`snapCell`'s `applLb` of the latest, a fact of one generation, is dropped: R1 §1.5.) -/
def latestDur (γ : GNames) (rc : RCtx GF) (i : SID) (lat : SnapLatest)
    (pend : Option (Nat × Nat × GoString)) (dp : Option DiscPend) : IProp GF :=
  iprop(latestOk γ rc lat ∗
    (match pend with
      | none => ⌜lat = none⌝ ∨ ∃ (m : SnapshotMeta) (b : List w8), ⌜lat = some (m, b)⌝ ∗
          (durLb γ i (uint.nat m.Index') ∗ ⌜dp = none⌝ ∨ snapFollow γ i (uint.nat m.Index') (uint.nat m.Term') ∗
            ⌜∃ ℓ, dp = some ⟨uint.nat m.Index', uint.nat m.Term', ℓ⟩⌝ ∗
            ∃ a : Nat, monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ uint.nat m.Index'⌝)
      | some (s, st, id) => ∃ (m : SnapshotMeta) (b : List w8) (a : Nat),
          ⌜lat = some (m, b) ∧ m.ID' = id ∧ uint.nat m.Index' = s ∧ uint.nat m.Term' = st ∧ a < s⌝ ∗
          snapFollow γ i s st ∗ monoNatAuthOwn rc.dur.applied (1 : Qp).half a))

/-- (hraft_robust, R2) The latest snapshot's index (`0`: none). The log store's lower bound `lo` stays at
most one above it (a compaction deletes up to a snapshot closed before; an install's discard up to its own);
the frontier `c` may run ahead (the configurations answer raises it before the snapshot's `Close`). -/
def latIdxD (lat : SnapLatest) : Nat :=
  match lat with
  | none => 0
  | some (m, _) => uint.nat m.Index'

/-- (hraft_robust, R4b) The latest snapshot's index is at least `x` (persistent). -/
def latLb (rc : RCtx GF) (x : Nat) : IProp GF := monoNatLbOwn rc.dur.lat x

instance latLb_persistent rc x : Persistent (latLb (GF := GF) rc x) := by
  unfold latLb; infer_instance

/-- (hraft_robust L0) **A server's state that survives a crash** (R1 §1.3): its protocol state `s`,
its log store's state `A` (with `logCell`'s bound `lo` and compaction frontier `c`), its stable store's
`D`, the pending term step `tp`, its snapshot store's latest `lat` and pending install `pend`, and the
pending discard `dp`. -/
structure SrvDur where
  s : SState
  A : LogAbs
  lo : Nat
  c : Nat
  D : StableAbs
  tp : Option TermPend
  lat : SnapLatest
  pend : Option (Nat × Nat × GoString)
  dp : Option DiscPend

/-- (hraft_robust, R5 Q0) **The boot pin** in the crash state: during `NewRaft`, the stores' state is the
arm-time one (`NewRaft` holds the other ½); afterwards discarded `none`. -/
def bootPin (rc : RCtx GF) (X : SrvDur) : IProp GF :=
  iprop((∃ o : Option (LogAbs × SnapLatest), dghostVar rc.dur.boot (DFrac.own (1 : Qp).half) o ∗
      ⌜∀ p, o = some p → p = (X.A, X.lat)⌝) ∨
    dghostVar rc.dur.boot DFrac.discard (none : Option (LogAbs × SnapLatest)))

/-- (hraft_robust, R5 Q0) The boot is over (persistent): `bootPin` is its second disjunct. -/
def bootOver (rc : RCtx GF) : IProp GF :=
  dghostVar rc.dur.boot DFrac.discard (none : Option (LogAbs × SnapLatest))

instance bootOver_persistent rc : Persistent (bootOver (GF := GF) rc) := by
  unfold bootOver; infer_instance

/-- (hraft_robust L0) **The body of `srvDurInv`** at `X`: gprot's exclusive halves of server `i` (its
state, log, term, commit index and durable-prefix view), the views' other halves, the stores'
client authorities, and the couplings between the two: the log store holds the protocol log (`logOk`,
from `lo`, `lo ≤ c + 1` for the compaction frontier `c`), the stable store's vote and term are the
protocol's (`voteMatches`, `termDurOk` with the pending term step), the written commit index is
durable, the snapshot store's latest (`latestDur`), and the pending steps' premises (`tpRes`,
`dpRes`). -/
def durBody (γ : GNames) (rc : RCtx GF) (i : SID) (X : SrvDur) : IProp GF :=
  iprop(srvOwn γ i X.s ∗ durView γ i (1 : Qp).half X.s.dur.1 ∗ logCouple γ i X.s.log ∗
    termCouple γ i X.s.term ∗ cidxCouple γ i X.s.cidx ∗
    ghostVar rc.dur.sv (1 : Qp).half (X.s, X.tp, X.dp) ∗ ghostVar rc.dur.st (1 : Qp).half (X.D, X.A.staged) ∗
    ghostVar rc.dur.tv (1 : Qp).half X.s.term ∗ ghostVar rc.dur.cv (1 : Qp).half X.s.cidx ∗
    rc.ownL X.A ∗ rc.ownS X.D ∗ rc.ownSS X.lat ∗
    ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
      uint.nat X.A.ci ≤ X.s.dur.1⌝ ∗
    ⌜(∀ d, X.dp = some d → X.lo ≤ d.x) ∧
      (∀ x st id, X.pend = some (x, st, id) → (∃ ℓ, X.dp = some ⟨x, st, ℓ⟩) ∨ prevMatch X.s.log x st) ∧ X.lo ≤ latIdxD X.lat + 1⌝ ∗
    bootPin rc X ∗
    monoNatAuthOwn rc.dur.comp (1 : Qp).half X.c ∗ ⌜∀ d, X.dp = some d → X.c < d.x⌝ ∗
    ⌜(X.tp = none ∨ X.dp = none) ∧
      (∀ d, X.dp = some d → ∃ m b, X.lat = some (m, b) ∧ uint.nat m.Index' = d.x ∧ uint.nat m.Term' = d.st)⌝ ∗
    monoNatAuthOwn rc.dur.lat 1 (latIdxD X.lat) ∗
    latestDur γ rc i X.lat X.pend X.dp ∗ ghostVar rc.dur.pend (1 : Qp).half X.pend ∗
    tpRes γ X.tp ∗ dpRes γ i X.s X.dp)

/-- (hraft_robust L0) The crash token of `srvDurInv` (held by the generation's crash wand). -/
def srvCrashTok (rc : RCtx GF) : IProp GF := ghostVar rc.dur.tok 1 ()

/-- (hraft_robust L0, R1 §1.3) **Server `i`'s crash invariant for one generation** (Route 1 of
`notes/raft-crash-law-design.md`): the crash state `durBody`, or (after the generation crashed) the
crash token, which the crash law (`raft_crash`) swaps in to take the body out. Allocated before the
generation runs (`raft_arm`); replaces `logCell` and `snapCell`. A goroutine of the generation opens it
with its crash token (`inv_nc_acc`, `|NC=`). -/
def srvDurInvRaw (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  inv durN iprop((∃ X : SrvDur, durBody γ rc i X) ∨ crashed ∗ srvCrashTok rc)

instance srvDurInvRaw_persistent γ rc i : Persistent (srvDurInvRaw (GF := GF) γ rc i) := by
  unfold srvDurInvRaw; infer_instance

/-- (hraft_robust, R5 Q0) **`srvDurInv` after the boot**: the raw invariant (`raft_arm` allocates it, `NewRaft`
and the crash law use it) with the boot over (`bootOver`). -/
def srvDurInv (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop(srvDurInvRaw γ rc i ∗ bootOver rc)

instance srvDurInv_persistent γ rc i : Persistent (srvDurInv (GF := GF) γ rc i) := by
  unfold srvDurInv; infer_instance

/-! ### Window resources (R1 §3) -/

/-- (hraft_robust L0, R1 §2.2) **A durable step pending at a store write's commit point**: the model
step that the write's atomic update fires, recorded in the window resource the write lends to the
store (`winRes`), so that a crash that keeps the write's new contents can fire it (`pend_fire`).
* `app es`: the leader's appends (`leaderAppendCmd_upd`: no-ops, barriers, commands), `StoreLogs`;
* `cfg e k p`: a configuration entry (`leaderAppendCfg_upd`), `StoreLogs`;
* `trunc prev pt ents lci j`: the follower's truncation (`truncate_upd`), `DeleteRange`;
* `fstore prev pt ents lci j lc`: the follower's append (`followerStore_upd`), then, if `lc = some v`,
  the commit learnt with it (`learnCommitFollower` of `min lci v`, the written commit index),
  `StoreLogs`;
* `discard d`: an install's discard (`installDiscard_upd`), `DeleteRange`;
* `vote c li lt`: the vote (`grantVote_upd`), the second vote write (`SetUint64(LastVoteTerm)`);
* `term tp`: a term step made durable (`SetUint64(CurrentTerm)`): recorded as `durBody`'s `tp`. -/
inductive Pend where
  | app (es : RLog)
  | cfg (e : Entry) (k p : Nat)
  | trunc (prev pt : Nat) (ents : RLog) (lci j : Nat)
  | fstore (prev pt : Nat) (ents : RLog) (lci j : Nat) (lc : Option Nat)
  | discard (d : DiscPend)
  | vote (c : SID) (li lt : Nat)
  | term (tp : TermPend)

/-- (hraft_robust, R2 req. 2) `Pend` is countable (the main goroutine's pending-write record `pw`). -/
def Pend.code : Pend → Nat × Pos
  | .app es => (0, Pos.Countable.encode es)
  | .cfg e k p => (1, Pos.Countable.encode (e, k, p))
  | .trunc prev pt ents lci j => (2, Pos.Countable.encode (prev, pt, ents, lci, j))
  | .fstore prev pt ents lci j lc => (3, Pos.Countable.encode (prev, pt, ents, lci, j, lc))
  | .discard d => (4, Pos.Countable.encode d)
  | .vote c li lt => (5, Pos.Countable.encode (c, li, lt))
  | .term tp => (6, Pos.Countable.encode tp)

instance pend_countable : Pos.Countable Pend :=
  Pos.Countable.ofInjective (fun p => Pos.Countable.encode p.code)
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a <;> cases b <;> (try simp only [Pend.code, Prod.mk.injEq] at h) <;> (try omega) <;>
        (obtain ⟨-, h⟩ := h; have h := Pos.encode_inj h; simp_all))

/-- (hraft_robust L0) The pure premises of the pending step `p`'s law, over the protocol state `s`. -/
def pendPre (γ : GNames) (i : SID) (s : SState) : Pend → Prop
  | .app es => ∀ e ∈ es, e.term = s.term ∧ (e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier)
  | .cfg e k _ => e.term = s.term ∧ e.kind = kConfig ∧ cfgValid γ.srvs (γ.cv e.data) ∧
      adjV (cfgOfC γ.cv s.log) (γ.cv e.data) ∧ lastCfgIdx s.log ≤ k
  | .trunc prev pt ents _ j => prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents j ∧
      j < ents.length ∧ prev + 1 + j ≤ s.log.length ∧ termAt s.log (prev + 1 + j) ≠ termAt ents (j + 1)
  | .fstore prev pt ents lci j lc => prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents j ∧
      ((j < ents.length ∧ s.log.length = prev + j) ∨ (j = ents.length ∧ prev + j ≤ s.log.length)) ∧
      (∀ v, lc = some v → v ≤ prev + ents.length ∧ 0 < Min.min lci v)
  | .discard d => d.ℓ ≠ i ∧ 1 ≤ d.x ∧ ¬ prevMatch s.log d.x d.st
  | .vote _ li lt => s.vterm < s.term ∧ upToDate li lt s.log
  | .term (.set t) => s.term ≤ t
  | .term .elect => True

/-- (hraft_robust L0) The resources of the pending step `p`'s law besides gprot's halves (persistent
facts, receipts, operation tokens, the lent commitment configuration), over the protocol state `s`. -/
def pendHyps (γ : GNames) (i : SID) (s : SState) : Pend → IProp GF
  | .app es => iprop(leaderIs γ s.term i ∗ receipt es.length ∗
      ([∗list] e ∈ es.filter (fun e => decide (e.kind = kCommand)), ∃ n, opTok γ e.data n))
  | .cfg _ k p => iprop(leaderIs γ s.term i ∗ ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
      commitIs γ s.term k p ∗ receipt 1)
  | .trunc prev pt ents lci _ => aeValid γ s.term prev pt ents lci
  | .fstore prev pt ents lci _ _ => aeValid γ s.term prev pt ents lci
  | .discard d => iprop(aeValid γ s.term d.x d.st [] d.x ∗ leaderIs γ s.term d.ℓ)
  | .vote c li lt => candIs γ c s.term li lt
  | .term tp => tpRes γ (some tp)

/-- (hraft_robust, R2) A quarter of the main goroutine's view of its state (`srvV` is two of them). -/
def srvVq (rc : RCtx GF) (s : SState) : IProp GF :=
  ghostVar rc.dur.sv (1 : Qp).half.half (s, (none : Option TermPend), (none : Option DiscPend))

/-- (hraft_robust, R5 Q7) A quarter of the main goroutine's view inside a pending phase (`srvVP`). -/
def srvVPq (rc : RCtx GF) (s : SState) (tp : Option TermPend) (dp : Option DiscPend) : IProp GF :=
  ghostVar rc.dur.sv (1 : Qp).half.half (s, tp, dp)

/-- (hraft_robust, R5 Q7) The pending discard while the step `p`'s write is in its window: an install's
discard is written with its discard recorded (`dp = some d`), every other write with none. -/
def pendDp : Pend → Option DiscPend
  | .discard d => some d
  | _ => none

/-- (hraft_robust, R2) A quarter of the main goroutine's stable-store view (`stVS` is two of them). -/
def stVq (rc : RCtx GF) (D : StableAbs) (g : w64) : IProp GF := ghostVar rc.dur.st (1 : Qp).half.half (D, g)

/-- (hraft_robust, R2) What a crash needs of a write's surviving image, beyond the step's premises: a log
write makes the staged commit index (written with it) durable (for a follower's append that learns a
commit, at most the commit it learns); the vote's second write finds the candidate stored by its first. -/
def winPure (s : SState) (D : StableAbs) (g : w64) : Pend → Prop
  | .app _ => uint.nat g ≤ s.dur.1
  | .cfg _ _ _ => uint.nat g ≤ s.dur.1
  | .fstore _ _ _ lci _ lc => (lc = none → uint.nat g ≤ s.dur.1) ∧
      (∀ v, lc = some v → uint.nat g ≤ Min.min lci v)
  | .vote c _ _ => D.bytes.lookup (go!"LastVoteCand" : List w8) = some c
  | _ => True

/-- (hraft_robust L0, R1 §3) **The window resource of a write that fires `p`** at the state `s` (a
parameter; the crash law and a store's window take `∃ s p`): a quarter of the main goroutine's views of
`s` and of the stable store (R2: the writer keeps the other quarters, so the window it gets back agrees
with its own `s`, `D`, `g`), the facts a crash needs of the surviving image (`winPure`), and the main
goroutine's view of `s` (lent to the store, so `s` is frozen in the window: only the main goroutine
changes it), and the law's premises over `s`. The write's caller lends it (the contracts' `W`); the
write's atomic update gives it back, and the store's crash lemma, if the new contents survived. -/
def winRes (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (p : Pend) : IProp GF :=
  iprop(ghostVar rc.dur.pw (1 : Qp).half (some p) ∗ srvVPq rc s none (pendDp p) ∗ (∃ (D : StableAbs) (g : w64), stVq rc D g ∗ ⌜winPure s D g p⌝) ∗
    pendHyps γ i s p ∗ ⌜pendPre γ i s p⌝)

/-- (stage 3) **The FSM goroutine's answer to a snapshot request** `f` (`fsmSnapshotCh`): nil with the
request's fields set to the FSM's position `x ≥ 1` (the end of an item it processed, `batchEnd`), its
term `tx` (the committed entry's, `CIdx`) and an `FSMSnapshot` of the state there (`fsmSnapOk`); or
`ErrNothingNewToSnapshot` (nothing applied yet). -/
def snapReqQ (γ : GNames) (rc : RCtx GF) (f : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ (x tx m : Nat) (snap : GoInterfaceOk),
      f.[reqSnapshotFuture, go!"index"] ↦ W64 x ∗ f.[reqSnapshotFuture, go!"term"] ↦ W64 tx ∗
      f.[reqSnapshotFuture, go!"snapshot"] ↦ GoInterface.ok snap ∗
      ⌜1 ≤ x⌝ ∗ batchEnd rc m x ∗ (∃ e : Entry, CIdx γ x e ∗ ⌜e.term = tx⌝) ∗
      fsmSnapOk snap rc.snapP x) ∨
    (isRaftErr .nothingNewToSnapshot err ∗
      (∃ (x tx : w64) (sn : GoInterface), f.[reqSnapshotFuture, go!"index"] ↦ x ∗
        f.[reqSnapshotFuture, go!"term"] ↦ tx ∗ f.[reqSnapshotFuture, go!"snapshot"] ↦ sn)))

/-- (stage 3) **A snapshot request** on `fsmSnapshotCh` (`takeSnapshot`): its fields (for the FSM
goroutine to set) and the responder side answering `snapReqQ`. -/
def snapReqP (γ : GNames) (rc : RCtx GF) (f : Loc) : IProp GF :=
  iprop((∃ (x tx : w64) (sn : GoInterface), f.[reqSnapshotFuture, go!"index"] ↦ x ∗
      f.[reqSnapshotFuture, go!"term"] ↦ tx ∗ f.[reqSnapshotFuture, go!"snapshot"] ↦ sn) ∗
    deferResp (f.[reqSnapshotFuture, go!"deferError"]) (snapReqQ γ rc f))

/-- (stage 3) **The main loop's answer to a configurations request** `f` for the FSM position `x`:
nil with the configurations (stage 4: the committed one, a valid configuration `ss` at its index `ci`,
which is the committed log's at `x` unless it is above `x`, `snapCfg`; `takeSnapshot` refuses a
committed index above the snapshot's; stage 3: the bootstrap configuration at index 1), `x` at most `i`'s
durable prefix and `lastApplied` (`durLb`, `applLb`) and the compaction frontier raised to `x`
(`compLb`; one answer for the three: the configurations request is the snapshot goroutine's only
exchange with the main loop, review tier 2); or (the leader loop
during a leadership transfer) `ErrLeadershipTransferInProgress`. -/
def cfgReqQ (γ : GNames) (rc : RCtx GF) (i : SID) (f : Loc) (x : Nat) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ cf : configurations,
      f.[configurationsFuture, go!"configurations"] ↦ cf ∗
      (∃ ss : List Server, cfgVal γ cf.committed' ss ∗
        (⌜x < uint.nat cf.committedIndex'⌝ ∨ snapCfg γ x (uint.nat cf.committedIndex') ss)) ∗
      durLb γ i x ∗ applLb rc x ∗ compLb rc x) ∨
    (isRaftErr .leadershipTransferInProgress err ∗
      ∃ cf : configurations, f.[configurationsFuture, go!"configurations"] ↦ cf))

/-- (stage 3) **A configurations request** on `configurationsCh` (`takeSnapshot`, after the FSM
answered its snapshot request at `x ≥ 1`, the end of an item sent on `fsmMutateCh`): its field and
the responder side answering `cfgReqQ`. -/
def cfgReqP (γ : GNames) (rc : RCtx GF) (i : SID) (f : Loc) : IProp GF :=
  iprop(∃ (x m : Nat), ⌜1 ≤ x⌝ ∗ batchEnd rc m x ∗
    (∃ cf : configurations, f.[configurationsFuture, go!"configurations"] ↦ cf) ∗
    deferResp (f.[configurationsFuture, go!"deferError"]) (cfgReqQ γ rc i f x))

/-- (stage 3) **A user snapshot request** on `userSnapshotCh` (`Raft.Snapshot()`): its `opener` and
the responder side (answer anything, once). -/
def userSnapP (f : Loc) : IProp GF :=
  iprop((∃ op : GoFunc, f.[userSnapshotFuture, go!"opener"] ↦ op) ∗
    deferResp (f.[userSnapshotFuture, go!"deferError"]) (fun _ => iprop(True)))

/-! ## Observers -/

/-- What an observer's filter gets with observation data `d` (and gives back), indexed by the
server's protocol state `s`: for the `Leader` state (`setState(Leader)`, by the main goroutine as
it becomes leader), the server's `leaderIs` witness (hraft_robust L0: no longer its protocol state,
which is in `srvDurInv`); otherwise only
that a `RaftState` observation carries a `uint32` (`s` is then irrelevant). -/
def obsArg (γ : GNames) (i : SID) (s : SState) (d : GoInterface) : IProp GF := by
  classical
  exact if d = leaderObs then iprop(leaderIs γ s.term i)
    else iprop(⌜∀ v, d = interface.mkOk RaftState.ty v → ∃ st : w32, v = #st⌝)

/-- The spec of an observer's filter `fl` for server `i` at `r`: called with a fresh
`Observation{r, d}` and `obsArg γ i s d` (and the term cell, so it may call `r.CurrentTerm()`),
it returns them (for the same `s`). -/
def filterOk (γ : GNames) (rc : RCtx GF) (i : SID) (r : Loc) (fl : GoFunc) : IProp GF :=
  iprop(□ ∀ (ob : Loc) (s : SState) (d : GoInterface) (Φ : val → IProp GF),
    termCell r γ rc i -∗ obsArg γ i s d -∗ ob ↦ Observation.mk r d -∗
    ▷ (∀ b : Bool, obsArg γ i s d -∗ ob ↦ Observation.mk r d -∗ Φ #b) -∗
    WP (App (Val #fl) (Val #ob)) {{ Φ }})

instance filterOk_persistent γ rc i r fl : Persistent (filterOk (GF := GF) γ rc i r fl) := by
  unfold filterOk; infer_instance

/-- A registered observer: no channel, not blocking, a filter meeting `filterOk`. -/
def obsOk (γ : GNames) (rc : RCtx GF) (i : SID) (r : Loc) (o : Loc) : IProp GF :=
  iprop(∃ (fl : GoFunc) (id : w64),
    o.[Observer, go!"channel"] ↦□ chan.nil ∗ o.[Observer, go!"blocking"] ↦□ false ∗
    o.[Observer, go!"filter"] ↦□ fl ∗ o.[Observer, go!"id"] ↦□ id ∗ filterOk γ rc i r fl)

instance obsOk_persistent γ rc i r o : Persistent (obsOk (GF := GF) γ rc i r o) := by
  unfold obsOk; infer_instance

/-- `observersLock`'s resource: the observers map, each registered observer `obsOk`. -/
def observersP (γ : GNames) (rc : RCtx GF) (i : SID) (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (m : GoMap) (mv : GMap w64 Loc),
    r.[Raft, go!"observers"] ↦{DFrac.own q} m ∗ m ↦${DFrac.own q} mv ∗
    [∗map] _k ↦ o ∈ mv, obsOk γ rc i r o)

/-! ## `isRaft` -/

/-- `isRaft`'s immutable fields. -/
def raftImm (r : Loc) (i : SID) : IProp GF :=
  iprop(r.[Raft, go!"protocolVersion"] ↦□ (W64 3) ∗
    r.[Raft, go!"localID"] ↦□ (i : ServerID) ∗ r.[Raft, go!"localAddr"] ↦□ (i : ServerAddress) ∗
    r.[Raft, go!"preVoteDisabled"] ↦□ false ∗ (∃ nlt : Bool, r.[Raft, go!"noLegacyTelemetry"] ↦□ nlt) ∗
    r.[Raft, go!"RestoreCommittedLogs"] ↦□ false)

instance raftImm_persistent r i : Persistent (raftImm (GF := GF) r i) := by
  unfold raftImm; infer_instance

/-! ### The stores' window families (hraft_robust, R3 Q2) -/

/-- (hraft_robust) The log store write `op` that the pending step `p` at state `s` makes (its `StoreLogs`
or `DeleteRange`; `False` for a step that is not a log write). A follower's append may re-store, from
`prev + k + 1`, entries the protocol log already has (R4a: `appendEntries` compares with the raw last log
index, below the snapshot's after a restart over a compacted log); they equal the log's. -/
def pendLogOk (s : SState) : Pend → LogOp → Prop
  | .app es, op => op = .store (s.log.length + 1) es
  | .cfg e _ _, op => op = .store (s.log.length + 1) [e]
  | .fstore prev _ ents _ j _, op => ∃ k, k ≤ j ∧ op = .store (prev + k + 1) (ents.drop k) ∧
      ∀ m, k ≤ m → m < j → ent s.log (prev + m + 1) = ents[m]?
  | .trunc prev _ _ _ j, op => op = .del (prev + 1 + j) s.log.length
  | .discard _, op => ∃ mn mx, op = .del mn mx
  | _, _ => False

/-- (hraft_robust) The stable store write `op` that the pending step `p` at state `s` makes. -/
def pendStOk (s : SState) : Pend → StableOp → Prop
  | .vote _ _ _, op => op = .setU (go!"LastVoteTerm" : List w8) (W64 s.term)
  | .term (.set t), op => op = .setU (go!"CurrentTerm" : List w8) (W64 t)
  | .term .elect, op => op = .setU (go!"CurrentTerm" : List w8) (W64 (s.term + 1))
  | _, _ => False

/-- (hraft_robust) **Raft's window family for its log store** (`isLogStore`'s `Wl`): a write of the main
goroutine lends `winRes` of the step it fires; the snapshot goroutine's compaction (`DeleteRange` up to the
frontier) lends only the frontier's bound. (Pre-model writes, `BootstrapCluster` on a fresh disk: stage
R5/the kit.) -/
def logWin (γ : GNames) (rc : RCtx GF) (i : SID) (op : LogOp) : IProp GF :=
  iprop((∃ (s : SState) (p : Pend), ⌜pendLogOk s p op⌝ ∗ winRes γ rc i s p) ∨
    (∃ mn mx : Nat, ⌜op = .del mn mx⌝ ∗ compLb rc mx ∗ latLb rc mx ∗ durLb γ i mx))

/-- (hraft_robust) **Raft's window family for its stable store** (`isStableStore`'s `Ws`): the vote's second
write and the term writes lend `winRes`; the vote's first write (`LastVoteCand`) lends nothing. -/
def stWin (γ : GNames) (rc : RCtx GF) (i : SID) (op : StableOp) : IProp GF :=
  iprop((∃ (s : SState) (p : Pend), ⌜pendStOk s p op⌝ ∗ winRes γ rc i s p) ∨
    (∃ vb : List w8, ⌜op = .set (go!"LastVoteCand" : List w8) vb⌝) ∨
    (∃ (kb : List w8) (v : w64) (D : StableAbs) (g : w64),
      ⌜op = .setU kb v ∧ (D.ints.lookup kb).getD (W64 0) = v⌝ ∗ stVq rc D g ∗
      ghostVar rc.dur.pw (1 : Qp).half (none : Option Pend)))

/-- (hraft_robust) **Raft's close obligation for its snapshot store** (`isSnapStore`'s `Qc`): the closed
snapshot's facts (`latestOk`) and its index durable at `i` or installed while `i` followed (what
`latestDur` keeps), given the bytes' bound (the store has it from its Go slice: its commit and its crash
lemma; R4b). Persistent facts only, so the FSM's `Persist` can be given it from `snapP`. -/
def snapWin (γ : GNames) (rc : RCtx GF) (i : SID) (m : SnapshotMeta) (b : List w8) : IProp GF :=
  iprop(⌜b.length < 2 ^ 63⌝ -∗ latestOk γ rc (some (m, b)) ∗
    (durLb γ i (uint.nat m.Index') ∨ snapFollow γ i (uint.nat m.Index') (uint.nat m.Term')))

/-- `isRaft`'s interface values and their contracts. (Stage 3: the log store over a partial map,
not a `MonotonicLogStore`; the snapshot store `isSnapStore` with `io.EOF`'s value; the transport and
the FSM with the FSMs' snapshot meaning `rc.snapP`.) -/
def raftIfaces (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop(∃ (logsI stableI snapsI transI fsmI : GoInterfaceOk) (rpcCh : Loc) (eof : GoInterface),
    r.[Raft, go!"logs"] ↦□ (GoInterface.ok logsI) ∗ isLogStore logsI rc.ownL (logWin γ rc i) ∗
    ⌜go.typeSetContains logsI.ty MonotonicLogStore.ty = false⌝ ∗
    r.[Raft, go!"stable"] ↦□ (GoInterface.ok stableI) ∗ isStableStore stableI rc.ownS (stWin γ rc i) ∗
    r.[Raft, go!"snapshots"] ↦□ (GoInterface.ok snapsI) ∗ isSnapStore snapsI rc.ownSS eof (snapWin γ rc i) ∗
    globalAddr io.EOF ↦□ eof ∗
    r.[Raft, go!"trans"] ↦□ (GoInterface.ok transI) ∗ isTransport transI γ rc.snapP i rpcCh ∗
    ⌜go.typeSetContains transI.ty WithPreVote.ty = true⌝ ∗
    r.[Raft, go!"rpcCh"] ↦□ rpcCh ∗
    r.[Raft, go!"fsm"] ↦□ (GoInterface.ok fsmI) ∗ isFSM fsmI γ i rc.fsmOwn rc.respP rc.snapP ∗
    ⌜fsmNotBatching fsmI⌝)

set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance raftIfaces_persistent r γ rc i : Persistent (raftIfaces (GF := GF) r γ rc i) := by
  unfold raftIfaces; infer_instance

def latestCfgN : Namespace := raftN.@"latestConfiguration"

/-- (stage 3, D33) The `latestConfiguration` cell's invariant body: the `atomic.Pointer[Configuration]`
is `nil` (API-S4-2: a non-member's, until its first configuration entry; `getLatestConfiguration` returns
`Configuration{}`) or points to a read-only copy of a configuration with no servers or a valid one (`cfgOpt`;
stage 4; stage 3: a bootstrap configuration, `cfgIs`). -/
def latestCfgCell (r : Loc) (γ : GNames) : IProp GF :=
  iprop(∃ p : Loc,
    sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p ∗
    (⌜p = null⌝ ∨ ∃ cfg : Configuration, p ↦□ cfg ∗ cfgOpt γ cfg))

/-- `isRaft`'s configuration (`conf`, never stored again: `config()` returns `c` with
`cfgOk c i`) and (stage 3, review T1-6; D33: an `atomic.Pointer`) the latest cluster configuration: an
invariant cell (stored by `NewRaft` and, by `setLatestConfiguration`, the main goroutine whenever its
latest configuration changes; read with `Load`), always pointing to a configuration with no servers or a
valid one (`latestCfgCell`). -/
def raftConf (r : Loc) (γ : GNames) (i : SID) : IProp GF :=
  iprop(∃ c : Config,
    sync.atomic.ownValue (r.[Raft, go!"conf"]) DFrac.discard (interface.mkOk Config.ty #c) ∗
    ⌜cfgOk c i⌝ ∗
    inv latestCfgN (latestCfgCell r γ))

instance raftConf_persistent r γ i : Persistent (raftConf (GF := GF) r γ i) := by
  unfold raftConf; infer_instance

/-- `isRaft`'s cells. -/
def raftCells (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop(termCell r γ rc i ∗ cidxCell r γ rc i ∗ srvDurInv γ rc i ∗ stateCell r rc ∗
    appliedCell r rc ∗ cftCell r ∗ ltipCell r ∗
    dghostVar rc.names.llb DFrac.discard (none : Option (w64 × w64 × w64 × w64)))

instance raftCells_persistent r γ rc i : Persistent (raftCells (GF := GF) r γ rc i) := by
  unfold raftCells; infer_instance

/-- `isRaft`'s locks and routines group. -/
def raftLocks (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop(sync.isMutex (r.[Raft, go!"raftState"].[raftState, go!"lastLock"]) (lastLockInv r γ rc i) ∗
    rwLock leaderLockN (r.[Raft, go!"leaderLock"]) (leaderLockP r) ∗
    rwLock lastContactLockN (r.[Raft, go!"lastContactLock"]) (lastContactP r) ∗
    rwLock observersLockN (r.[Raft, go!"observersLock"]) (observersP γ rc i r) ∗
    rgOk r)

instance raftLocks_persistent r γ rc i : Persistent (raftLocks (GF := GF) r γ rc i) := by
  unfold raftLocks; infer_instance

/-- The channel field `fld` of `r` holds a dead channel (never sent on, never closed). -/
def deadField (V : Type) [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] (r : Loc)
    (fld : GoString) : IProp GF :=
  iprop(∃ ch : Loc, r.[Raft, fld] ↦□ ch ∗ deadChan V ch)

instance deadField_persistent V [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] r fld :
    Persistent (deadField (GF := GF) V r fld) := by
  unfold deadField; infer_instance

/-- `isRaft`'s channels: `applyCh` (a bag of client futures, `applyP`), `fsmMutateCh` (the FSM
batch channel, `fsmP`), `leaderCh` (its location; the main goroutine owns it), (stage 2)
`verifyCh` (a bag of verify futures, `verifyP`) and `leadershipTransferCh` (a bag of transfer
futures, `ltfP`), (stage 3) `fsmSnapshotCh` (snapshot requests, `snapReqP`), `userSnapshotCh` (user
snapshot requests, `userSnapP`) and `configurationsCh` (configurations requests, `cfgReqP`), (stage 4)
`configurationChangeCh` (a bag of configuration change futures, `ccfP`), and the channels that are
never used in scope (`shutdownCh` is never closed). -/
def raftChans (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop((∃ applyCh : Loc, r.[Raft, go!"applyCh"] ↦□ applyCh ∗
      ∃ γa : ChanNames, isChanBag (V := Loc) γa applyCh (applyP γ rc i)) ∗
    (∃ vch : Loc, r.[Raft, go!"verifyCh"] ↦□ vch ∗
      ∃ γv : ChanNames, isChanBag (V := Loc) γv vch (verifyP γ rc i vch)) ∗
    (∃ lch : Loc, r.[Raft, go!"leadershipTransferCh"] ↦□ lch ∗
      ∃ γt : ChanNames, isChanBag (V := Loc) γt lch (ltfP γ i)) ∗
    (∃ fsmCh : Loc, r.[Raft, go!"fsmMutateCh"] ↦□ fsmCh ∗
      isSpsc (V := GoInterface) rc.names.fsmCh fsmCh (fsmP γ rc i) (fun _ => iprop(False))) ∗
    (∃ leaderCh : Loc, r.[Raft, go!"leaderCh"] ↦□ leaderCh) ∗
    (∃ sch : Loc, r.[Raft, go!"fsmSnapshotCh"] ↦□ sch ∗
      ∃ γs : ChanNames, isChanBag (V := Loc) γs sch (snapReqP γ rc)) ∗
    (∃ uch : Loc, r.[Raft, go!"userSnapshotCh"] ↦□ uch ∗
      ∃ γu : ChanNames, isChanBag (V := Loc) γu uch userSnapP) ∗
    (∃ cch : Loc, r.[Raft, go!"configurationsCh"] ↦□ cch ∗
      ∃ γq : ChanNames, isChanBag (V := Loc) γq cch (cfgReqP γ rc i)) ∗
    (∃ cch : Loc, r.[Raft, go!"configurationChangeCh"] ↦□ cch ∗
      ∃ γq : ChanNames, isChanBag (V := Loc) γq cch (ccfP γ)) ∗
    deadField Unit r go!"shutdownCh" ∗
    deadField Loc r go!"userRestoreCh" ∗
    deadField Loc r go!"bootstrapCh" ∗
    deadField Unit r go!"leaderNotifyCh" ∗
    deadField Unit r go!"followerNotifyCh")

instance raftChans_persistent r γ rc i : Persistent (raftChans (GF := GF) r γ rc i) := by
  unfold raftChans; infer_instance

/-- The body of `isRaft` (see `isRaft`). -/
def isRaftDef (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop(Inv γ ∗ isSrv γ i ∗ raftImm r i ∗ raftIfaces r γ rc i ∗ raftConf r γ i ∗
    raftCells r γ rc i ∗ raftLocks r γ rc i ∗ raftChans r γ rc i ∗ ⌜γ.cv = cfgDec γ.srvs⌝)

/-- **What every goroutine of server `i` knows about `r`** (persistent): the protocol (stage 4: whose
decoding of a configuration's voters is `DecodeConfiguration`'s, `cfgDec`), the
immutable fields, the contracts of the interface values (with the client handles of `rc`), the
`Config` (`cfgOk`), the cells, locks and channels. Sealed: use the laws of `core/Laws.lean`. -/
@[irreducible] def isRaft (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  isRaftDef r γ rc i
theorem isRaft_unseal : @isRaft = @isRaftDef := by funext; with_unfolding_all rfl

instance isRaft_persistent r γ rc i : Persistent (isRaft (GF := GF) r γ rc i) := by
  rw [isRaft_unseal]; unfold isRaftDef; infer_instance

/-! ## The commitment -/

/-- **The commitment's lock invariant** (`cm.Mutex`), for the leader `i` of term `T`: (stage 4) the
commitment's half of the configuration it counts (`ccfgOwn γ i T p`, the main goroutine holds the
other: `commitment.setConfiguration` joins them, `gprot.installCfg_upd`), a configuration entry at
`p` of `llog T`, whose voters are the match indexes' keys (stage 3: the fixed voters); each match
index is `0`, acknowledged in `T`, or (stage 3) the commit index of a valid install of `T` the
replication goroutine of `T` counted (`sendLatestSnapshot`'s `commitment.match`: `lciOk γ T m`); the
commit index is `0`, or past the election part and covered by a recorded commit of `T`
(`gprot.commit_upd`, `gprot.commit_or_snap`, by a quorum of the configuration at `p`); the start
index is past the leader's log at its election; the commit channel is a notification bag. -/
def commitInv (γ : GNames) (i : SID) (T : Nat) (cm : Loc) : IProp GF :=
  iprop(∃ (ch : Loc) (mi : GoMap) (mm : GMap SID w64) (ci si : w64) (n0 p : Nat) (e : Entry),
    cm.[commitment, go!"commitCh"] ↦ ch ∗ notifyChan ch ∗
    cm.[commitment, go!"matchIndexes"] ↦ mi ∗ mi ↦$ mm ∗
    ccfgOwn γ i T p ∗ llogIdx γ T p e ∗
    ⌜e.kind = kConfig ∧ (∀ j, (mm.lookup j).isSome ↔ j ∈ γ.cv e.data) ∧
      (γ.cv e.data).length < 2 ^ 32⌝ ∗
    ([∗map] j ↦ m ∈ mm, ⌜m = W64 0⌝ ∨ ackIs γ j T (uint.nat m) ∨ lciOk γ T (uint.nat m)) ∗
    cm.[commitment, go!"commitIndex"] ↦ ci ∗
    (⌜ci = W64 0⌝ ∨ (⌜n0 < uint.nat ci⌝ ∗ ∃ k p, ⌜uint.nat ci ≤ k⌝ ∗ commitIs γ T k p)) ∗
    cm.[commitment, go!"startIndex"] ↦□ si ∗ len0Is γ T n0 ∗ ⌜uint.nat si = n0 + 1⌝ ∗
    leaderIs γ T i ∗ Inv γ)

/-- The commitment `cm` of the leader `i` of term `T` (persistent): its start index (read-only,
never written after `newCommitment`; `configurationChangeChIfStable` reads it without the lock),
(review T1-2) `len0 + 1` (so a commit index `≥ startIndex` is past the election-time log and covered
by a recorded commit of `T`, `mainOwnAt`'s leader arm), and its lock. -/
def isCommitment (γ : GNames) (i : SID) (T : Nat) (cm : Loc) : IProp GF :=
  iprop((∃ (si : w64) (n0 : Nat), cm.[commitment, go!"startIndex"] ↦□ si ∗ len0Is γ T n0 ∗
      ⌜uint.nat si = n0 + 1⌝) ∗
    sync.isMutex (cm.[commitment, go!"Mutex"]) (commitInv γ i T cm))

instance isCommitment_persistent γ i T cm : Persistent (isCommitment (GF := GF) γ i T cm) := by
  unfold isCommitment; infer_instance

/-! ## Replication goroutines -/

/-- The `Server` value of voter `j` (`Voter`, address = id). -/
def voterSrv (j : SID) : Server := Server.mk (W64 0) j j

/-- (stage 2) The ghost names of a replication goroutine's stop channel: the channel's and its
"closed" flag; (review tier-2 5) the send token's. -/
structure StopNames where
  ch : ChanNames
  done : GName
  snd : GName

/-- (review tier-2 5) **The stop channel's send token** (exclusive): only the main goroutine sends on
it, once (`startStopReplication`'s `stopCh <- lastIdx` before `close(stopCh)`); a buffered value
holds the token, so the sender, holding it, finds the buffer empty (the send does not block). -/
def stopSendTok (γs : StopNames) : IProp GF := dghostVar γs.snd (.own 1) false

/-- (stage 2) The stop channel's invariant: a buffered `chan uint64` (capacity 1) holding at most one
value (stage 4: `startStopReplication` stops a removed server's goroutine with `stopCh <- lastIdx`
then `close(stopCh)`; the value is any `uint64`; stage 3: nothing was ever sent; review tier-2 5: a
buffered value holds the send token, `stopSendTok`), open with the closer's half of the flag at
`false`, or closed with the flag `true` forever. -/
def stopInv (γs : StopNames) : IProp GF :=
  iprop(∃ st : ChanState w64, ownChan γs.ch w64 st ∗
    (match st with
      | .Buffered [] => dghostVar γs.done (.own (1 : Qp).half) false
      | .Buffered [_] => dghostVar γs.done (.own (1 : Qp).half) false ∗ stopSendTok γs
      | .Closed [] => dghostVar γs.done .discard true
      | .Closed [_] => dghostVar γs.done .discard true ∗ stopSendTok γs
      | _ => iprop(False)))

/-- **The stop channel** of a replication goroutine (persistent; stage 2: a close-only broadcast
channel, as Perennial's `Idioms/Broadcast`, for `uint64` and capacity 1): closed (only) by the
main goroutine (`stopCloser`); any goroutine may receive on it any number of times, before and
after the close (`replicate`'s loop receives again after a pipeline stopped on the close). -/
def stopChan (γs : StopNames) (ch : Loc) : IProp GF :=
  iprop(isChan ch γs.ch w64 ∗ inv stopN (stopInv γs))

instance stopChan_persistent γs ch : Persistent (stopChan (GF := GF) γs ch) := by
  unfold stopChan; infer_instance

/-- (stage 2) The right to close the stop channel (the main goroutine's), (review tier-2 5) before
its one send: with the send token (`wp_stop_send` spends it, giving `stopCloseRight`). -/
def stopCloser (γs : StopNames) : IProp GF :=
  iprop(dghostVar γs.done (.own (1 : Qp).half) false ∗ stopSendTok γs)

/-- (review tier-2 5) The right to close the stop channel, without the send token (after the send, or
dropping it: `stopCloser_close`). -/
def stopCloseRight (γs : StopNames) : IProp GF := dghostVar γs.done (.own (1 : Qp).half) false

/-- The facts about a `*followerReplication` shared by the main goroutine and the replication
goroutine (persistent): for server `j ≠ i` (stage 4: any of the servers, a member of the leader's
latest configuration with any suffrage when started; stage 3: a voter), term `T`, commitment `cm`;
(stage 4) its `peer`, read-only: the `Server` with ID and address `j` and the suffrage it had when the
goroutine started (`startStopReplication` rewrites it, under `peerLock`, only when the address
changed, never in scope: every valid configuration has `Address = ID`, `srvsOk`); (stage 2) its
notify set
holds registered verify futures with `j`'s vote tokens (`notifyEntry`); `triggerDeferErrorCh`
carries the leadership transfer's `*deferError`s (answer anything, once); `nextIndex` (a plain
`uint64` accessed with `atomic.Load/StoreUint64`) is half in an invariant (any goroutine's atomic
load opens it: `pickServer`, the transfer goroutine) and half the writer's (`replOwn`: the
replication goroutine, lent to the pipeline decoder; a store needs both halves; the writer's plain
read `s.nextIndex-1` its own half). No fact about its value is needed (REPL-3). -/
def replShared (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc) :
    IProp GF :=
  iprop(∃ (cm stopCh trig notif sd tde : Loc) (γs : StopNames),
    s.[followerReplication, go!"currentTerm"] ↦□ (W64 T) ∗
    (∃ sf : ServerSuffrage, s.[followerReplication, go!"peer"] ↦□ Server.mk sf j j) ∗
    isSrv γ j ∗ ⌜j ≠ i⌝ ∗
    rwLock peerLockN (s.[followerReplication, go!"peerLock"]) (fun _ => iprop(True)) ∗
    s.[followerReplication, go!"commitment"] ↦□ cm ∗ isCommitment γ i T cm ∗
    s.[followerReplication, go!"stopCh"] ↦□ stopCh ∗ stopChan γs stopCh ∗
    s.[followerReplication, go!"triggerCh"] ↦□ trig ∗ notifyChan trig ∗
    s.[followerReplication, go!"notifyCh"] ↦□ notif ∗ notifyChan notif ∗
    s.[followerReplication, go!"stepDown"] ↦□ sd ∗ notifyChan sd ∗
    s.[followerReplication, go!"triggerDeferErrorCh"] ↦□ tde ∗
    (∃ γt : ChanNames, isChanBag (V := Loc) γt tde
      (fun d => deferResp d (fun _ => iprop(True)))) ∗
    inv nextIdxN iprop(∃ v : w64,
      s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} v) ∗
    rwLock replContactLockN (s.[followerReplication, go!"lastContactLock"])
      (fun q => iprop(∃ t : time.Time, s.[followerReplication, go!"lastContact"] ↦{DFrac.own q} t)) ∗
    (∃ vch : Loc, r.[Raft, go!"verifyCh"] ↦□ vch ∗
      sync.isMutex (s.[followerReplication, go!"notifyLock"])
        iprop(∃ (m : GoMap) (M : GMap Loc Unit), s.[followerReplication, go!"notify"] ↦ m ∗ m ↦$ M ∗
          [∗map] v ↦ _u ∈ M, notifyEntry γ rc i T vch j v)))

/-- The stop channel of `s` with its names (persistent; the closer is the main goroutine,
`stopCloser`; receivers need nothing more). -/
def replStopCh (s : Loc) (γs : StopNames) : IProp GF :=
  iprop(∃ stopCh : Loc, s.[followerReplication, go!"stopCh"] ↦□ stopCh ∗ stopChan γs stopCh)

/-- **The main goroutine's handle on a replication goroutine** for server `j`: the shared facts
and the right to close its stop channel. -/
def replMain (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc) :
    IProp GF :=
  iprop(replShared r γ rc i T j s ∗
    ∃ γs : StopNames, replStopCh s γs ∗ stopCloser γs)

/-- **A replication goroutine's resources** (`replicate(s)`, leader `i` of term `T`): the shared
facts, `leaderIs γ T i` and `termLb γ i T`, the right to receive on its stop channel, and its own
fields (`failures`, `allowPipeline`; stage 2: the writer's half of `nextIndex`, REPL-3). -/
def replOwn (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (s : Loc) : IProp GF :=
  iprop(∃ j : SID, replShared r γ rc i T j s ∗ leaderIs γ T i ∗ termLb γ i T ∗
    (∃ γs : StopNames, replStopCh s γs) ∗
    (∃ v : w64, s.[followerReplication, go!"failures"] ↦ v) ∗
    (∃ b : Bool, s.[followerReplication, go!"allowPipeline"] ↦ b) ∗
    (∃ v : w64, s.[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} v))

/-! ## The main goroutine -/

-- (hraft_robust L0) `voteMatches` moved to the crash-state section.

/-- **The main goroutine's exclusive resources** (at every iteration of `run`, and passed to the
handlers): its protocol state `s` (and half of its durable-prefix view), (stage 3) its half of the
pending-install record (none), the compaction frontier's authority (at most `lastApplied`), the
stable store, its
halves of the `lastLog`, `state` and `lastApplied` ghost variables (the state `Leader` only with
`leaderIs` and, stage 2, its publications' bound `pubOwn`, at most what it handed to the FSM), its
half of the pending appends (none, stage 2), the verify futures' registry (stage 2, `verifyRegistry`; every registered
future has a non-zero quorum size), the FSM producer's state, the `configurations` field (stage 4; stage 3:
latest = committed = the bootstrap configuration at index 1):
* the latest at `li`, the last configuration entry of the protocol log (`0`: none, no servers);
* the committed at `ci`: the latest (`ci = li`), or its parent (the previous configuration entry) while
  the FSM position `a` is below `li` (`processConfigurationLogEntry` makes the previous latest the
  committed one; the commit index reaching `li` makes the latest committed); (review T1-1) `ci` is
  committed by a commit of a term `≤ s.term` whose leader log has the server's entry there
  (`gprot.cmtIdx`, from `gprot.cfgPrevCommitted` or `gprot.cmtIdx_dur`: so an `AppendEntries` of the
  current term truncates only above `ci`, `gprot.cmtIdx_llog`, and `ci ≥ 1` is an entry of the
  committed log, `gprot.cmtIdx_CIdx`);
* (review T1-1) the commit index is at most the FSM position `a` (`processLogs(idx)` follows every
  `setCommitIndex(idx)`; `installSnapshot` raises only `a`, to the snapshot's index);
* as leader of `s.term` (also): its half of the configuration its commitment counts, the latest
  (`ccfgOwn`; the commitment's lock holds the other), and what it knows of its commits: its commit
  index is within its election-time log `n0` or covered by a recorded commit of its term, and a
  latest configuration that is the committed one is within `n0` or covered by a recorded commit of its
  term (stage 4, FOLLOW-1; was: within `n0` or the commit index, not monotone in it) (what
  `configurationChangeChIfStable` checks before `appendConfigurationEntry`, `gprot.leaderAppendCfg_upd`);
`leaderCh` (owned alone: nobody receives). Not included:
the main goroutine's thread token (passed separately), the leader state (`leaderStateAny`, or `leaderOwn` inside `runLeader`). -/
def mainOwnAt (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) : IProp GF :=
  iprop(∃ (a : Nat) (sst : StableAbs) (cfg ccfg : Configuration) (cidx li : w64)
      (lch : Loc) (γl : ChanNames) (bs : List Bool) (c : Nat),
    srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗
    (∃ g : w64, stVS rc sst g ∗ ⌜uint.nat g ≤ s.dur.1⌝) ∗ ⌜voteMatches sst s⌝ ∗
    ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
    ghostVar rc.names.state (1 : Qp).half st ∗
    (⌜st ≠ stLeader⌝ ∨ leaderIs γ s.term i ∗ (∃ m : Nat, pubOwn γ i s.term m ∗ ⌜m ≤ a⌝) ∗
      ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
      ∃ n0 : Nat, len0Is γ s.term n0 ∗
        (⌜s.cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜s.cidx ≤ k⌝) ∗
        (⌜cidx ≠ li ∨ uint.nat li ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat li ≤ k⌝)) ∗
    ⌜True⌝ ∗
    verifyRegistry γ rc i ∗
    monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1 ∧ s.cidx ≤ a⌝ ∗ fsmProd γ rc a ∗
    ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
    monoNatAuthOwn rc.dur.comp (1 : Qp).half c ∗ ⌜c ≤ a⌝ ∗
    r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
    cfgAtIs γ s.log (uint.nat li) cfg ∗ cfgAtIs γ s.log (uint.nat cidx) ccfg ∗
    ⌜uint.nat li = lastCfgIdx s.log ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (s.log.take (uint.nat li - 1)) ∧ a < uint.nat li))⌝ ∗
    cmtIdx γ s.term s.log (uint.nat cidx) ∗
    r.[Raft, go!"leaderCh"] ↦□ lch ∗ isChan lch γl Bool ∗ ownChan γl Bool (.Buffered bs) ∗
    ⌜sint.Z γl.chanCap = 1 ∧ bs.length ≤ 1⌝)

/-- (stage 4, hub L1) **`mainOwnAt` of a leader whose latest configuration is the committed one**
(`configurations.committedIndex = latestIndex`, what `configurationChangeChIfStable` checks): `mainOwnAt r γ rc
i s stLeader` with the committed index `cidx := li`. `configurationChangeChIfStable` returns it with the
channel, `appendConfigurationEntry` takes it (its new entry's parent is then the committed configuration). -/
def mainOwnAtSt (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) : IProp GF :=
  iprop(∃ (a : Nat) (sst : StableAbs) (cfg ccfg : Configuration) (li : w64)
      (lch : Loc) (γl : ChanNames) (bs : List Bool) (c : Nat),
    srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗
    (∃ g : w64, stVS rc sst g ∗ ⌜uint.nat g ≤ s.dur.1⌝) ∗ ⌜voteMatches sst s⌝ ∗
    ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
    ghostVar rc.names.state (1 : Qp).half stLeader ∗
    (leaderIs γ s.term i ∗ (∃ m : Nat, pubOwn γ i s.term m ∗ ⌜m ≤ a⌝) ∗
      ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
      ∃ n0 : Nat, len0Is γ s.term n0 ∗
        (⌜s.cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜s.cidx ≤ k⌝) ∗
        (⌜uint.nat li ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat li ≤ k⌝)) ∗
    ⌜True⌝ ∗
    verifyRegistry γ rc i ∗
    monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1 ∧ s.cidx ≤ a⌝ ∗ fsmProd γ rc a ∗
    ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
    monoNatAuthOwn rc.dur.comp (1 : Qp).half c ∗ ⌜c ≤ a⌝ ∗
    r.[Raft, go!"configurations"] ↦ configurations.mk ccfg li cfg li ∗
    cfgAtIs γ s.log (uint.nat li) cfg ∗ cfgAtIs γ s.log (uint.nat li) ccfg ∗
    ⌜uint.nat li = lastCfgIdx s.log⌝ ∗
    cmtIdx γ s.term s.log (uint.nat li) ∗
    r.[Raft, go!"leaderCh"] ↦□ lch ∗ isChan lch γl Bool ∗ ownChan γl Bool (.Buffered bs) ∗
    ⌜sint.Z γl.chanCap = 1 ∧ bs.length ≤ 1⌝)

/-- The main goroutine's resources at some protocol state `s` and raft state `st`, between the
handlers of `run`: in the state `Leader` (just elected, `runLeader` not yet entered) nothing was
appended since the election (`len0Is`, which `runLeader`'s commitment needs), and (stage 4) the
commitment's half of the configuration it will count (`newCommitment` takes it). -/
def mainOwn (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) : IProp GF :=
  iprop(∃ (s : SState) (st : w32), mainOwnAt r γ rc i s st ∗
    (⌜st ≠ stLeader⌝ ∨ len0Is γ s.term s.log.length ∗ ccfgOwn γ i s.term (lastCfgIdx s.log)))

/-- The leader state fields outside `runLeader` (any values). -/
def leaderStateAny (r : Loc) (rc : RCtx GF) : IProp GF :=
  iprop(∃ (cc : GoChan) (cm : Loc) (infl : GoSlice) (rs nt : GoMap) (sd : GoChan),
    ghostMapAuth rc.names.vnm (1 : Qp).half (∅ : GMap Loc Unit) ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"commitCh"] ↦ cc ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"commitment"] ↦ cm ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"inflight"] ↦ infl ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"replState"] ↦ rs ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"notify"] ↦ nt ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"stepDown"] ↦ sd)

/-- One inflight future: the future, its index and entry. -/
structure InflightItem where
  f : Loc
  k : Nat
  e : Entry

/-- **The leader state** of the main goroutine during `runLeader` of term `T`: `leaderIs`, the
commit channel and the commitment (`isCommitment`, start index `len0 + 1`), the inflight futures
(in index order, each dispatched in `T`: an entry of `llog T`, with its responder obligation),
the replication goroutines' handles (one per started server `j ≠ i`; which ones: `leader.leaderOwnC`),
`notify` (stage 2) the
registered verify futures with their responder sides, `stepDown` a notification bag. -/
def leaderOwn (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) : IProp GF :=
  iprop(∃ (cc : GoChan) (cm : Loc) (infl : GoSlice) (fs : List InflightItem) (rs : GoMap)
      (rmap : GMap SID Loc) (nt : GoMap) (sd : GoChan) (n0 : Nat),
    leaderIs γ T i ∗ len0Is γ T n0 ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"commitCh"] ↦ cc ∗ notifyChan cc ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"commitment"] ↦ cm ∗ isCommitment γ i T cm ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"inflight"] ↦ infl ∗
    infl ↦* fs.map InflightItem.f ∗ ownSliceCap Loc infl (DFrac.own 1) ∗
    ⌜(fs.map InflightItem.k).Pairwise (· < ·)⌝ ∗
    ([∗list] x ∈ fs, futResp γ rc i x.f x.k x.e ∗ llogIdx γ T x.k x.e) ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"replState"] ↦ rs ∗ rs ↦$ rmap ∗
    ([∗map] j ↦ s ∈ rmap, replMain r γ rc i T j s) ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"notify"] ↦ nt ∗
    (∃ (NM : GMap Loc Unit) (vch : Loc), nt ↦$ NM ∗ ghostMapAuth rc.names.vnm (1 : Qp).half NM ∗
      r.[Raft, go!"verifyCh"] ↦□ vch ∗
      [∗map] v ↦ _u ∈ NM, leaderNotifyEntry γ rc i T vch v) ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"stepDown"] ↦ sd ∗ notifyChan sd)

end defs

end github_com.hashicorp.raft

end Perennial
