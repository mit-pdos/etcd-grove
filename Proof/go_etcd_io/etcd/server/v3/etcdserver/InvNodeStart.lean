/-
**The raft wrapper's construction** (stage R8b-C of the raft v3.7 retarget, 2026-10-16; D12:
`notes/decisions.md`, "The new cluster's start"): what `newRaftNode` (`raft.go`) and the new
cluster's `bootstrappedRaft.newRaftNode` (`bootstrap.go`) are specified over, beside
`InvRaftNode.lean`'s predicates of the running wrapper. Lean-first (no Rocq counterpart).

* **The contracts** on the names-only callees and on what Perennial does not model, persistent
  triples the specs take in their preconditions (as `isServerBuilt` takes the names-only parts'
  contracts, `clusterVersionOk`): `NewRaftLoggerZap` (`zap_raft.go`, names-only: some logger
  interface, `rnLoggerZapOk`); (until premise-fixes-4, 2026-11-10, raft's `SetLogger` too,
  `rnSetLoggerOk`, false in the model: raft's initializer dropped its globals; since, raft keeps
  `raftLoggerMu` owning `raftLogger` in `isInitialized` and proves `SetLogger.spec`, a callee of
  `newRaftNode`'s proof); `contention.NewTimeoutDetector`
  (names-only: `isRNTimeoutDetector`, `rnTimeoutDetectorOk`); `time.NewTicker` (`isRNTicker`;
  since 2026-11-03 no contract: Perennial's proved specs of `NewTicker` and `Ticker.Stop` are
  callees of `newRaftNode`'s proof, `isRNTicker_of_time`; until then `rnTickerOk`); the server's package
  globals `raftStatus` (a function value) and `raftStatusMu` (the mutex protecting it; not in the
  package facts `srvRaftInit`, which hold the metrics only: `rnRaftStatusOk`, the mutex's
  invariant owning the function); `serverstorage.NewStorage` (names-only: the WAL, `isRNWal`,
  `rnNewStorageOk`); `membership.RaftCluster.IsIDRemoved` (translated and proved,
  `membership.RaftCluster.IsIDRemoved.spec_static`; here as some boolean, `rnClusterOk`, from which
  the `isIDRemoved` closure meets `isRNIDRemoved`; `bootstrapContract`'s post gives it, a
  consequence of its `isRaftCluster`).
* **`rnBuilt E γ r cv`**: the wrapper as `newRaftNode(cv)` leaves it, before `NewServer` copies
  it into `EtcdServer.r` (`r: *b.raft.newRaftNode(...)`, by value), sets its `transport` and
  `start` runs it: the struct value owned whole at `r`, with the components `newRaftNode` alone
  provides (`rnParts`, persistent, on the value: the detector, the ticker, `stopped`'s bag,
  `done`'s broadcast channel, `msgSnapC`'s bag, `applyc`'s SPSC channel, `readStateC`'s bag of
  answered read states), `tickMu` a fresh `RWMutex` (its guard over `latestTickTs` is made where
  the struct finally lives: `isRaftNode_of_rnParts`, `NodeStart.lean`, which adds what the node
  and the server provide, `rnEnvOk`, the node's contract, the storage's, the transport's),
  `cfg`'s fields as the caller gave them, both halves of `applyc` with `cum` at `[[]]`, and the
  right to close `done`, and the claim on the stop's escrow (`rnStopClaim`). The names `γ` are the
  wrapper's (`RNNames`): `newRaftNode` allocates `ap`, `cum`, `done` and `sc`, the rest are the
  caller's.
* **`rnStartCfg`**: the raft configuration and the peers a new cluster's node boots with (pure),
  shared by `bootstrappedRaft.newRaftNode.spec`, `NodeStartSpec` and `bootOk`.
* `srvIdxOk_boot`: the bootstrap log (`srvBootLogOk`) passes the server's `srvIdxOk` at the applied
  index `0` (its entries are v1 conf changes whose bytes decode: `isConfChangeEncoding`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Perennial.Spec.time.Ticker__Stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-! ## The boot configuration -/

section pure
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **The raft configuration and the peers a new cluster's node boots with** (pure; 2026-11-05,
the `newRaftNode` review's M: until then the same conjuncts spelled out in
`bootstrappedRaft.newRaftNode.spec`'s, `NodeStartSpec`'s and `bootOk`'s `Hraft`): the wrapper's
logger `b.lg` non-nil (`newRaftNode`'s), `NewRawNode`'s premises on `b.config` (`StartNode.spec`'s,
with (raft-entsize [r3f]) its `MaxSizePerMsg ≤ 2 ^ 20` at a bounded cluster;
its storage the `MemoryStorage` `b.storage`; `CheckQuorum` and `PreVote` either way since
2026-10-17), and the peers `pv` non-empty (`len(b.peers) != 0`: `StartNode`'s branch) with their
ids `ps`. What each user needs beyond it (the heartbeat, the peers' distinctness, the cluster's
voters, ...) it states beside it. -/
structure rnStartCfg (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (pv : List Peer)
    (ps : List w64) : Prop where
  lg : bv.lg' ≠ null
  valid : ConfigValid cv
  logger : cv.Logger' = interface.ok lok
  storage : cv.Storage' = memStorIface bv.storage'
  inflight : sint.Z cv.MaxInflightMsgs' < 2 ^ 62
  noForwarding : cv.DisableProposalForwarding' = false
  readOnly : cv.ReadOnlyOption' = W64 0
  ccValidation : cv.DisableConfChangeValidation' = false
  sizes : cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0
  /-- (raft-entsize [r3f], the user's decision 2026-11-09) a message's entries are cut at
  `MaxSizePerMsg ≤ 2 ^ 20` (`StartNode.spec`'s premise at a bounded cluster, the size law's):
  etcd's raft configuration sets `MaxSizePerMsg: maxSizePerMsg` (`server/etcdserver/raft.go:38`,
  `maxSizePerMsg = 1 * 1024 * 1024`) in `raftConfig`, which both `bootstrappedRaft` constructions
  call (`server/etcdserver/bootstrap.go:564-575`), at the pinned etcd (`a4d2bb1720`); checked by
  `examples/entsize` (`TestMaxSizePerMsg`, run from `etc/gates.sh`). -/
  maxMsg : uint.Z cv.MaxSizePerMsg' ≤ 2 ^ 20
  noAsync : cv.AsyncStorageWrites' = false
  applied : cv.Applied' = W64 0
  peers : ps = pv.map Peer.ID'
  peersNe : ps ≠ []

/-- (restart S3 item 5, Q35 (a), 2026-11-11) **The raft configuration a restarted node boots with**
(pure): `rnStartCfg`'s conjuncts on the logger and `b.config` (`RestartNode.spec`'s `NewRawNode`
premises, `Applied` zero: `raftConfig` leaves it unset, `bootstrap.go:580-592` at the pin
`a4d2bb172`), and no peers (`len(b.peers) == 0`: `RestartNode`'s branch, `bootstrap.go:596`;
`bootstrapRaftFromWAL` sets none, `:570-578`). -/
structure rnRestartCfg (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (pv : List Peer) :
    Prop where
  lg : bv.lg' ≠ null
  valid : ConfigValid cv
  logger : cv.Logger' = interface.ok lok
  storage : cv.Storage' = memStorIface bv.storage'
  inflight : sint.Z cv.MaxInflightMsgs' < 2 ^ 62
  noForwarding : cv.DisableProposalForwarding' = false
  readOnly : cv.ReadOnlyOption' = W64 0
  ccValidation : cv.DisableConfChangeValidation' = false
  sizes : cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0
  maxMsg : uint.Z cv.MaxSizePerMsg' ≤ 2 ^ 20
  noAsync : cv.AsyncStorageWrites' = false
  applied : cv.Applied' = W64 0
  peersNil : pv = []

/-- (restart S3 item 5, Q35 (a), r2db §4.3, 2026-11-11) **How the raft node boots** (the boot sum):
a new cluster's node (`fresh`, `StartNode`), or a restart (`restart`, `RestartNode`) from the storage
contents `σ` with the conf state `cs` (the backend's), the client's durable state `S`, the
configuration `m` after the first `a` committed entries, and the restart point's backend log `A₀`
(the wrapper's labels). -/
inductive RNBoot where
  | fresh
  | restart (σ : StorContents) (cs : ConfStateM) (S : RaftState) (a : Nat) (m : Membership)
      (A₀ : List EntryModel)

/-- The wrapper's restart point's backend log (`RNNames.a0`): `[]` fresh, `A₀` at a restart. -/
def RNBoot.a0 : RNBoot → List EntryModel
  | .fresh => []
  | .restart _ _ _ _ _ A₀ => A₀

/-- The restart point's start term (`RNNames.t0`): `0` fresh, the restored hard state's term. -/
def RNBoot.t0 : RNBoot → w64
  | .fresh => W64 0
  | .restart σ _ _ _ _ _ => σ.hs.Term'

/-- The restart point's WAL commit (`RNNames.commit0`): `0` fresh, the restored commit. -/
def RNBoot.commit0 : RNBoot → Nat
  | .fresh => 0
  | .restart σ _ _ _ _ _ => σ.commit

/-- The restart point's snapshot index (`RNNames.snap0`): `0` fresh, the restored base. -/
def RNBoot.snap0 : RNBoot → Nat
  | .fresh => 0
  | .restart σ _ _ _ _ _ => σ.b

/-- The log the wrapper's tokens start at (`newRaftNode`'s `L₀`; Q34 (a), `P`): `[]` fresh, the
backend log up to the restored base at a restart (`A₀.take σ.b`). -/
def RNBoot.P : RNBoot → List EntryModel
  | .fresh => []
  | .restart σ _ _ _ _ A₀ => A₀.take σ.b

theorem RNBoot.P_prefix (bt : RNBoot) : bt.P <+: bt.a0 := by
  cases bt with
  | fresh => exact List.prefix_refl _
  | restart σ _ _ _ _ A₀ => exact List.take_prefix _ _

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## The contracts (see the file header) -/

/-- **`NewRaftLoggerZap(lg)`** (names-only): some logger interface value, for a non-nil zap
logger. -/
def rnLoggerZapOk : IProp GF :=
  iprop(□ ∀ lg : Loc, {{ ⌜lg ≠ null⌝ }} (App (Val (@! NewRaftLoggerZap)) (Val #lg))
    {{ (l : GoInterface), RET #l; True }})

instance rnLoggerZapOk_persistent : Persistent (rnLoggerZapOk (GF := GF)) := by
  unfold rnLoggerZapOk; infer_instance

/-- **`contention.NewTimeoutDetector(d)`** (names-only): a detector meeting `isRNTimeoutDetector`. -/
def rnTimeoutDetectorOk : IProp GF :=
  iprop(□ ∀ d : time.Duration, {{ True }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.contention.NewTimeoutDetector)) (Val #d))
    {{ (td : Loc), RET #td; isRNTimeoutDetector td }})

instance rnTimeoutDetectorOk_persistent : Persistent (rnTimeoutDetectorOk (GF := GF)) := by
  unfold rnTimeoutDetectorOk; infer_instance

/-- **A ticker of `time.NewTicker` is the wrapper's ticker** (2026-11-03; until then `rnTickerOk`,
a contract `newRaftNode`'s spec took, and from the final whole-`bootOk` review's S2 to here a theorem
of this repository's `time` axioms, `rnTickerOk_of_time`): Perennial's `isTicker`'s channel bag is
`isRNTicker`'s (ticks carrying nothing; until 2026-11-05, the user's S1, at `E.T = True`, a
premise), and its `Stop` returns. Over `Stop`'s spec as a hypothesis (a callee spec:
`newRaftNode`'s proof takes it). -/
theorem isRNTicker_of_time (wpS : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (tk ch : Loc) (γ : ChanNames) :
    time.isTicker (GF := GF) tk ch γ ⊢ isRNTicker tk := by
  iintro #Ht
  ihave #Ht' := Ht
  iunfold time.isTicker at Ht'
  icases Ht' with ⟨#HC, #HI, #HR, #Hbag⟩
  iunfold isRNTicker
  iexists ch
  isplitr
  · iexact HC
  isplitr
  · iright; iexists γ; iexact Hbag
  iintro !> %Ψ !> - HΨ
  wp_apply wpS tk
  · iexists ch, γ; iexact Ht
  iapply HΨ
  ipureintro; trivial

/-- **The package globals `raftStatus` and `raftStatusMu`** (`raft.go`): the mutex owns the
function value (`raftStatus` is read by the `expvar` closure registered at init, under the
mutex; `bootstrappedRaft.newRaftNode` writes it once, under the mutex). -/
def rnRaftStatusOk : IProp GF :=
  sync.isMutex (globalAddr raftStatusMu) iprop(∃ f : GoFunc, globalAddr raftStatus ↦ f)

instance rnRaftStatusOk_persistent : Persistent (rnRaftStatusOk (GF := GF)) := by
  unfold rnRaftStatusOk; infer_instance

/-- (D22 J1a, 2026-10-26) **The storage `st` is a `*storage` made over the snapshotter `ss`**
(`storage.storageSnap`): what `storage.Release`'s axiom names the snapshot directory by. -/
def rnStorageOf (st : GoInterface) (ss : Loc) : Prop :=
  ∃ p : Loc, st = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p ∧
    storage.storageSnap p ss

/-- **`serverstorage.NewStorage(lg, w, ss)`** (names-only): the WAL as the raft loop uses it
(`isRNWal`); (D22 J1a, 2026-10-26) a `*storage` over the snapshotter `ss` (`NewStorage` returns
`&storage{lg: lg, w: w, s: s}`, `storage.go`). (2026-10-31, `notes/axiom-review/savesnap.md`) Over a WAL ready to write
(`storage.walReady`): until then over any `w`, false for a nil one (`isRNWal`'s `Close` panics on
it). The storage is over `w`'s open token (`storage.walOpen w`, shared by every storage over `w`;
2026-10-31, the user's decision), which `bootstrap`'s contract gives. -/
def rnNewStorageOk : IProp GF :=
  iprop(□ ∀ (lg w ss : Loc), {{ ⌜storage.walReady w⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewStorage)) (Val #lg)) (Val #w))
      (Val #ss))
    {{ (st : GoInterface), RET #st; isWalStorage st ∗ ⌜rnStorageOf st ss ∧ storage.walOf st = w⌝ }})

instance rnNewStorageOk_persistent : Persistent (rnNewStorageOk (GF := GF)) := by
  unfold rnNewStorageOk; infer_instance

/-- **`cl.IsIDRemoved(id)`** of the cluster `cl` (`membership.RaftCluster`): some boolean.
(premise-fixes-4: until then this said names-only; `IsIDRemoved` is translated and proved, and this
triple follows from its spec, `membership.RaftCluster.IsIDRemoved.spec_static`, under the cluster's
`isRaftCluster`.) -/
def rnClusterOk (cl : Loc) : IProp GF :=
  iprop(□ ∀ id : w64, {{ True }}
    (App (Val (cl @!! go.GoType.PointerType api.membership.RaftCluster.ty @!! go!"IsIDRemoved"))
      (Val #id))
    {{ (b : Bool), RET #b; True }})

instance rnClusterOk_persistent (cl : Loc) : Persistent (rnClusterOk (GF := GF) cl) := by
  unfold rnClusterOk; infer_instance

/-- `tickMu`'s resource is fractional (for `sync.init_RWMutex`). -/
instance rnTickInv_fractional (r : Loc) : Fractional (rnTickInv (GF := GF) r) := by
  unfold rnTickInv
  exact fractional_exists_agree (fun (t : time.Time) q => iprop(rnLatestTickTsAddr r ↦{DFrac.own q} t))
    (fun t => fractional_of_dfractional (fun dq => typedPointsto (rnLatestTickTsAddr r) t dq))
    (fun x y q1 q2 => by
      iintro ⟨H1, H2⟩
      icombine H1 H2 gives %H
      ipureintro; exact H)

/-! ## The wrapper as built -/

/-- **The wrapper's components** (persistent): the predicates on the struct *value* `rv`'s
components, independent of where the struct lives (`NewServer` copies `*newRaftNode(...)` into
`EtcdServer.r` by value): the logger a zap logger (premise-fixes-6: until then non-nil), `msgSnapC`'s bag, `applyc`'s SPSC channel,
`readStateC`'s bag of answered read states, the ticker, the detector, `stopped`'s bag and `done`'s
broadcast channel (its `Unknown` view). -/
def rnParts (E : RNEnv GF) (γ : RNNames) (rv : raftNode) : IProp GF :=
  iprop("#Hlgnn" ∷ zapLoggerOk rv.lg' ∗
    "#Hmsci" ∷ isRNMsgSnapC γ rv.msgSnapC' ∗
    "#Hapci" ∷ isRNApplyc E γ rv.applyc' ∗
    "#Hrsci" ∷ isRNReadStateC E rv.readStateC' ∗
    "#Htki" ∷ isRNTicker rv.ticker' ∗
    "#Htdi" ∷ isRNTimeoutDetector rv.td' ∗
    "#Hstci" ∷ rnStopBag E γ (storage.walOf rv.raftNodeConfig'.storage') rv.stopped' ∗
    "#Hdnci" ∷ ownBroadcastChan rv.done' γ.done
      (rnDoneEsc γ (storage.walOf rv.raftNodeConfig'.storage')) .Unknown)

instance rnParts_persistent (E : RNEnv GF) (γ : RNNames) (rv : raftNode) :
    Persistent (rnParts E γ rv) := by
  unfold rnParts; infer_instance

/-- **The raft wrapper `r` as `newRaftNode(cv)` leaves it** (see the file header): the struct
value `rv`, owned whole at `r` (to be copied), with `cfg`'s fields as the caller gave them
(`raftNodeConfig' = cv`, so `transport` is `cv`'s, nil), its `tickMu` a fresh `RWMutex` (the
guard over `latestTickTs` is made where the struct finally lives, `isRaftNode_of_rnParts`), the
components' predicates (`rnParts`), `applyc`'s two halves with `cum` at `[L₀]` (restart S3 item 6:
the start log `L₀`, `[]` at a first start; until then `[[]]`) (the loop's and
the apply side's ghost state, `rnLoopTok`/`rnApplyTok`), the right to close `done`, and the
claim on the stop's escrow (`rnStopClaim`). -/
def rnBuilt (E : RNEnv GF) (γ : RNNames) (r : Loc) (cv : raftNodeConfig) (L₀ : List EntryModel) :
    IProp GF :=
  iprop(∃ rv : raftNode,
    "Hr" ∷ r ↦ rv ∗
    "%Hrv" ∷ ⌜rv.lg' = cv.lg' ∧ rv.raftNodeConfig' = cv⌝ ∗
    "Hmu" ∷ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
    "#Hparts" ∷ rnParts E γ rv ∗
    "Hprod" ∷ sspscProducer γ.ap ([] : List toApply) ∗
    "Hcons" ∷ sspscConsumer γ.ap ([] : List toApply) ∗
    "Hcum" ∷ monoListAuthOwn γ.cum 1 [L₀] ∗
    "Hcum0" ∷ monoListIdxOwn γ.cum 0 L₀ ∗
    "Hdtok" ∷ ownBroadcastChan rv.done' γ.done
      (rnDoneEsc γ (storage.walOf rv.raftNodeConfig'.storage')) .Pending ∗
    -- (2026-11-03, R2b-3b) the claim on the stop's escrow
    "Hsc" ∷ rnStopClaim γ)

/-- (restart S3 item 5, Q35 (a), r2db §4.3, 2026-11-11) **What `bootstrappedRaft.newRaftNode` needs of
the boot `bt`**, for the server's raft names `γr`, the receiver's value `bv`, the config `cv` and the
peers: at `fresh`, `StartNode`'s (the configuration and the peers, `rnStartCfg`; the storage as
`StartNode` boots it, `restartStorage` at the empty contents with the frame `Q`; this node's boot
token, its id vacant, its durable state at `RaftState.init`: until then the spec's own conjuncts);
at `restart σ cs S a m A₀`, `RestartNode`'s (the configuration, `rnRestartCfg`, no peers; the
configuration point `a` between the restored base and commit, the bootstrap log within the commit,
`cs` reporting `m`, the storage holding `S`; the storage as `RestartNode` reads it, `restartStorage`
at `σ`, `cs` and `Applied = 0`, with the frame `Q`; the cluster, its receipts' bound, the id vacant,
the durable state `S`, the configuration `m` at `a`). -/
def rnBootPre (γr : SrvRaft) (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk)
    (pv : List Peer) (ps : List w64) (ctxs : List (List w8)) (Q : GName → IProp GF) :
    RNBoot → IProp GF
  | .fresh =>
    letI := srvStor (GF := GF) γr
    iprop(⌜rnStartCfg bv cv lok pv ps⌝ ∗
      restartStorage γr.cl (memStorIface bv.storage')
        ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩
        memSnapEmpty.Metadata'.ConfState' 0 Q ∗
      nodeBoot γr.cl srvClusterN ps ctxs cv.ID' ∗ nodeVacant γr.cl cv.ID' ∗
      raftState γr.cl cv.ID' RaftState.init)
  | .restart σ cs S a m _ =>
    letI := srvStor (GF := GF) γr
    iprop(⌜rnRestartCfg bv cv lok pv ∧ σ.b ≤ a ∧ a ≤ σ.commit ∧ γr.cl.bootLen ≤ σ.commit ∧
        confStateIs cs m ∧ StorageHolds S σ⌝ ∗
      restartStorage γr.cl (memStorIface bv.storage') σ cs 0 Q ∗
      isCluster γr.cl srvClusterN ∗ readyFits γr.cl srvClusterN ∗ nodeVacant γr.cl cv.ID' ∗
      raftState γr.cl cv.ID' S ∗ confAt γr.cl a m)

/-- (restart S3 item 5, Q35 (a), r2db §4.3, 2026-11-11) **What the node's start gives of the boot
`bt`**, for the node `n` and the storage's key `K`: at `fresh`, `StartNode`'s (made by `StartNode`,
`nodeStartedFresh`; the driver at its start; the durable state at `RaftState.init`; the view at the
peers' membership: until then the spec's own conjuncts); at `restart σ cs S a m A₀`, `RestartNode`'s
(the committed log `l` of the restored base, the driver at it with the restored hard state, the
durable state `S` and the follower's role; the view at `(a, m)`). -/
def rnBootPost (γr : SrvRaft) (n : Loc) (K : GName) (bv : bootstrappedRaft) (cv : Config)
    (ps : List w64) (ctxs : List (List w8)) : RNBoot → IProp GF
  | .fresh =>
    letI := srvStor (GF := GF) γr
    iprop(nodeStartedFresh n γr.cl srvClusterN ps ctxs cv.ID' ∗
      nodeDriver n γr.cl srvClusterN (NodeDriverState.init (memStorIface bv.storage') K) ∗
      raftState γr.cl cv.ID' RaftState.init ∗
      nodeConfig n γr.cl srvClusterN ⟨0, Membership.simple (GMap.listToSet ps)⟩)
  | .restart σ _ S a m _ =>
    letI := srvStor (GF := GF) γr
    iprop(∃ l : List LogEntry, isCommittedLogLb γr.cl l ∗ ⌜l.length = σ.b⌝ ∗
      nodeDriver n γr.cl srvClusterN ⟨memStorIface bv.storage', l, σ.hs, none, K, S, StateFollower⟩ ∗
      raftState γr.cl cv.ID' S ∗
      nodeConfig n γr.cl srvClusterN ⟨a, m⟩)

end defs

end EtcdGrove
end Perennial
