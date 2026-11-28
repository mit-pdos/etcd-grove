/-
The server's raft wrapper (`server/v3/etcdserver/raft.go`): the shared vocabulary of
`Spec/raftNode__*.lean`. Lean-first (no Rocq counterpart); the plan is `decisions.md`, "The
server's raft wrapper"; since 2026-10-16 (stage R7b of the raft v3.7 retarget, D10) the node's
predicates are definitions over raft's own (`Proof/go_etcd_io/raft/v3/InvNode.lean`), and the
node contract is to be discharged from raft's specs.

- **The environment** `E : RNEnv` is what the node contract is stated over: `C L`, "`L` is a
  prefix of the cluster's committed log"; `M m`, "raft may send the message `m`"; `T`, once a
  tick's resource (node.go's term-budget credit), now unused and pinned to `True`; and (2026-10-13, the request path's unit 4b) the read
  names `γr` and the read-index registrations `RQ id n` (`ReadIndex` registered the request id
  `id` at a lower bound `n` of the committed index), which the read states a `Ready` carries
  answer (`srvReadStateOk`, `read/Inv.lean`). What the discharge needs of `E` is `rnEnvOk E γ`
  (persistent, in `isRaftNode`): `E.T` is `True` (raft's tick credit until D19b; since then
  nothing reads it: `raftNode.tick` takes its credit from a Go step of its own, and since 2026-11-05
  the ticker's bag carries `True` itself, `isRNTicker`), `E.M` of a message raft handed out
  (with its read credit, D21 stage M1),
  `E.C` from the committed log (and back: the log prefix and the indices), `E.RQ` raft's read
  registration (`srvRQ`), and the names tied (`E.γr.raft.raft = γ.node`, ...).
- **The node** (`isRaftNodeIfc E γ n`, the `raft.Node` interface, shaped like node.go's verified
  specs): `Ready()` is a handshake channel whose payload is raft's `readyP γ.node` (`rnReadyP`);
  the driver (`rnDrv γ L`, raft's `nodeDriver` at `pre ++ L`) learns the payload's log is `L`
  and is busy (`rnBusy`, raft's `nodeDriverBusy`) until `Advance()`, which takes the append
  receipt of the `Ready`'s entries (the `MemoryStorage`'s, `rnAppendReceipt`). Receiving a
  `Ready` (`rn_ready_recv`) derives the server's view of its data (`rnReadyData`: the messages
  persisted, `E.C` from the committed log) under the run's premises `rnLogFits` (pure since
  2026-10-18, D19b stage 5: the receipt bound past the bootstrap log, from which every `Ready`'s
  entries fit `Append`'s index bound and the committed index fits) and the read states' bridge
  (`rnReadStateBridge`, `srvReadStateOk_of_raft`).
- **`applyc`** is an SPSC channel (`isSspsc`) of `toApply`s; the `k`th payload carries the
  mono-list `cum`'s elements `k` and `k + 1` (the log forwarded before and after it), so the
  consumer, at `cum[|received|] = A` (`rnApplyTok γ A`), learns that the batch extends `A`. The
  loop (`rnLoopTok γ L`) owns the producer half and `cum`'s authority, whose last element is
  the node's delivered log `L`.
- **The other components** are persistent predicates of triples (the WAL, the
  `MemoryStorage`, the transport, the timeout detector, the ready handler's closures, the
  ticker, whose ticks carry nothing, `True`: until 2026-11-05 its bag was `E.T`), and the wrapper's fields are read-only after `start` but
  `latestTickTs`, under `tickMu` (`rnTickInv`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Proof.go_etcd_io.raft.v3.NodeInstalls
public import Perennial.Golang.Theory.Chan.Idioms.Idioms
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopChan
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayModel
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.replayTerms__termAt
public import Perennial.Ghost.MonoList
public import Perennial.Proof.ThreadPool
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NotifyC2
public import Proof.go_etcd_io.raft.v3.MemstorageApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

-- `EntryModel`'s countable instance: `InvRaftpb.lean` (2026-10-14, unit T1).

section countable
variable [GooseExts]

-- `Ready`'s countable instance: raft's (`InvNode.ready_countable`; the server's own went with
-- stage R7b, the file importing raft's node layer).

instance toApply_countable : Pos.Countable toApply :=
  countableOfLeftInverse (fun a : toApply => (a.entries', a.snapshot', a.notifyc', a.raftAdvancedC', a.raftTerm', a.replayTerms'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩) (fun _ => rfl)

-- `ReadState`'s instance (`readState_countable`): `InvRequest.lean` (2026-10-13, the read loop).

end countable

/-- The ghost names of a raft wrapper (2026-10-16, stage R7b; 2026-10-27, branch `server-port`:
over raft's node API): the cluster as the server sees it (`node : SrvRaft`), the node's id and the
`*raft.node` behind the interface (`nl`, the node API's node), the committed log before the
server's start index (`ServerRaftNames.pre`, the same list), the `*MemoryStorage`, its names and
the registry's ghost name (`memStorReg`, raft's storage API: the registry is a class there, so
that `memStorageModel` is an instance; here its name is a field, and each predicate over the
storage builds the instance from it, `letI : MemStorReg GF := ⟨γ.reg⟩`); `applyc`'s SPSC names and
the mono-list `cum` of the log forwarded after each payload; the broadcast channel `done`;
(2026-11-01, durability layer 4) the key raft named the storage by at the attach (`StartNode`'s
post, `restartStorage`'s continuation), which the node's storage bounds (`nodeAppliedLb`,
`nodeCommitLb`) and the storage's invariant (`memStorInv`) are keyed by. -/
structure RNNames [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] (GF : BundledGFunctors) where
  node : SrvRaft
  id : w64
  nl : NodeH
  pre : List EntryModel
  ms : Loc
  γs : MemStorNames
  ap : SpscNames
  cum : GName
  done : ChanNames
  key : GName
  -- (2026-11-03, R2b-1 stage 3c) the WAL's durability (the slot convention's field group); (P5,
  -- 2026-11-25) the crash-aware one's (`WalNamesK`: `rnDurInvK`'s names, `wal` its `ν`)
  walK : WalNamesK GF
  -- (wal-link L3, 2026-11-19) the snapshotter the storage was made over (`NewStorage`'s, `isWalStorage`'s
  -- `ss`: what `Release` names the snapshot directory by)
  ss : Loc
  -- (2026-11-03, R2b-3b) the claim on the loop's stop escrow (`rnStopClaim`, `rnDoneEsc`)
  sc : GName
  -- (R2d'a A6, 2026-11-06; DRAFT) the restart point's backend log `A₀` (the backend's ghost applied
  -- log through its consistent index, `bootstrap.go:255-273` at the etcd pin `673da07c8`), over
  -- which the driver's view is stated (`rnCfgAt`); `[]` at a first start (`newRaftNode`'s)
  a0 : List EntryModel
  -- (R2d'a A10 item 5, 2026-11-06) the restart point's restored `HardState` term `T₀`
  -- (`RestartNode`'s); `W64 0` at a first start (`newRaftNode`'s). (restart3 A1, 2026-11-15) Read by
  -- nothing since `rnSnapMsg`'s bound and the window row went; kept for the restart data's first
  -- disjunct
  t0 : w64
  -- (R2d'b F1 / S1, Q40, 2026-11-11) the restart point's WAL commit `σ.commit` (raft's restored
  -- commit, from which the loop's commit never drops: `rnLoopTokP`) and snapshot index `σ.b`; `0`
  -- at a first start (`newRaftNode`'s)
  commit0 : Nat
  snap0 : Nat

/-- (P5) The WAL durability's names (`rnDurInv`'s, now inside the crash-aware `walK`). -/
abbrev RNNames.wal [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors} (γ : RNNames GF) : WalNames GF := γ.walK.ν

/-- The `MemoryStorage` registry's name: the cluster's (2026-10-27; until then a field). -/
abbrev RNNames.reg [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors} (γ : RNNames GF) : GName := γ.node.reg

/-- The cluster's names at the wrapper's start log (for `srvLE`/`srvCfgView`, which read only the
cluster and the start log). -/
abbrev RNNames.srv [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors} (γ : RNNames GF) : ServerRaftNames := ⟨γ.node, γ.pre, W64 0⟩

/-- Raft's full committed log holding the server's `L` after its start (`srvLogOf`, by the
wrapper's names). -/
def rnLogOf [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors} (γ : RNNames GF) (L : List EntryModel) : List EntryM :=
  (γ.pre ++ L).map EntryModel.toM

theorem rnLogOf_append [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors} (γ : RNNames GF) (A B : List EntryModel) :
    rnLogOf γ (A ++ B) = rnLogOf γ A ++ B.map EntryModel.toM := by
  simp [rnLogOf]

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

abbrev rnLgAddr (r : Loc) : Loc := structFieldRef raftNode go!"lg" r
abbrev rnTickMuAddr (r : Loc) : Loc := structFieldRef raftNode go!"tickMu" r
abbrev rnLatestTickTsAddr (r : Loc) : Loc := structFieldRef raftNode go!"latestTickTs" r
abbrev rnCfgAddr (r : Loc) : Loc := structFieldRef raftNode go!"raftNodeConfig" r
abbrev rnNodeAddr (r : Loc) : Loc := structFieldRef raftNodeConfig go!"Node" (rnCfgAddr r)
abbrev rnIsIDRemovedAddr (r : Loc) : Loc :=
  structFieldRef raftNodeConfig go!"isIDRemoved" (rnCfgAddr r)
abbrev rnRaftStorageAddr (r : Loc) : Loc :=
  structFieldRef raftNodeConfig go!"raftStorage" (rnCfgAddr r)
abbrev rnReplayTermsAddr (r : Loc) : Loc :=
  structFieldRef raftNodeConfig go!"initialReplayTerms" (rnCfgAddr r)
abbrev rnStorageAddr (r : Loc) : Loc := structFieldRef raftNodeConfig go!"storage" (rnCfgAddr r)
abbrev rnHeartbeatAddr (r : Loc) : Loc :=
  structFieldRef raftNodeConfig go!"heartbeat" (rnCfgAddr r)
abbrev rnTransportAddr (r : Loc) : Loc :=
  structFieldRef raftNodeConfig go!"transport" (rnCfgAddr r)
abbrev rnMsgSnapCAddr (r : Loc) : Loc := structFieldRef raftNode go!"msgSnapC" r
abbrev rnApplycAddr (r : Loc) : Loc := structFieldRef raftNode go!"applyc" r
abbrev rnReadStateCAddr (r : Loc) : Loc := structFieldRef raftNode go!"readStateC" r
abbrev rnTickerAddr (r : Loc) : Loc := structFieldRef raftNode go!"ticker" r
abbrev rnTdAddr (r : Loc) : Loc := structFieldRef raftNode go!"td" r
abbrev rnStoppedAddr (r : Loc) : Loc := structFieldRef raftNode go!"stopped" r
abbrev rnDoneAddr (r : Loc) : Loc := structFieldRef raftNode go!"done" r

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- What the node contract is stated over (see the file header). -/
structure RNEnv (GF : BundledGFunctors) where
  C : List EntryModel → IProp GF
  M : Loc → IProp GF
  T : IProp GF
  γr : ReadNames
  RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF
  /-- (2026-10-24, rafthttp stage 6d) what the transport's `Send` borrows, which the loop holds
  (for the server, a reader's token of the transport's lock). -/
  S : IProp GF
  /-- (2026-10-26, D43 M5c) what the transport's `Stop` takes: the right to stop it, which
  `stopped` carries to the loop (for the static server `True`, its transport frozen; in the
  dynamic mode the transport's live right, which the apply thread hands over, M6). -/
  ST : IProp GF

/-- A message the node handed out, as the wrapper reads and forwards it: its destination and
type read-only, and `E.M m`. (2026-10-19, D21 stage M1: owned, no longer persistent, so that
`E.M` can carry a message's one-shot read credit to the transport; until then `□ E.M m`.) -/
def rnMsgOk (E : RNEnv GF) (m : Loc) : IProp GF :=
  iprop(∃ (to : w64) (ty : w32), msgAt m to ty ∗ E.M m)

/-- Evidence stored with each server snapshot. The initial image is bounded
by the boot index. The other writers are the apply thread and the Raft driver. -/
def srvStoredOrigin (cl : Cluster) (applied pin : GName) (boot : Nat) (sv : SnapshotM) : IProp GF :=
  iprop(⌜uint.nat sv.Metadata'.Index' ≤ boot⌝ ∨ monoNatLbOwn applied (uint.nat sv.Metadata'.Index') ∨
    ∃ n : NodeH, dghostVar pin DFrac.discard n.installs ∗ nodeInstalledIndex cl n sv.Metadata'.Index')

instance (cl : Cluster) (applied pin : GName) (boot : Nat) (sv : SnapshotM) :
    Persistent (srvStoredOrigin (GF := GF) cl applied pin boot sv) := by
  unfold srvStoredOrigin; infer_instance

instance [MemStorReg GF] (ms : Loc) (gs : MemStorNames) (cl : Cluster) (key applied pin : GName)
    (boot : Nat) : Persistent (memStorInvT (GF := GF) ms gs cl key (srvStoredOrigin cl applied pin boot)) := by
  unfold memStorInvT; infer_instance

/-- The server retains the storage invariant and identifies the actual node
that attached it. The name `pin` is allocated before calling StartNode. -/
def srvAttachedMem [MemStorReg GF] (ms : Loc) (gs : MemStorNames) (cl : Cluster) (key applied : GName)
    (n : NodeH) (boot : Nat) : IProp GF :=
  iprop(∃ pin : GName, dghostVar pin DFrac.discard n.installs ∗
    nodeTagPin cl n (fun sv => iprop(snapshotValid cl sv ∗ srvStoredOrigin cl applied pin boot sv)) ∗
    memStorInvT ms gs cl key (srvStoredOrigin cl applied pin boot))

instance [MemStorReg GF] (ms : Loc) (gs : MemStorNames) (cl : Cluster) (key applied : GName)
    (n : NodeH) (boot : Nat) : Persistent (srvAttachedMem (GF := GF) ms gs cl key applied n boot) := by
  unfold srvAttachedMem memStorInvT; infer_instance

/-- Creating a snapshot requires the applied-index name of the writer. -/
def srvCreateMem [MemStorReg GF] (ms : Loc) (gs : MemStorNames) (cl : Cluster) (key applied : GName) :
    IProp GF :=
  iprop(∃ pin boot, memStorInvT ms gs cl key (srvStoredOrigin cl applied pin boot))

instance [MemStorReg GF] (ms : Loc) (gs : MemStorNames) (cl : Cluster) (key applied : GName) :
    Persistent (srvCreateMem (GF := GF) ms gs cl key applied) := by
  unfold srvCreateMem; infer_instance

/-- Compaction uses the storage bounds at its key and preserves the stored snapshot. -/
def srvCompactMem [MemStorReg GF] (ms : Loc) (gs : MemStorNames) (cl : Cluster) (key : GName) : IProp GF :=
  iprop(∃ applied, srvCreateMem ms gs cl key applied)

instance [MemStorReg GF] (ms : Loc) (gs : MemStorNames) (cl : Cluster) (key : GName) :
    Persistent (srvCompactMem (GF := GF) ms gs cl key) := by
  unfold srvCompactMem; infer_instance

/-- The Ready batch from which the server received this outgoing message. -/
def rnMessageSource (γ : RNNames GF) (q : QMsg) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ term ms bound installed, ⌜q ∈ ms⌝ ∗
    readySnapSources γ.node.cl γ.nl γ.id term ms bound installed)

instance (γ : RNNames GF) (q : QMsg) : Persistent (rnMessageSource (GF := GF) γ q) := by
  unfold rnMessageSource; infer_instance

/-- (D22 S-l sender, 2026-10-22; 2026-10-30, the repair: snapshots allowed, until then `False`)
**A `MsgSnap` raft handed out, owned**: the message, whole (a `Ready`'s: `readyDq`, a
`MsgSnap` being no response; 2026-10-31, S1: until then at some fraction, which
`createMergedSnapshotMessage`'s write of `m.Snapshot` cannot take), of type `MsgSnap`, sent by the
node, with its credits (`sentMsg_snapshot` gives its snapshot's certificate): what
`processMessages` hands to `msgSnapC` and `applyAll`'s merge rewrites. (restart3 A1, 2026-11-15; from
R2d'a A10 item 5 until then: its term above this incarnation's start term `γ.t0`, which only the
deleted window row `winNoMergedSendR` read; the fork's window guard replaces it.)
(raft-entsize [r3c], 2026-11-10) Without top-level unknown fields (`pbMsg … []`, raft's literal:
`msgOut_snapUf`), for the merged message's content (`createMergedSnapshotMessage`). -/
def rnSnapMsg (γ : RNNames GF) (m : Loc) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ st : MsgSt, msgOwn m (DFrac.own 1) st ∗
    ⌜st.msg.Type' = MsgSnap⌝ ∗
    sentMsg γ.node.cl srvClusterN γ.id st ∗ msgCredits γ.node.cl srvClusterN st ∗
    pbMsg raftpb.Message m [] ∗ rnMessageSource γ ⟨m, st⟩)

/-- (D22 S-l sender) **A message of a `Ready`, as the server receives it**: any but a `MsgSnap`
read-only with `E.M` (`rnMsgOk`'s, with its type not `MsgSnap`), a `MsgSnap` owned
(`rnSnapMsg`). `processMessages` turns the first into `rnMsgOk` for the transport and hands the
second to `msgSnapC`. (raft-entsize §2, 2026-11-09: the first read-only at the content raft handed
it out with, `msgOut`; until then `msgAt`, today's form of it.) -/
def rnMsgR (E : RNEnv GF) (γ : RNNames GF) (m : Loc) : IProp GF :=
  iprop((∃ st : MsgSt, msgOut γ.node.cl m DFrac.discard st ∗ ⌜st.msg.Type' ≠ MsgSnap⌝ ∗ E.M m) ∨
    rnSnapMsg γ m)

/-- (raft-entsize [r3c]) **A handed-out `MsgSnap` has no top-level unknown fields** (raft's
`msgOut_snap`), as its object's `pbMsg … []`. -/
theorem msgOut_snapUf [StorageModel GF] (γc : Cluster) (l : Loc) (dq : DFrac) (st : MsgSt)
    (h : st.msg.Type' = MsgSnap) :
    msgOut (GF := GF) γc l dq st ⊢ msgOut γc l dq st ∗ pbMsg raftpb.Message l [] := by
  unfold msgOut
  iintro ⟨%c, Hc, %Hm, #Ho⟩
  obtain ⟨Hmod, Hcs, Hsn⟩ := Hm
  have hu : c.f.uf = [] := Hsn (by rw [← Hmod] at h; exact h)
  unfold msgPtsCC
  icases Hc with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  isplitl
  · iexists c
    isplitl
    · iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
      isplitr
      · ipureintro; exact Hnn
      iframe
      iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcx Hpb
    iframe Ho
    ipureintro; exact ⟨Hmod, Hcs, Hsn⟩
  rw [hu] at *
  iexact Hpb

/-! ## The node's `Ready`/`Advance` exchange -/

/-- `MemoryStorage.Append`'s index bound: the batch's last index at most `2^61` (2026-10-27: the
node API's `readyRest_fits`). -/
def rnFits (es : List EntryModel) : Prop :=
  ∀ e0, es.head? = some e0 → uint.Z e0.index + (es.length : Int) ≤ 2 ^ 61

/-- (2026-10-30, the repair, stage P) The batch's indices consecutive from its first
(`MemoryStorage.Append`'s premise; the node API's `readySnap none` states it). -/
def rnConsec (es : List EntryModel) : Prop :=
  ∀ e0, es.head? = some e0 → ∀ (j : Nat) (e : EntryModel), es[j]? = some e →
    uint.nat e.index = uint.nat e0.index + j

/-- (P5) A fitting consecutive batch's indices are within raft's room (`rnDurK_save.law`'s premise). -/
theorem rnFits_idx {es : List EntryModel} (hf : rnFits es) (hc : rnConsec es) :
    ∀ e ∈ es.map EntryModel.toM, uint.nat e.Index' ≤ 2 ^ 61 - 1 := by
  intro e he
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he'
  have hjl : j < es.length := (List.getElem?_eq_some_iff.1 hj).1
  cases hh : es with
  | nil => rw [hh] at hjl; simp at hjl
  | cons e0 t =>
    have h1 := hf e0 (by rw [hh]; rfl)
    have h2 := hc e0 (by rw [hh]; rfl) j e' hj
    rw [hh] at h1 hjl
    simp only [List.length_cons] at h1 hjl
    simp only [EntryModel.toM]
    have : uint.nat e0.index + (t.length + 1) ≤ 2 ^ 61 := by word
    omega

/-- (P5) A fitting batch `Save` accepts (its indices consecutive, `WalSaveOk`) is within raft's room
(`rnDurK_save.law`'s premise, for the snapshot `Ready`'s batch). -/
theorem walSaveOk_idx {σ : StorContents} {es : List EntryM} (hs : WalSaveOk σ es)
    (hf : ∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ 2 ^ 61) :
    ∀ e ∈ es, uint.nat e.Index' ≤ 2 ^ 61 - 1 := by
  intro e he
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
  have hjl : j < es.length := (List.getElem?_eq_some_iff.1 hj).1
  cases hh : es with
  | nil => rw [hh] at hjl; simp at hjl
  | cons e0 t =>
    rw [hh] at hs hf hj hjl
    have h1 := hf e0 rfl
    have h2 := (hs e0 rfl).2.2 j e hj
    simp only [List.length_cons] at h1 hjl
    have : uint.nat e0.Index' + (t.length + 1) ≤ 2 ^ 61 := by word
    omega

/-- The right to append `es` to the `MemoryStorage` (from a `Ready`): raft's storage API's
`appendRight` at the storage (the range from the batch's first index owned), and the indices'
bound. -/
def rnAppendRight (γ : RNNames GF) (es : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(appendRight (memStorIface γ.ms) (es.map EntryModel.toM) ∗ ⌜rnFits es ∧ rnConsec es⌝)

/-- The receipt of the append of `es` (for `Advance`): raft's storage API's `appendReceipt`, with
nothing frozen (2026-10-30, the repair: `appendReceipt`'s frozen prefix `a` is `[]`, which
`Advance`'s `advReceipt` admits; the server makes no snapshot, D2(i), so needs no frozen entry). -/
def rnAppendReceipt (γ : RNNames GF) (es : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  appendReceipt (memStorIface γ.ms) (es.map EntryModel.toM) []

/-- (2026-10-30, the repair) **The storage's entry at `i` frozen** (persistent; `CreateSnapshot`'s
premise): none at `0`, else read-only for good (the raft loop freezes the committed entries,
`advReceipt`'s prefix, and hands the batch's over with `raftAdvancedC`, `rnFrozenB`). -/
def srvFrozenAt (γs : MemStorNames) (i : Nat) : IProp GF :=
  iprop(⌜i = 0⌝ ∨ ∃ e, memLog γs i DFrac.discard [e])

/-- (2026-10-30, the repair) **The entries `lo .. hi - 1` frozen** (persistent; the raft loop's
hand-over with `raftAdvancedC`). -/
def srvFrozenRange (γs : MemStorNames) (lo hi : Nat) : IProp GF :=
  [∗list] j ∈ List.range' lo (hi - lo), srvFrozenAt γs j

/-- (2026-10-31, the snapshot track: #11's S3) **The entries of `L` frozen from `lo` on, with
their terms** (persistent; the raft loop's hand-over with `raftAdvancedC`, next to
`srvFrozenRange`): the storage's entry at `lo + k` is frozen and has `L[k]`'s term, so a snapshot
`CreateSnapshot` names after it has the applied term (`srvFrozenTerm`); (2026-10-31, #3) or, for
any entry but the last, compacted (a snapshot `Ready`'s `ApplySnapshot` compacts the storage below
the snapshot's index and leaves its dummy entry, frozen with the snapshot's term, the last). -/
def srvFrozenTerms (γs : MemStorNames) (lo : Nat) (L : List EntryModel) : IProp GF :=
  [∗list] k ↦ m ∈ L, iprop((∃ e : EntryM, memLog γs (lo + k) DFrac.discard [e] ∗ ⌜e.Term' = m.term⌝) ∨
    (⌜k + 1 < L.length⌝ ∗ memCompacted γs (lo + k)))

instance srvFrozenTerms_persistent (γs : MemStorNames) (lo : Nat) (L : List EntryModel) :
    Persistent (srvFrozenTerms (GF := GF) γs lo L) := by
  unfold srvFrozenTerms; infer_instance

/-- The frozen terms of a log from those of its two parts. -/
theorem srvFrozenTerms_app (γs : MemStorNames) (lo : Nat) (L1 L2 : List EntryModel) :
    srvFrozenTerms (GF := GF) γs lo L1 ∗ srvFrozenTerms γs (lo + L1.length) L2 ⊢
      srvFrozenTerms γs lo (L1 ++ L2) := by
  unfold srvFrozenTerms
  refine Entails.trans ?_ BigSepL.bigSepL_append.2
  refine sep_mono (BigSepL.bigSepL_mono_of_forall fun {k x} => ?_)
    (BigSepL.bigSepL_mono_of_forall fun {k x} => ?_)
  · iintro (H | ⟨%h, H⟩)
    · ileft; iexact H
    · iright; iframe H; ipureintro; simp only [List.length_append]; omega
  · rw [show lo + L1.length + k = lo + (k + L1.length) by omega]
    iintro (H | ⟨%h, H⟩)
    · ileft; iexact H
    · iright; iframe H; ipureintro; simp only [List.length_append]; omega

/-- (2026-10-30, the repair) **Every entry below `n` frozen or compacted** (persistent;
`Compact`'s premise at any compaction index below the applied index: `ApplySnapshot` compacts
below a snapshot). -/
def srvFrozenBelow (γs : MemStorNames) (n : Nat) : IProp GF :=
  [∗list] j ∈ List.range n, iprop((∃ e, memLog γs j DFrac.discard [e]) ∨ memCompacted γs j)

/-- (2026-10-30, the repair) **`Advance`'s receipt for a batch without a snapshot** after the
committed log `d ++ ce` handed out: raft's `advReceipt` (the append's receipt with a frozen prefix
`a` of the committed entries, which the loop freezes before `Advance`, `appendReceipt`'s). -/
def rnAdvReceipt (γ : RNNames GF) (d ce es : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  advReceipt (memStorIface γ.ms) (srvLE γ.srv (d ++ ce)).length (es.map EntryModel.toM) none

/- (2026-10-30, the repair) **The node's running token** (raft's `nodeRunning`: `node.Stop` takes
all of it; a half refutes the stopped answers of `Advance` and `ApplyConfChange`,
`nodeRunning_stopped`) is split in halves, written out where used: the raft loop's in
`rnLoopTokP` and `Advance`'s clause; the apply side's held by `EtcdServer.run` (its state's
`"Hrunh"`), lent to a batch with a view (`applyAll`/`applyEntries`/`apply`, `dvCCPre`), and given to
the loop with `raftNode.stop` (`rnStopBag`'s payload) once the scheduler is drained: etcd stops
raft after the scheduler. -/

/-- (2026-10-30, the repair, stage P) **A `Ready`'s committed entries `ce` after the log `d`, as the
node API freezes them** (raft's `readySnap none`): the first ones frozen in the storage
(`ceFrozen`), the batch `es` consecutive, the rest of `ce` the batch's first entries. The raft loop
freezes the latter after `Append` (`rn_freeze_receipt`) for `raftAdvancedC`'s frozen range. -/
def rnCeFrozen (γ : RNNames GF) (d ce es : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(ceFrozen (memStorIface γ.ms) (srvLE γ.srv d).length
      (LogEntry.toEntries (ce.map EntryModel.toLE) (srvLE γ.srv d).length)
      (es.map EntryModel.toM) ∗
    ⌜∀ e0, (es.map EntryModel.toM).head? = some e0 →
      (∀ (j : Nat) (e : EntryM), (es.map EntryModel.toM)[j]? = some e →
        uint.nat e.Index' = uint.nat e0.Index' + j) ∧
      ∀ (j : Nat) (e : LogEntry), (ce.map EntryModel.toLE)[j]? = some e →
        uint.nat e0.Index' ≤ (srvLE γ.srv d).length + 1 + j →
        Option.map LogEntry.ofEntryM
          (es.map EntryModel.toM)[(srvLE γ.srv d).length + 1 + j - uint.nat e0.Index']? = some e⌝)

instance rnCeFrozen_persistent (γ : RNNames GF) (d ce es : List EntryModel) :
    Persistent (rnCeFrozen (GF := GF) γ d ce es) := by
  unfold rnCeFrozen; infer_instance

/-- A `Ready`'s `SoftState`: nil, or read-only fields (raft's `softStateRO`). -/
def softStateAt (p : Loc) : IProp GF := softStateRO p

instance softStateAt_persistent (p : Loc) : Persistent (softStateAt (GF := GF) p) := by
  unfold softStateAt; infer_instance

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **A `Ready`'s messages `ms`, not yet sent**: each
owned as the node API hands it out (raft-entsize §2: at the content it pinned, `msgOut`), with its
credits, and at role leader (`r' = StateLeader`, the
role after the `Ready`) their sends (raft's `readyLeaderMsgs`: a leader may send before the batch is
durable). Otherwise *enter* gives the sends (`readyMsgs`), after the WAL `Save`. -/
def rnRawMsgs (γ : RNNames GF) (ms : List QMsg) (r' : StateType) : IProp GF :=
  iprop(([∗list] q ∈ ms, msgOut γ.node.cl q.loc (readyDq q.st) q.st ∗
      msgCredits γ.node.cl srvClusterN q.st) ∗
    (⌜r' = StateLeader⌝ -∗ readyMsgs γ.node.cl srvClusterN γ.id ms) ∗
    □ (∀ q : QMsg, ⌜q ∈ ms⌝ -∗ rnMessageSource γ q))

/-- A `Ready`'s entries in a sized cluster: the slice, the objects at sized contents, and today's
`entRO` list. -/
theorem readyEnts_rn [StorageModel GF] (γc : Cluster) (s : GoSlice) (es : List EntryM) (b : Nat)
    (hmd : γc.maxData = some b) :
    readyEnts (GF := GF) γc s es ⊢
      ∃ esL : List Loc, s ↦*□ esL ∗ rnEntsSized esL (es.map EntryModel.ofM) ∗
        [∗list] l;e ∈ esL;es, entRO l e := by
  iintro #H
  icases readyEnts_sized γc s es b hmd $$ H with ⟨%esL, %cs, #Hs, #Hb, %Hcs⟩
  iexists esL
  iframe Hs
  isplitr
  · unfold rnEntsSized
    iexists cs
    iframe Hb
    ipureintro
    rw [EntryModel.map_toM_ofM]; exact Hcs
  rw [← Hcs.1]
  iapply entsBigZ_entsBig false esL (cs.map EntryC.model)
  iapply entsBigC_entsBigZ false esL cs (fun h => by cases h) $$ Hb

/-- What a `Ready` gives the driver, after the committed log `d` handed out before it: the
committed entries `ce` to apply next (`C (d ++ ce)`), the entries `es` to append with the right
to, the messages, each one raft may send; a `SoftState`, a `HardState` (`p'` the last non-empty
one, `p` before); the read states, each answering the registrations of its request id
(`srvReadStateOk E.RQ`); no snapshot. (2026-10-27: raft's commit witness of the hard state,
`hsWit`, is gone: the snapshot sender that needed it is unreachable, `rnSnapMsg`.) -/
def rnReadyData (E : RNEnv GF) (γ : RNNames GF) (rd : Ready) (d ce es : List EntryModel)
    (p p' : HardStateM) (S S' : RaftState) (r r' : StateType) (ms : List QMsg) : IProp GF :=
  iprop(∃ (ceL esL msL : List Loc) (hs : HardStateModel),
    rd.CommittedEntries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (d ++ ce) ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗ rnEntsSized esL es ∗ rnAppendRight γ es ∗
    -- (2026-11-03, R2b-3: *enter* at the `Save`) the messages as the node API hands them out, not yet
    -- sent (`rnRawMsgs`: *enter* sends them, or at role leader `readyLeaderMsgs`)
    rd.Messages' ↦*□ msL ∗ ⌜msL = ms.map QMsg.loc⌝ ∗ rnRawMsgs γ ms r' ∗
    -- the soft state, and the role after it (`r'`, from the driver's `r`)
    (∃ ss, softStateIs rd.SoftState' ss ∗ ⌜r' = roleAfter r ss⌝) ∗ hardStateAt rd.HardState' hs ∗
    -- (wal-link L3) canonical when not `nil` (`hsOptC`, the node API's): what the WAL's `Save` takes
    hsOptC rd.HardState' hs.toM ∗
    ⌜p' = phsNext p hs.toM⌝ ∗
    (∃ rsL : List ReadState, rd.ReadStates' ↦*□ rsL ∗ [∗list] rs ∈ rsL, srvReadStateOk E.γr.raft E.RQ rs) ∗
    ⌜es.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term ∧ uint.nat a.index < uint.nat b.index) ∧
      (∀ e, es.head? = some e → uint.nat p.Commit' < uint.nat e.index)⌝ ∗
    ⌜rd.Snapshot' = null⌝ ∗
    -- (2026-10-30, the repair, stage P) the committed entries as the node API freezes them
    rnCeFrozen γ d ce es ∗
    -- (2026-11-03, R2b-1 stage 4) the batch a WAL `Save` step, from the loop's view at the driver's
    -- durable state `S` to the entered one `S'` (`walSaveStep_ready`)
    ⌜WalSaveStep ⟨S, p, none, srvLE γ.srv d⟩ ⟨S', p', none, srvLE γ.srv (d ++ ce)⟩ hs.toM
      (es.map EntryModel.toM) ∧
      -- (P5) the entered durable state the batch's (for a commit-only batch's *enter*), its commit
      -- within its log (`ReadyRestFacts`'; `rnDurK_save.law`'s premise)
      S' = readyDurable S p' none (es.map EntryModel.toM) ∧ uint.nat S'.commit ≤ S'.last⌝)

/-- (R2d'a A6, 2026-11-06; DRAFT) **The ghost log after the committed log `L`**: the log handed out,
`pre ++ L`, completed by the restart point's backend log past it (`γ.a0`; the deleted ViewR.lean's `ghostOf ⟨|pre|,
a0⟩ (pre ++ L)`). At a first start (`a0 = []`) it is `pre ++ L`. -/
def rnGhost (γ : RNNames GF) (L : List EntryModel) : List EntryModel :=
  (γ.pre ++ L) ++ γ.a0.drop (γ.pre ++ L).length

/-- (R2d'a A6, 2026-11-06; DRAFT) **The driver's view of the configuration after the committed log
`L`, over the ghost log** (the deleted ViewR.lean's `rnCfgAtR`): the view after `rnGhost γ L`, every conf entry of it
applied (`srvCfgView`, `InvCfgView.lean`). At a restart, raft's view starts at its configuration
point `min |A₀| σ.commit` (2026-11-24, d6 step 3: until then the backend's consistent index,
`RestartNode`, `bootstrap.go:597`; `notes/restart-plan.md`, R2d' finding 1), possibly past Go's log
while the replay window is open; at a first start it is the view after `pre ++ L`. -/
def rnView (γ : RNNames GF) (L : List EntryModel) : IProp GF :=
  srvCfgView γ.srv γ.nl [] (rnGhost γ L)

/-- The driver's state at the committed log `L` handed out and the hard state `p`, idle, at the
storage's key `γ.key`, the durable state `S` and the role `r` (2026-11-01, durability layer 4). -/
def rnDrvSt (γ : RNNames GF) (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType) :
    NodeDriverState :=
  ⟨memStorIface γ.ms, srvLE γ.srv L, p, none, γ.key, S, r⟩

/-- (R2d'a A6, 2026-11-06; DRAFT) **The restart data** (persistent): a first start (`a0 = []`, and
(A10 item 5, Q28 (i)) the start term `t0 = 0`; (S1, 2026-11-11) the restart point's WAL commit and
snapshot index `commit0 = snap0 = 0`), or a restart (`pre = []`; R2d'a's `σ.b = 0` restriction
lifted by restart S3/S4, 2026-11-11/12: the server's hubs carry Go's start log `P`, `srvRunRestartR`)
whose backend log `a0` is committed (`srvRLogLb`), between the
restored records' snapshot index and commit (`snap0 ≤ |a0| ≤ commit0`). (restart3 A1, 2026-11-15:
row 4, `rnSnapTermAbove`, this incarnation's `MsgSnap`s above `t0`, deleted with the window row it
served.)

(S1, Q31 (a), Q40 F1, 2026-11-11; until then the restart disjunct carried R2d'a's A8,
`rnWinInstallAbove`, row 2, and `rnWalCommitAbove`, row 3, which was false at the start of almost
every restart) Row 2 is now derived (`rnRestartOk_winAbove`), from `|a0| ≤ commit0` and the loop's
fact `commit0 ≤ p.Commit'` (`rnLoopTokP`); row 3 is gone. Of the restart-only premises
(`notes/restart-plan.md`, "R2d'a restart-only premises") the restart disjunct carries
`srvRLogLb γ.srv γ.a0` (8). `snap0 ≤ |a0| ≤ commit0` is a fact of the names
fixed when the node is built, true of every graceful stop's image (`raftNode.stop.spec`'s post);
`|a0| ≤ commit0` is **graceful-only** (after a power loss the backend's consistent index can be above
the WAL's synced commit: crash-design §2.3), so it stays this one conjunct, and nothing that does not
need it (the loop's fact, row 2's `commit0 < snapIdx`) is stated with it.

(2026-11-24, the lifetime law: `notes/etcd-dist-d6.md`, T4 round 5) At a restart, the node's start
term is `t0` (`nodeStartTerm`, `RestartNode`'s post): every `MsgSnap` its `Ready`s hand out is past it
(`readySnapSources_startTerm`; row 4's fact, now raft's law, not a premise).

(2026-11-24, D6 T4 option (a), item 1) And raft's L1 mark at the restart: `a0` committed before every
campaign of the node up to its restored term `t0` (`cmtBefore`, made by `raftState_cmtBefore` where the
restart holds the durable state at `t0`, `NodeStartLinked`), which `raftState_leadAgree` takes at each
*enter*. -/
def rnRestartOk (γ : RNNames GF) : IProp GF :=
  iprop(⌜γ.a0 = [] ∧ γ.t0 = W64 0 ∧ γ.commit0 = 0 ∧ γ.snap0 = 0⌝ ∨
    -- (auth-lease S4, 2026-11-16) a restart only outside the cluster's no-snapshot mode
    -- (`RestartNode`'s)
    (⌜γ.pre = [] ∧ γ.snap0 ≤ γ.a0.length ∧ γ.a0.length ≤ γ.commit0 ∧ ¬ clusterNoSnap γ.node.cl⌝ ∗
      srvRLogLb γ.srv γ.a0 ∗ nodeStartTerm γ.nl γ.t0 ∗
      cmtBefore γ.node.cl γ.id γ.t0 (γ.a0.map EntryModel.toLE)))

instance rnRestartOk_persistent (γ : RNNames GF) : Persistent (rnRestartOk (GF := GF) γ) := by
  unfold rnRestartOk; infer_instance

/-- (2026-11-24, D6 T4 option (a), item 1) **L1's mark at a restart**: a restarted node's backend log
`a0` is marked committed before its campaigns up to the restart's term (raft's `cmtBefore`). -/
theorem rnRestart_cmtBefore (γ : RNNames GF) :
    rnRestartOk (GF := GF) γ ⊢ ⌜γ.a0 ≠ []⌝ -∗ cmtBefore γ.node.cl γ.id γ.t0 (γ.a0.map EntryModel.toLE) := by
  unfold rnRestartOk
  iintro #Hr %hne
  icases Hr with (%Ha | ⟨-, -, -, #Hcb⟩)
  · exact absurd Ha.1 hne
  · iexact Hcb

/-- (S1, 2026-11-11) **The restart point's backend log at or below raft's commit**: from the restart
data and the loop's fact `commit0 ≤ c` (`rnLoopTokP`), `|a0| ≤ c`; at a first start (`a0 = []`)
trivially. (Until S1 `rnRestartOk_commit`, from the false row 3.) -/
theorem rnRestartOk_a0_le (γ : RNNames GF) (c : Nat) (hc : γ.commit0 ≤ c) :
    rnRestartOk (GF := GF) γ ⊢ ⌜γ.a0.length ≤ c⌝ := by
  unfold rnRestartOk
  iintro #Hr
  icases Hr with (%Ha | ⟨%Ha, -⟩)
  · ipureintro; rw [Ha.1]; exact Nat.zero_le _
  · ipureintro; exact Nat.le_trans Ha.2.2.1 hc

/-- (auth-lease S4, 2026-11-16) **In the cluster's no-snapshot mode, a first start** (`a0 = []`): a
restart is outside the mode. -/
theorem rnRestartOk_mode (γ : RNNames GF) :
    rnRestartOk (GF := GF) γ ⊢ ⌜clusterNoSnap γ.node.cl → γ.a0 = []⌝ := by
  unfold rnRestartOk
  iintro #Hr
  icases Hr with (%Ha | ⟨%Ha, -⟩)
  · ipureintro; intro _; exact Ha.1
  · ipureintro; intro hm; exact absurd hm Ha.2.2.2

/-- (R2d'a task 4; S1, 2026-11-11: derived, until then R2d'a's A8 `rnWinInstallAbove`, a premise)
**A `Ready`'s snapshot above the restart point**: a snapshot a `Ready` hands the driver at the hard
state `p` is above `p`'s commit (`readyRest_snap`: raft's `restore` rejects one at or below its
commit), so, with the loop's fact `commit0 ≤ p.Commit'` (`rnLoopTokP`), above the restart point's
WAL commit `commit0` (the crash-proof form, which needs no graceful fact); and, from the restart data
(`|a0| ≤ commit0` at a restart, graceful-only), above the backend's log `a0`, or `a0 = []` (a first
start). -/
theorem rnRestartOk_winAbove (γ : RNNames GF) (L : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) (rd : Ready) (ce : List LogEntry) (es : List EntryM) (h : HardStateM)
    (Lo : Option SnapLoan) (ms : List QMsg) (ss : Option (w64 × StateType))
    (hc : γ.commit0 ≤ uint.nat p.Commit') :
    rnRestartOk (GF := GF) γ ⊢
      (letI := srvStor (GF := GF) γ.node;
        readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss) -∗
      (letI := srvStor (GF := GF) γ.node;
        readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss) ∗
      ⌜(∀ l, Lo = some l → γ.commit0 < uint.nat l.snap.Metadata'.Index') ∧
        (γ.a0 = [] ∨ ∀ l, Lo = some l → γ.a0.length < uint.nat l.snap.Metadata'.Index')⌝ := by
  letI := srvStor (GF := GF) γ.node
  iintro #Hr H
  ihave %Ha0 := rnRestartOk_a0_le γ _ hc $$ Hr
  cases Lo with
  | none =>
    iframe H; ipureintro
    refine ⟨fun l hl => ?_, Or.inr (fun l hl => ?_)⟩ <;> cases hl
  | some l =>
    ihave ⟨H, %Hs⟩ := readyRest_snap γ.node.cl srvClusterN γ.id rd _ ce es h l ms ss $$ H
    iframe H; ipureintro
    have hlt : uint.nat p.Commit' < uint.nat l.snap.Metadata'.Index' := Hs.1
    refine ⟨fun l' hl => ?_, Or.inr (fun l' hl => ?_)⟩
    · cases hl; omega
    · cases hl; omega

/-- **The driver's view of the configuration after the committed log `L`** (D43 M3; 2026-10-30,
the repair: raft's one mode, the old dynamic one's; R2d'a A6, 2026-11-06, DRAFT: over the ghost
log, `rnView`, with the restart data `rnRestartOk`; until then the view after `pre ++ L`, which it
is at a first start, `rnView_first`): every conf entry of the ghost log applied (`srvCfgView`,
`InvCfgView.lean`); until the repair nothing in a static cluster. (Restart S3 item 7, review 5,
2026-11-11: the view alone, `rnView`; until then with the restart data `rnRestartOk`, which is now
`isRaftNode`'s.) -/
def rnCfgAt (γ : RNNames GF) (L : List EntryModel) : IProp GF :=
  rnView γ L

/-- The driver, idle, handed the committed log `L` so far: the node API's `nodeDriver` at
`pre ++ L` (2026-10-27; until then raft's), with the driver's view of the configuration after `L`
(`rnCfgAt`); `p` the hard state of the last `Ready` with a non-empty one. (2026-11-01, durability
layer 4) Beside it the node's durable state, the driver's (`raftState`): the server enters each
`Ready`'s batch after its WAL `Save` (2026-11-03, R2b-3: until then at once, at the receive), from it
and the loop's half of the running token. (R2b-3) The role `r` named: the loop keeps `islead` tied
to it (`rnLoopTokP`). (2026-11-03, R2b-1 stage 3c) The durable state `S` a parameter: the loop's
view of the WAL's durability (`rnLoopTokP`) is at it, and `Advance` keeps it. -/
def rnDrv (γ : RNNames GF) (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType) :
    IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(nodeDriver γ.nl γ.node.cl srvClusterN (rnDrvSt γ L p S r) ∗ rnCfgAt γ L)

/-- (2026-10-31, the snapshot track: #11's S4) The committed log handed out through `L`, at the
node's storage: the storage contract's `DL` (`nodeCommitLb`) at its length (`CreateSnapshot`'s
`J.DL`). (2026-11-02, the lean merge: from the idle driver, whose key names the storage,
`nodeDriver_nodeCommitLb`; until then from `isNode` and `deliveredLogLb`, the open `storDL`.) -/
theorem rn_storDL (γ : RNNames GF) (L : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) :
    rnDrv (GF := GF) γ L p S r ⊢ rnDrv γ L p S r ∗ nodeCommitLb γ.node.cl γ.key (γ.pre ++ L).length := by
  letI := srvStor (GF := GF) γ.node
  iintro Hd
  iunfold rnDrv at Hd
  icases Hd with ⟨Hd, Hcf⟩
  ihave ⟨Hd, #Hc⟩ := nodeDriver_nodeCommitLb γ.nl γ.node.cl srvClusterN _ $$ Hd
  isplitl [Hd Hcf]
  · iunfold rnDrv; iframe
  · iExactEq Hc
    simp [rnDrvSt, srvLE]

/-- The driver with a `Ready` in hand, handed the committed log `d ++ ce`, to append `es`
before `Advance`: the node API's `nodeDriver` busy, without the view; (2026-11-01, durability
layer 4) the batch entered: the node's durable state the driver's. -/
def rnBusyN (γ : RNNames GF) (d ce es : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(nodeDriver γ.nl γ.node.cl srvClusterN
    ⟨memStorIface γ.ms, srvLE γ.srv (d ++ ce), p, some (es.map EntryModel.toM, none), γ.key, S, r⟩)

/-- The driver with a `Ready` in hand (`rnBusyN`) and its view after the log before it, `d`. -/
def rnBusy (γ : RNNames GF) (d ce es : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) : IProp GF :=
  iprop(rnBusyN γ d ce es p S r ∗ rnCfgAt γ d)

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **A received `Ready`'s batch, not yet entered**: the
node's durable state `S` before it (`raftState`) and raft's *enter* (`readyEnter`), from the idle
driver's state at `d`, `p`, `S`, role `r`, to the busy one `st'`, sending the messages `ms`. The loop
fires it after the WAL `Save` (`rn_enter`); a stop before leaves the durable state at `S`, which
the WAL's records hold. -/
def rnPendEnter (γ : RNNames GF) (d : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType)
    (st' : NodeDriverState) (ms : List QMsg) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(readyEnter γ.nl γ.node.cl srvClusterN γ.id
      ⟨memStorIface γ.ms, srvLE γ.srv d, p, none, γ.key, S, r⟩ st' ms)

/-- (2026-11-03, R2b-3) The busy state after a `Ready` without a snapshot. -/
abbrev rnBusyStN (γ : RNNames GF) (d ce es : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) : NodeDriverState :=
  ⟨memStorIface γ.ms, srvLE γ.srv (d ++ ce), p, some (es.map EntryModel.toM, none), γ.key, S, r⟩

/-- (2026-11-03, R2b-3) **The driver with a `Ready` received, not yet entered** (`rnBusy` before
*enter*): the pending *enter* to the busy state, and the view after the log before it. -/
def rnBusyP (γ : RNNames GF) (d ce es : List EntryModel) (p p' : HardStateM) (S S' : RaftState)
    (r r' : StateType) (ms : List QMsg) : IProp GF :=
  iprop(rnPendEnter γ d p S r (rnBusyStN γ d ce es p' S' r') ms ∗ rnCfgAt γ d)

/-- **The node API's read registration of the request id `id`** (persistent; 2026-10-27: what
`E.RQ id n Qr` is for the server): the context `beBytes id` committed to the server's read of
`Qr` (`srvReadQ`), after a committed log at least `n` long (`n` a lower bound of the committed
index at the registration). -/
def srvRQ (γs : ServerRaftNames) (id n : w64) (Qr : List EntryModel → IProp GF) : IProp GF :=
  iprop(∃ l0 : List LogEntry,
    isReadCtx γs.raft.cl srvClusterN (beBytes id) (srvReadQ γs Qr) ∗
    readCtxAfter γs.raft.cl srvClusterN (beBytes id) l0 ∗ ⌜uint.Z n ≤ (l0.length : Int)⌝)

instance srvRQ_persistent (γs : ServerRaftNames) (id n : w64) (Qr : List EntryModel → IProp GF) :
    Persistent (srvRQ (GF := GF) γs id n Qr) := by
  unfold srvRQ; infer_instance

/-- **What the discharge needs of the environment `E`** (persistent; 2026-10-16, stage R7b;
2026-10-27 over the node API): a tick's resource is trivial; the names tied (the server's cluster
is the node's, the start log and index the same); the cluster's conf-change rule the server's
(2026-10-30, the repair: in every cluster; until then in a dynamic one, its decoder; and the
storage's cap at least `1`, which went with the old storage contract); raft's committed log at the
server (`srvRaftLogInv`); a message the node handed out (read-only, sent by it, with its credits)
is one `E.M` admits; `E.C` of a committed log prefix whose next index fits, and back, the committed
log and the indices of what `E.C` holds; `E.RQ` the server's read registration. -/
def rnEnvOk (E : RNEnv GF) (γ : RNNames GF) : IProp GF :=
  iprop(⌜E.T = iprop(True)⌝ ∗
    ⌜E.γr.raft.raft = γ.node ∧ E.γr.raft.pre = γ.pre ∧
      uint.Z E.γr.raft.ai0 = γ.pre.length⌝ ∗
    ⌜γ.node.rule = srvRule E.γr.kv.c0 γ.node.boot⌝ ∗
    srvRaftLogInv E.γr.raft ∗
    -- (raft-entsize §2, 2026-11-09) the message at the content raft handed it out with (`msgOut`,
    -- whose element of the handed-out set gives the size law); until then `msgOwn m □ st`
    □ (∀ (m : Loc) (st : MsgSt), msgOut γ.node.cl m DFrac.discard st ∗
        sentMsg γ.node.cl srvClusterN γ.id st ∗ msgCredits γ.node.cl srvClusterN st ∗ ⌜st.msg.Type' ≠ MsgSnap⌝ -∗
        E.M m) ∗
    □ (∀ L : List EntryModel, srvRLogLb E.γr.raft L -∗
        ⌜uint.Z E.γr.raft.ai0 + 1 + L.length < 2 ^ 64⌝ ={⊤}=∗ □ E.C L) ∗
    □ (∀ L : List EntryModel, E.C L -∗ srvRLogLb E.γr.raft L ∗ ⌜srvIdxOk E.γr.raft.ai0 L⌝) ∗
    ⌜E.RQ = srvRQ E.γr.raft⌝)

instance rnEnvOk_persistent (E : RNEnv GF) (γ : RNNames GF) : Persistent (rnEnvOk E γ) := by
  unfold rnEnvOk; infer_instance

/-- (R2d, Q17 F6) **The environment's raft log invariant, at the node's cluster.** -/
theorem rnEnvOk_logInv (E : RNEnv GF) (γ : RNNames GF) :
    rnEnvOk (GF := GF) E γ ⊢ ⌜E.γr.raft.raft = γ.node⌝ ∗ srvRaftLogInv E.γr.raft := by
  iintro #H
  iunfold rnEnvOk at H
  icases H with ⟨-, %Hn, -, #HRL, -⟩
  iframe HRL
  ipureintro; exact Hn.1

/-- **The run's premise on raft's `Ready`s** (pure, D19b stage 5): the time-receipt bound past
the bootstrap log. (2026-10-27: the node API bounds a `Ready`'s indices itself, `readyRest`; kept
for the wrapper's statements.) -/
def rnLogFits (γ : RNNames GF) : IProp GF :=
  iprop(⌜receiptBound GF + γ.node.boot.length ≤ 2 ^ 61⌝)

instance rnLogFits_persistent (γ : RNNames GF) : Persistent (rnLogFits (GF := GF) γ) := by
  unfold rnLogFits; infer_instance

/-- **The read states' bridge** (persistent): a `ReadState` the node API hands out (`readStateOk`
of its context `c` at its index, its cells read-only) answers the server's registrations
(`srvReadStateOk`). `srvReadStateOk_of_raft` proves it from `rnEnvOk`. -/
def rnReadStateBridge (E : RNEnv GF) (γ : RNNames GF) : IProp GF :=
  iprop(□ ∀ (c : List w8) (i : w64) (v : ReadState),
    readStateOk γ.node.cl srvClusterN c i -∗ ⌜v.Index' = i⌝ -∗ v.RequestCtx' ↦*□ c -∗
      srvReadStateOk E.γr.raft E.RQ v)

instance rnReadStateBridge_persistent (E : RNEnv GF) (γ : RNNames GF) :
    Persistent (rnReadStateBridge E γ) := by
  unfold rnReadStateBridge; infer_instance


/-- **A read state, in the server's terms** (what `rnReadStateBridge` states, under `rnEnvOk`):
its context was committed (`srvCtxDeposited`), and for each registration of it, the read state's
index is past the registration's bound (`readStateOk_after`) and the read's witness holds at it
(`srvReadWit_of`). -/
theorem srvReadStateOk_of_raft [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames GF)
    (c : List w8) (i : w64) (v : ReadState) :
    rnEnvOk E γ ∗ readStateOk γ.node.cl srvClusterN c i ∗ ⌜v.Index' = i⌝ ∗
      v.RequestCtx' ↦*□ c ⊢ srvReadStateOk E.γr.raft E.RQ v := by
  letI := srvAnyStor (GF := GF)
  iintro ⟨#Henv, #Hst, %Hi, #Hctx⟩
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, -, #Hinv, -, -, -, %HRQ⟩
  obtain ⟨Hraft, -, -⟩ := Hn
  rw [HRQ]
  iunfold srvReadStateOk
  iexists c
  iframe Hctx
  isplitr
  · iunfold srvCtxDeposited
    iexists i
    rw [Hraft]
    iexact Hst
  iintro !> %id %n %Qr %Hbs #HRQ'
  iunfold srvRQ at HRQ'
  icases HRQ' with ⟨%l0, #Hrc, #Haft, %Hn0⟩
  subst Hbs
  ihave #Hst' : readStateOk E.γr.raft.raft.cl srvClusterN (beBytes id) i $$ []
  · rw [Hraft]; iexact Hst
  ihave %Hle := readStateOk_after E.γr.raft.raft.cl srvClusterN (beBytes id) i l0 $$ [Hst' Haft]
  · iframe Hst' Haft
  isplitr
  · ipureintro
    rw [Hi]
    have : (uint.nat i : Int) = uint.Z i := by word
    omega
  rw [Hi]
  iapply srvReadWit_of E.γr.raft (beBytes id) Qr i $$ Hinv Hst' Hrc

/-- **The read states' bridge, from `rnEnvOk`** (2026-10-27). -/
theorem rnReadStateBridge_of_raft [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames GF) :
    ⊢ rnEnvOk E γ -∗ rnReadStateBridge E γ := by
  iintro #Henv
  iunfold rnReadStateBridge
  iintro !> %c %i %v #Hst %Hi #Hctx
  iapply srvReadStateOk_of_raft E γ c i v
  iframe Henv Hst Hctx
  ipureintro; exact Hi

/-! ## (D22 J6a) A `Ready` with a snapshot (2026-10-30, the repair: snapshots allowed) -/

/-- (D22 J6a; 2026-10-30, the repair: snapshots allowed, until then `False`) **What a `Ready` with
a snapshot gives the driver**, after the committed log `d`: the node API's snapshot part
(`readySnap … (some l)`: the loan's snapshot, half owned, its certificate, the storage's range from
an index at most the snapshot's with the end, `snapGiven`), the committed log `A'` the snapshot
jumps to (raft's `strip l.dlv`, past `d`), `E.C A'`, the entries `es` to append after it with the
right to, the messages, soft state, hard state (`p'` after `p`) and read states as `rnReadyData`'s;
(2026-10-31, #3) the entries' index bound (`MemoryStorage.Append`'s, the node API's
`readyRest_fits`), the empty committed entries (`updateCommittedIndex`'s) and the last term of
`A'` the snapshot's (its certificate's, `snapshotValid`: the loop's `srvFrozenTerms` after it),
and the snapshot valid (`ApplySnapshot`'s `J.SV`). -/
def rnReadySnap (E : RNEnv GF) (γ : RNNames GF) (rd : Ready) (d es A' : List EntryModel)
    (p p' : HardStateM) (l : SnapLoan) (S S' : RaftState) (r r' : StateType) (ms : List QMsg) :
    IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ (ceL esL msL : List Loc) (hs : HardStateModel),
    -- (2026-11-01, durability layer 4) at the driver's state at receipt, whatever its durable
    -- state and role (`readySnap` reads the storage, the delivered log and the key)
    (∃ (S0 : RaftState) (r : StateType),
      readySnap γ.node.cl srvClusterN γ.id rd (rnDrvSt γ d p S0 r) [] (es.map EntryModel.toM) (some l)) ∗
    -- (2026-11-03, R2b-1 stage 4) the snapshot a WAL `SaveSnap` step and the batch a `Save` step,
    -- from the loop's view at the driver's durable state `S` to the entered one `S'`
    -- (`walSnapSteps_ready`)
    ⌜WalSnapStep ⟨S, p, none, srvLE γ.srv d⟩ l.snap.Metadata' ∧
      WalSaveStep ⟨S, p, some l.snap.Metadata', srvLE γ.srv d⟩ ⟨S', p', none, srvLE γ.srv A'⟩
        hs.toM (es.map EntryModel.toM) ∧
      -- (P5) the entered state raft's, its commit within its log (`rnDurK_save.law`'s premise)
      S' = readyDurable S p' (some l) (es.map EntryModel.toM) ∧ uint.nat S'.commit ≤ S'.last⌝ ∗
    -- (2026-10-31, #3) no committed entries
    rd.CommittedEntries' ↦*□ ceL ∗ entriesAt ceL [] ∗
    ⌜srvLE γ.srv A' = strip l.dlv ∧ d.length < A'.length ∧
      (∀ e0, (es.map EntryModel.toM).head? = some e0 →
        uint.Z e0.Index' + ((es.map EntryModel.toM).length : Int) ≤ 2 ^ 61) ∧
      Option.map EntryModel.term A'.getLast? = some l.snap.Metadata'.Term' ∧
      es.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term ∧ uint.nat a.index < uint.nat b.index)⌝ ∗ □ E.C A' ∗
    snapshotValid γ.node.cl l.snap ∗ nodeInstalledIndex γ.node.cl γ.nl l.snap.Metadata'.Index' ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗ rnEntsSized esL es ∗
    rd.Messages' ↦*□ msL ∗ ⌜msL = ms.map QMsg.loc⌝ ∗ rnRawMsgs γ ms r' ∗
    (∃ ss, softStateIs rd.SoftState' ss ∗ ⌜r' = roleAfter r ss⌝) ∗
    hardStateAt rd.HardState' hs ∗ hsOptC rd.HardState' hs.toM ∗ ⌜p' = phsNext p hs.toM⌝ ∗
    (∃ rsL : List ReadState, rd.ReadStates' ↦*□ rsL ∗
      [∗list] rs ∈ rsL, srvReadStateOk E.γr.raft E.RQ rs))

/-- (keepfix (c) step 1, 2026-11-28) **The server's cluster has a non-empty boot log**
(`srvRaftLogInv`'s log and `srvClusterOk`'s `bootLen`). -/
theorem srvRaftLogInv_bootLen_pos (γ : ServerRaftNames) :
    srvRaftLogInv (GF := GF) γ ⊢ ⌜0 < γ.raft.cl.bootLen⌝ := by
  iintro #H
  iunfold srvRaftLogInv at H
  icases H with ⟨-, #Hcl, -, -, -, -, %Hvs⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, %Hbl, -⟩
  ipureintro
  rw [Hbl, Hvs.2.2.1.1]; exact List.length_pos_iff.mpr Hvs.1

/-- (J8b, 2026-11-01) **A snapshot `Ready` is past the boot log**: its index is at least the boot
log's length. True of raft: a node restores a snapshot only above its committed index
(`raft.restore`), which is at least the boot log's length, so every snapshot a `Ready` hands out is
past it. From raft's `readySnap_bootLen` and the server's cluster at its bootstrap log
(`srvClusterOk`, through `rnEnvOk`). What `applyAll.specSnapM` takes (`|boot| ≤ i`, through
`rnApSnap`). -/
theorem rnReadySnap_bootLen (E : RNEnv GF) (γ : RNNames GF) (rd : Ready) (d es A' : List EntryModel)
    (p p' : HardStateM) (l : SnapLoan) (S S' : RaftState) (r r' : StateType) (ms : List QMsg) :
    ⊢ rnEnvOk E γ -∗ rnReadySnap E γ rd d es A' p p' l S S' r r' ms -∗
      rnReadySnap E γ rd d es A' p p' l S S' r r' ms ∗
      ⌜(γ.node.boot.length : Int) ≤ uint.Z l.snap.Metadata'.Index'⌝ := by
  iintro #Henv H
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, -, #Hinv, -⟩
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨-, #Hcl, -⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, %Hbl, -⟩
  rw [Hn.1] at Hbl
  iunfold rnReadySnap at H
  icases H with ⟨%ceL, %esL, %msL, %hs, ⟨%S0, %r, HrS⟩, Hrest⟩
  ihave ⟨%Hb, HrS⟩ := (letI := srvStor (GF := GF) γ.node; readySnap_bootLen _ _ _ _ _ _ _ _) $$ HrS
  isplitl
  · iunfold rnReadySnap
    iexists ceL, esL, msL, hs
    iframe Hrest
    iexists S0, r
    iexact HrS
  ipureintro
  rw [Hbl] at Hb
  omega

/-- (D22 J6a; 2026-10-30, the repair: until then `False`) **The driver with a snapshot `Ready` in
hand**: the node API's `nodeDriver` busy with the loan, delivered the snapshot's log `A'`, its view
after the log before (`rnCfgAt γ d`, replaced by `Advance`'s answer at the snapshot).
(2026-10-31, the snapshot track) With `readySnap`'s facts `Advance` needs: the snapshot's log is
`A'` (the loan's delivered log, as long as the snapshot's index) past the log before, the index in
`(0, 2^61)`. -/
def rnBusyS (γ : RNNames GF) (d A' es : List EntryModel) (p : HardStateM) (l : SnapLoan)
    (S : RaftState) (r : StateType) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(nodeDriver γ.nl γ.node.cl srvClusterN
      ⟨memStorIface γ.ms, srvLE γ.srv A', p, some (es.map EntryModel.toM, some l), γ.key, S, r⟩ ∗
    rnCfgAt γ d ∗
    ⌜srvLE γ.srv A' = strip l.dlv ∧ srvLE γ.srv d <+: strip l.dlv ∧
      l.dlv.length = uint.nat l.snap.Metadata'.Index' ∧
      0 < uint.Z l.snap.Metadata'.Index' ∧ uint.Z l.snap.Metadata'.Index' < 2 ^ 61 ∧
      -- (R2d'a task 4) the snapshot above the restart point (A8; S1: derived, `rnRestartOk_winAbove`)
      (γ.a0 = [] ∨ γ.a0.length < uint.nat l.snap.Metadata'.Index')⌝)

/-- (2026-11-03, R2b-3) The busy state after a snapshot `Ready`. -/
abbrev rnBusyStS (γ : RNNames GF) (A' es : List EntryModel) (p : HardStateM) (l : SnapLoan) (S : RaftState)
    (r : StateType) : NodeDriverState :=
  ⟨memStorIface γ.ms, srvLE γ.srv A', p, some (es.map EntryModel.toM, some l), γ.key, S, r⟩

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **The driver with a snapshot `Ready` received, not yet
entered** (`rnBusyS` before *enter*). -/
def rnBusySP (γ : RNNames GF) (d A' es : List EntryModel) (p p' : HardStateM) (l : SnapLoan)
    (S S' : RaftState) (r r' : StateType) (ms : List QMsg) : IProp GF :=
  iprop(rnPendEnter γ d p S r (rnBusyStS γ A' es p' l S' r') ms ∗
    rnCfgAt γ d ∗
    ⌜srvLE γ.srv A' = strip l.dlv ∧ srvLE γ.srv d <+: strip l.dlv ∧
      l.dlv.length = uint.nat l.snap.Metadata'.Index' ∧
      0 < uint.Z l.snap.Metadata'.Index' ∧ uint.Z l.snap.Metadata'.Index' < 2 ^ 61 ∧
      -- (R2d'a task 4) the snapshot above the restart point (A8; S1: derived, `rnRestartOk_winAbove`)
      (γ.a0 = [] ∨ γ.a0.length < uint.nat l.snap.Metadata'.Index')⌝)

/-- **The `raft.Node` `n`** (see the file header; 2026-10-30, the repair: raft's unified node API):
its `ApplyConfChange` (the apply thread's, `raftApplyCC`); `Ready` returns the node API's `Ready`
channel (`isReadyChan`); `Advance` takes the busy driver, the view after the batch and the append
receipt, with the loop's half of the running token (refuting a stopped answer), and returns the
idle driver and the node's applied index at least the committed log handed out
(`nodeAppliedLb`; until the repair the storage's floor, `memFloorAtLeast`); `Tick` returns (until
the repair it took a time credit); `Stop` takes the whole running token and stops the node (until
the repair the premise `rnStopOk`); and `ReadIndex(ctx, rctx)`, with the big-endian bytes of a
request id read-only, a lower bound `n` of the committed index (`committedAtLeast E.γr n`), the
read's update and the context's fresh token (until the repair also a read credit), returns an error
the gRPC layer can take, and if `nil` the registration `E.RQ id n` (persistent). (2026-10-27: over
the node API.) -/
def isRaftNodeIfc (E : RNEnv GF) (γ : RNNames GF) (n : GoInterface) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗
    -- (D43 M3, 2026-10-25) its `ApplyConfChange` (the apply thread's)
    raftApplyCC γ.srv γ.nl n ∗
    □ ({{ True }} (App (Val #(methods ni.ty go!"Ready" ni.v)) (Val #()))
      {{ (ch : Loc), RET #ch; isReadyChan γ.nl γ.node.cl srvClusterN ch }}) ∗
    -- (D43 M3) with the view after the batch, its conf entries applied
    □ (∀ (d ce es : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType),
      {{ rnBusyN γ d ce es p S r ∗ rnCfgAt γ (d ++ ce) ∗ rnAdvReceipt γ d ce es ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) }}
        (App (Val #(methods ni.ty go!"Advance" ni.v)) (Val #()))
      -- (2026-10-30, the repair) and the node's applied index past the committed log handed out
      {{ RET #(); rnDrv γ (d ++ ce) p S r ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
          nodeAppliedLb γ.node.cl γ.key (γ.pre ++ d ++ ce).length }}) ∗
    -- (2026-10-30, the repair: snapshots allowed) `Advance` after a snapshot `Ready`: the storage's
    -- `snapReceipt` (the snapshot applied, the entries after it appended) and the snapshot's
    -- certificate; the idle driver at the snapshot's log `A'` with its view there
    □ (∀ (d A' es : List EntryModel) (p : HardStateM) (l : SnapLoan) (S : RaftState) (r : StateType),
      {{ rnBusyS γ d A' es p l S r ∗
          snapReceipt (memStorIface γ.ms) l (es.map EntryModel.toM) ∗
          snapshotCert γ.node.cl srvClusterN (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) ∗
          nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half }}
        (App (Val #(methods ni.ty go!"Advance" ni.v)) (Val #()))
      {{ RET #(); rnDrv γ A' p S r ∗ nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half ∗
          nodeAppliedLb γ.node.cl γ.key (γ.pre ++ A').length }}) ∗
    □ ({{ True }} (App (Val #(methods ni.ty go!"Tick" ni.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ nodeRunning γ.nl γ.node.cl srvClusterN 1 }}
        (App (Val #(methods ni.ty go!"Stop" ni.v)) (Val #()))
      -- (2026-11-03, R2b-3b) and the id vacant (raft's `node.Stop`)
      {{ RET #(); nodeStopped γ.nl γ.node.cl srvClusterN ∗ (∃ x, nodeVacantA γ.node.cl γ.id x) }}) ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice)
        (id n : w64) (Qr : List EntryModel → IProp GF),
      {{ context.isContext ctx cd ∗ sl ↦*□ beBytes id ∗ committedAtLeast E.γr n ∗
          srvReadAu E.γr.raft Qr ∗ srvRdFresh E.γr.raft (beBytes id) }}
        (App (App (Val #(methods ni.ty go!"ReadIndex" ni.v)) (Val #(GoInterface.ok ctx)))
          (Val #sl))
      {{ (err : GoInterface), RET #err; applyErrIs err ∗ nodeReadErrIs err ∗
          (⌜err = GoInterface.nil⌝ -∗ □ E.RQ id n Qr) }}) ∗
    -- (2026-10-27) the node itself (the `Ready` channel's receive takes it)
    (letI := srvStor (GF := GF) γ.node; isNode γ.nl γ.node.cl srvClusterN γ.id))

instance isRaftNodeIfc_persistent (E : RNEnv GF) (γ : RNNames GF) (n : GoInterface) :
    Persistent (isRaftNodeIfc E γ n) := by
  unfold isRaftNodeIfc; infer_instance

/-- The context the request path passes (`mvcc.txnCtx`: `Done()` nil, or Perennial's context)
is one raft's node API takes (`nodeCtx`, the same disjunction). -/
theorem txnCtx_nodeCtx (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    mvcc.txnCtx ctx cd ⊢ nodeCtx ctx cd := by
  unfold mvcc.txnCtx nodeCtx mvcc.doneNil doneNilCtx
  iintro (#H | #H)
  · ileft; iexact H
  · iright; iexact H

/-! ### Receiving a `Ready`: the node API's data in the server's terms -/

/-- (R2d'a A10 item 5) A `MsgSnap` is none of the types sent at term `0` (`SentMsgShape`). -/
theorem msgSnap_not_termless :
    ¬ (MsgSnap = MsgProp ∨ MsgSnap = MsgReadIndex ∨ MsgSnap = MsgTransferLeader) := by
  unfold MsgSnap MsgProp MsgReadIndex MsgTransferLeader; decide

/-- The messages a `Ready` hands out, each one `E.M` admits, with its credits, persisted (the
server's clusters send no `MsgSnap`, `srv_sentMsg_notSnap`). -/
theorem rnMsgOk_of_api [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames GF) :
    ∀ ms : List QMsg,
      ⊢ □ (∀ (m : Loc) (st : MsgSt), msgOut γ.node.cl m DFrac.discard st ∗
          sentMsg γ.node.cl srvClusterN γ.id st ∗ msgCredits γ.node.cl srvClusterN st ∗ ⌜st.msg.Type' ≠ MsgSnap⌝ -∗
          E.M m) -∗ srvClusterOk E.γr.raft -∗ ⌜E.γr.raft.raft = γ.node⌝ -∗
        □ (∀ q : QMsg, ⌜q ∈ ms⌝ -∗ rnMessageSource γ q) -∗
        ([∗list] q ∈ ms, msgOut γ.node.cl q.loc (readyDq q.st) q.st ∗
          sentMsg γ.node.cl srvClusterN γ.id q.st ∗ msgCredits γ.node.cl srvClusterN q.st)
          ={⊤}=∗
        [∗list] m ∈ ms.map QMsg.loc, rnMsgR E γ m
  | [] => by
    iintro #HM - - - -
    imodintro
    simp only [List.map_nil]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | q :: ms => by
    iintro #HM #Hcl %Hraft #Hsrc H
    icases (BigSepL.bigSepL_cons (Φ := fun _ (q : QMsg) => iprop(msgOut (GF := GF) γ.node.cl q.loc
      (readyDq q.st) q.st ∗ sentMsg γ.node.cl srvClusterN γ.id q.st ∗
      msgCredits γ.node.cl srvClusterN q.st))).1 $$ H with ⟨⟨Hm, #Hsm, Hc⟩, Hrest⟩
    ihave #Htail : □ (∀ q' : QMsg, ⌜q' ∈ ms⌝ -∗ rnMessageSource γ q') $$ []
    · iintro !> %q' %hq
      iapply Hsrc $$ %q' %(List.mem_cons_of_mem _ hq)
    ihave #Hq := Hsrc $$ %q %(List.mem_cons_self)
    imod rnMsgOk_of_api E γ ms $$ HM Hcl %Hraft Htail Hrest with Hrest
    simp only [List.map_cons]
    by_cases hsn : q.st.msg.Type' = MsgSnap
    · -- (2026-10-30, the repair) a `MsgSnap`: owned, for `msgSnapC`
      imodintro
      iapply (BigSepL.bigSepL_cons (Φ := fun _ m => rnMsgR (GF := GF) E γ m)).2
      iframe Hrest
      iunfold rnMsgR
      iright
      iunfold rnSnapMsg
      iexists q.st
      have hdq : readyDq q.st = DFrac.own 1 := by
        unfold readyDq; rw [hsn]; exact if_neg (by unfold RespType; decide)
      rw [hdq] at *
      ihave ⟨Hm, #Huf⟩ := (letI := srvStor (GF := GF) γ.node;
        msgOut_snapUf γ.node.cl q.loc (DFrac.own 1) q.st hsn) $$ Hm
      ihave Hm := (letI := srvStor (GF := GF) γ.node;
        msgOut_msgOwn γ.node.cl q.loc (DFrac.own 1) q.st) $$ Hm
      iframe Hm Hsm Hc Huf Hq
      ipureintro; exact hsn
    -- (raft-entsize §2) frozen at the content raft handed it out with
    imod (letI := srvStor (GF := GF) γ.node;
      msgOut_persist_fupd γ.node.cl q.loc (readyDq q.st) q.st ⊤) $$ Hm with #Hm
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := fun _ m => rnMsgR (GF := GF) E γ m)).2
    iframe Hrest
    iunfold rnMsgR
    ileft
    iexists q.st
    iframe Hm
    isplitr
    · ipureintro; exact hsn
    iapply HM $$ %q.loc %q.st
    iframe Hm Hsm Hc
    ipureintro; exact hsn

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **A `Ready`'s messages, sent**: the raw messages
(`rnRawMsgs`) with their sends (`readyMsgs`, from *enter*) are each one the transport takes
(`rnMsgR`). -/
theorem rnRawMsgs_sent [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames GF)
    (ms : List QMsg) (r' : StateType) :
    ⊢ rnEnvOk E γ -∗ rnRawMsgs γ ms r' -∗
      (letI := srvStor (GF := GF) γ.node; readyMsgs γ.node.cl srvClusterN γ.id ms) ={⊤}=∗
      [∗list] m ∈ ms.map QMsg.loc, rnMsgR E γ m := by
  letI := srvStor (GF := GF) γ.node
  iintro #Henv Hraw #Hsent
  iunfold rnRawMsgs at Hraw
  icases Hraw with ⟨Hmo, -, #Hsrc⟩
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, -, #Hinv, #HM, -⟩
  ihave #Hcl : srvClusterOk E.γr.raft $$ []
  · iunfold srvRaftLogInv at Hinv; icases Hinv with ⟨-, #H, -⟩; iexact H
  ihave Hmo := readyMsgs_sentC γ.node.cl srvClusterN γ.id ms $$ [$Hmo $Hsent]
  iapply rnMsgOk_of_api E γ ms $$ HM Hcl %Hn.1 Hsrc Hmo

/-- (2026-11-03, R2b-3) **A leader's messages, sent before *enter*** (raft's `readyLeaderMsgs`). -/
theorem rnRawMsgs_leader [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames GF)
    (ms : List QMsg) (r' : StateType) (hr : r' = StateLeader) :
    ⊢ rnEnvOk E γ -∗ rnRawMsgs γ ms r' ={⊤}=∗ [∗list] m ∈ ms.map QMsg.loc, rnMsgR E γ m := by
  letI := srvStor (GF := GF) γ.node
  iintro #Henv Hraw
  iunfold rnRawMsgs at Hraw
  icases Hraw with ⟨Hmo, Hl, #Hsrc⟩
  ihave #Hsent := Hl $$ %hr
  iapply rnRawMsgs_sent E γ ms r' $$ Henv [Hmo] Hsent
  iunfold rnRawMsgs
  iframe Hmo Hsrc
  iintro -
  iexact Hsent

/-- The read states a `Ready` hands out, each answering the server's registrations (through
the bridge). -/
theorem rnReadStates_of_api (E : RNEnv GF) (γ : RNNames GF) :
    ∀ (vs : List ReadState) (sts : List ReadStateM),
      ⊢ rnReadStateBridge E γ -∗
        ([∗list] v;st ∈ vs;sts, ⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx') -∗
        ([∗list] st ∈ sts, readStateOk γ.node.cl srvClusterN st.RequestCtx' st.Index') -∗
        [∗list] v ∈ vs, srvReadStateOk E.γr.raft E.RQ v
  | [], _ => by
    iintro - - -
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | v :: vs, sts => by
    iintro #Hbr H2 #Hok
    icases (BigSepL2.bigSepL2_cons_inv_left (Φ := fun _ (v : ReadState) (st : ReadStateM) =>
      iprop(⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx'))).1 $$ H2
      with ⟨%st, %sts', %Hsts, ⟨%Hi, #Hc⟩, H2'⟩
    subst Hsts
    icases (BigSepL.bigSepL_cons (Φ := fun _ (st : ReadStateM) =>
      readStateOk (GF := GF) γ.node.cl srvClusterN st.RequestCtx' st.Index')).1 $$ Hok
      with ⟨#Hok1, #Hok'⟩
    ihave #Hrest := rnReadStates_of_api E γ vs sts' $$ Hbr H2' Hok'
    iapply (BigSepL.bigSepL_cons (Φ := fun _ v => srvReadStateOk (GF := GF) E.γr.raft E.RQ v)).2
    iframe Hrest
    iunfold rnReadStateBridge at Hbr
    iapply Hbr $$ %st.RequestCtx' %st.Index' %v Hok1 %Hi Hc

/-- Raft's read-only entries, as the server's `entriesAt` (the models converted). -/
theorem entriesAt_of_entRO (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRO l e) ⊢ entriesAt (GF := GF) ls (es.map EntryModel.ofM) := by
  iintro #H
  icases BigSepL2.bigSepL2_length $$ H with %Hlen
  iunfold entriesAt
  isplitr
  · ipureintro; simp [Hlen]
  iintro !> %n %l %m %Hl %Hm
  rw [List.getElem?_map] at Hm
  cases He : es[n]? with
  | none => rw [He] at Hm; cases Hm
  | some e =>
    rw [He] at Hm
    simp only [Option.map_some, Option.some.injEq] at Hm
    subst Hm
    ihave #He' := (BigSepL2.bigSepL2_lookup (Φ := fun _ l e => entRO (GF := GF) l e) Hl He) $$ H
    iunfold entryAt
    rw [EntryModel.toM_ofM]
    iexact He'

/-- The committed entries a `Ready` hands out after the base `b`, as the server's records. -/
def rnCe (b : Nat) (ce : List LogEntry) : List EntryModel :=
  (LogEntry.toEntries ce b).map EntryModel.ofM

theorem rnCe_toLE (b : Nat) (ce : List LogEntry) :
    (rnCe b ce).map EntryModel.toLE = ce := by
  unfold rnCe LogEntry.toEntries
  apply List.ext_getElem?
  intro n
  simp only [List.getElem?_map, List.getElem?_mapIdx]
  cases ce[n]? <;> rfl

theorem rnCe_length (b : Nat) (ce : List LogEntry) : (rnCe b ce).length = ce.length := by
  simp [rnCe, LogEntry.toEntries]

theorem rnCe_index (b : Nat) (ce : List LogEntry) (n : Nat) (m : EntryModel)
    (h : (rnCe b ce)[n]? = some m) : m.index = W64 ((b : Int) + n + 1) := by
  unfold rnCe LogEntry.toEntries at h
  simp only [List.getElem?_map, List.getElem?_mapIdx] at h
  cases hc : ce[n]? with
  | none => rw [hc] at h; cases h
  | some x =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    simp [EntryModel.ofM, LogEntry.toEntryM]

/-- The Ready that delivered the applied prefix, at its hard-state term. -/
def rnBatchSource (γ : RNNames GF) (t : w64) (bound : Nat) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ ms installed, readySnapSources γ.node.cl γ.nl γ.id t ms bound installed)

instance (γ : RNNames GF) (t : w64) (bound : Nat) :
    Persistent (rnBatchSource (GF := GF) γ t bound) := by
  unfold rnBatchSource; infer_instance

/-- The outgoing message and the applying batch can be from different Ready
calls. The equality of terms is supplied by the server's term check. -/
theorem srv_snapshot_index_le (γ : RNNames GF) (rd : ReadNames) (pin : GName)
    (q : QMsg) (sv : SnapshotM) (bound : Nat)
    (ht : q.st.msg.Type' = MsgSnap) (hs : q.st.snap = some sv)
    (hb : γ.snap0 ≤ bound) :
    letI := srvStor (GF := GF) γ.node
    rnMessageSource γ q ⊢ rnBatchSource γ q.st.msg.Term' bound -∗
      sentMsg γ.node.cl srvClusterN γ.id q.st -∗ dghostVar pin DFrac.discard γ.nl.installs -∗
      nodeTagPin γ.node.cl γ.nl (fun s => iprop(snapshotValid γ.node.cl s ∗
        srvStoredOrigin γ.node.cl rd.cursor pin γ.snap0 s)) -∗
      ▷ (monoNatAuthOwn rd.cursor 1 bound -∗ monoNatAuthOwn rd.cursor 1 bound ∗ ⌜uint.nat sv.Metadata'.Index' ≤ bound⌝) := by
  letI := srvStor (GF := GF) γ.node
  iintro #Hsrc #Hobs #Hsent #Hpin #Htag
  iunfold rnMessageSource at Hsrc
  icases Hsrc with ⟨%term, %ms, %limit, %inst, %hq, #Hsrc⟩
  iunfold rnBatchSource at Hobs
  icases Hobs with ⟨%other, %oinst, #Hobs⟩
  ihave #Hlead := sentMsg_localSnapshotLeader γ.node.cl srvClusterN γ.id q.st ht $$ Hsent
  ihave ⟨%s, %heq, Hproof⟩ := readySnapSources_le γ.node.cl γ.nl γ.id q.st.msg.Term' term
    ms other limit bound q _ hq ht (.inr rfl) inst oinst $$ Hsrc Hobs Hlead Htag
  have he : s = sv := Option.some.inj (heq.symm.trans hs)
  subst s
  icases Hproof with (Hsv | %h)
  · inext
    icases Hsv with ⟨-, Horigin⟩
    iunfold srvStoredOrigin at Horigin
    iintro Hown
    icases Horigin with (%hi | Hlb | ⟨%n, #Hn, #Hinstalled⟩)
    · iframe Hown; ipureintro; omega
    · ihave %hi := monoNatLbOwn_valid rd.cursor _ _ _ $$ Hown Hlb
      iframe Hown
      ipureintro; exact hi.2
    · ihave %hn := dghostVar_agree pin n.installs DFrac.discard γ.nl.installs DFrac.discard $$ Hn Hpin
      ihave #Hinstalled := nodeInstalledIndex_installs γ.node.cl n γ.nl hn _ $$ Hinstalled
      ihave %hi := readySnapSources_installed_le γ.node.cl γ.nl γ.id term ms other limit bound
        inst oinst q sv hq ht hs $$ Hsrc Hobs Hlead Hinstalled
      iframe Hown; ipureintro; omega
  · inext; iintro Hown; iframe Hown; ipureintro; omega

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **The hard state `p` committed** (persistent), for a
batch of the log `pre ++ L`: empty, or its commit index committed at its term and at least
`|pre ++ L|` (what raft's receive gives without *enter*; `rnRtOk_of_hsC` makes the loop's
`rnRtOk` of it). -/
def rnHsC (γ : RNNames GF) (p : HardStateM) (L : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(rnBatchSource γ p.Term' (srvLE γ.srv L).length ∗
    -- (keepfix (c) step 1, 2026-11-28) the bound in the zero case too (F1), and a nonzero term with a
    -- nonzero commit index (F2', the server's boot log non-empty)
    (⌜p = hsZero ∧ ((srvLE γ.srv L).length : Int) ≤ uint.Z p.Commit'⌝ ∨
      committedAtTerm γ.node.cl srvClusterN p.Term' p.Commit' ∗
      ⌜((srvLE γ.srv L).length : Int) ≤ uint.Z p.Commit' ∧
        (1 ≤ uint.Z p.Commit' → p.Term' ≠ W64 0)⌝))

instance rnHsC_persistent (γ : RNNames GF) (p : HardStateM) (L : List EntryModel) :
    Persistent (rnHsC (GF := GF) γ p L) := by
  unfold rnHsC; infer_instance

/-- (2026-10-27) **Receiving a `Ready`, after the node API's receive** (`isReadyChan_recvAu`'s
postcondition, `readyGot`): the idle driver at `L` learns the `Ready`'s data in the server's terms
and is busy with it; the messages persisted, `E.C` of the committed log (`rnEnvOk`), the read states
answered (`rnReadStateBridge`); and the committed log delivered through the batch (`deliveredLogLb`,
for a dynamic cluster's `ApplyConfChange`). (2026-11-03, R2b-3: *enter* at the `Save`) *Enter* is not
fired here: the node's durable state `S` and raft's wand go to the pending busy driver (`rnBusyP`,
`rnBusySP`), which the loop fires after its WAL `Save` (`rn_enter`, `rn_enterS`); the messages stay
raw (`rnRawMsgs`), and the hard state's committed fact comes from the receive (`rnHsC`). (Until
then *enter* was applied here, with the loop's half of the running token.) -/
theorem rn_ready_recv [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames GF)
    (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType) (rd : Ready)
    (HLi : srvIdxOkW E.γr.raft.ai0 L) (Hc0 : γ.commit0 ≤ uint.nat p.Commit') :
    letI := srvStor (GF := GF) γ.node
    rnEnvOk E γ -∗ rnReadStateBridge E γ -∗ rnRestartOk γ -∗ rnCfgAt γ L -∗
      readyGot γ.nl γ.node.cl srvClusterN γ.id (rnDrvSt γ L p S r) rd ={⊤}=∗
      ((∃ ce' es' p' S' r' ms, rnReadyData E γ rd L ce' es' p p' S S' r r' ms ∗
        rnBusyP γ L ce' es' p p' S S' r r' ms ∗
        deliveredLogLb γ.nl γ.node.cl srvClusterN (srvLE γ.srv (L ++ ce')) ∗
        rnHsC γ p' (L ++ ce') ∗
        ⌜srvIdxOkW E.γr.raft.ai0 (L ++ ce')⌝ ∗
        -- (S1) raft's commit never drops (`readyRest_commit_mono`), for the loop's fact
        ⌜uint.nat p.Commit' ≤ uint.nat p'.Commit'⌝) ∨
      -- (2026-10-30, the repair: snapshots allowed) a `Ready` with a snapshot
      (∃ (es' A' : List EntryModel) (p' : HardStateM) (l : SnapLoan) (S' : RaftState)
          (r' : StateType) (ms : List QMsg),
        rnReadySnap E γ rd L es' A' p p' l S S' r r' ms ∗ rnBusySP γ L A' es' p p' l S S' r r' ms ∗
        rnHsC γ p' A' ∗
        ⌜srvIdxOkW E.γr.raft.ai0 A'⌝ ∗ ⌜uint.nat p.Commit' ≤ uint.nat p'.Commit'⌝)) := by
  letI := srvStor (GF := GF) γ.node
  iintro #Henv #Hbr #Hrok Hcfg Hgot
  iunfold readyGot at Hgot
  icases Hgot with ⟨%ce, %es, %h, %Lo, %ms, %ss, #Hsource, #Hce, #Hcom, ⟨%sts, #Hrs, #Hrsok⟩, Hrest, Hlead,
    Henter, #Hdlb0, #Hhsc⟩
  ihave #HmsgSrc : □ (∀ q : QMsg, ⌜q ∈ ms⌝ -∗ rnMessageSource γ q) $$ []
  · iintro !> %q %hq
    iunfold rnMessageSource
    iexists (phsNext p h).Term', ms, ((rnDrvSt γ L p S r).afterReady ce es h Lo ss).delivered.length,
      (Lo.map fun l => l.snap.Metadata'.Index')
    isplitr
    · ipureintro; exact hq
    iExactEq Hsource; rfl
  -- (R2d'a task 4) a snapshot's index above the restart point (A8; S1: derived, from the loop's fact)
  ihave ⟨Hrest, %Hwa2⟩ := rnRestartOk_winAbove γ L p S r rd ce es h Lo ms ss Hc0 $$ Hrok Hrest
  have Hwa := Hwa2.2
  -- (S1) raft's commit never drops
  ihave ⟨Hrest, %Hcm⟩ := readyRest_commit_mono γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r)
    ce es h Lo ms ss $$ Hrest
  simp only [rnDrvSt] at Hcm
  iunfold readyLeaderMsgs at Hlead
  simp only [committedEntriesAt, rnDrvSt]
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hn, -, #Hinv, #HM, #HC, -, -⟩
  obtain ⟨Hraft, Hpre, Hai0⟩ := Hn
  ihave #Hcl : srvClusterOk E.γr.raft $$ []
  · iunfold srvRaftLogInv at Hinv; icases Hinv with ⟨-, #H, -⟩; iexact H
  -- (out_size C3) the server's cluster bounds proposed data: a `Ready`'s entries are sized
  ihave %Hmd := srvRaftLogInv_maxData E.γr.raft $$ Hinv
  have Hmd' : γ.node.cl.maxData = some (2 ^ 30) := by rw [← Hraft]; exact Hmd
  -- (keepfix (c) step 1) the boot log non-empty, for the hard state's nonzero term (F2')
  ihave %Hbpos := srvRaftLogInv_bootLen_pos E.γr.raft $$ Hinv
  rw [Hraft] at Hbpos
  cases Lo with
  | some l =>
    -- a snapshot `Ready`: the snapshot's log `A'` (the loan's delivered log after the start log),
    -- committed, so `E.C A'`; the messages as without a snapshot
    ihave #Hfits : readyFits γ.node.cl srvClusterN $$ []
    · iunfold srvClusterOk at Hcl; icases Hcl with ⟨-, -, -, #H, -⟩; rw [Hraft]; iexact H
    simp only [NodeDriverState.afterReady]
    icases readyRest_fits γ.node.cl srvClusterN γ.id rd _ ce es h (some l) ms ss $$ [Hfits Hrest]
      with ⟨Hrest, %Hfit61⟩
    · iframe Hfits Hrest
    simp only [readyRest, readySnap]
    icases Hrest with ⟨#HesO, Hmsgs, Hmo, -, #Hhs, #Hss, -, ⟨%Hsp, Hown, #Hcom2, #Hcert, Hold,
      Hgiv⟩, %Hrrf⟩
    icases readyEnts_rn _ _ _ _ Hmd' $$ HesO with ⟨%esL, #HesL, #Hesz, #Hesro⟩
    obtain ⟨Hdlv, Hptr, Hce0, Hpfx, Hlt, Hdl, Hpos, H61, Hfl, Hli⟩ := Hsp
    subst Hce0
    obtain ⟨A', HA'⟩ : ∃ A', A' = (l.dlv.drop γ.pre.length).map EntryModel.ofM := ⟨_, rfl⟩
    have Hpre' : γ.pre.map EntryModel.toLE <+: strip l.dlv := by
      refine List.IsPrefix.trans ?_ Hpfx
      simp only [srvLE, List.map_append]
      exact List.prefix_append _ _
    have hA' : srvLE γ.srv A' = strip l.dlv := by
      have ht := List.prefix_iff_eq_take.1 Hpre'
      rw [List.length_map] at ht
      rw [HA']
      simp only [srvLE, List.map_append, List.map_map]
      have hc : (EntryModel.toLE ∘ EntryModel.ofM) = LogEntry.ofEntryM := rfl
      rw [hc, List.map_drop, ht]
      exact List.take_append_drop _ _
    have hlen' : (γ.pre ++ A').length = l.dlv.length := by
      have h := congrArg List.length hA'
      simp only [srvLE, strip, List.length_map] at h
      exact h
    have hLA : L.length < A'.length := by
      have h := Hlt
      simp only [srvLE, List.length_map, List.length_append] at h hlen'
      omega
    -- the indices of the loan's delivered log: `k + 1` at `k`
    have hkI : ∀ (k : Nat) (e : EntryM), l.dlv[k]? = some e → e.Index' = W64 (k + 1) := by
      intro k e he
      rw [Hdlv] at he
      unfold LogEntry.toEntries at he
      rw [List.getElem?_mapIdx] at he
      cases hx : (strip l.dlv)[k]? with
      | none => rw [hx] at he; cases he
      | some x =>
        rw [hx] at he
        simp only [Option.map_some, Option.some.injEq] at he
        subst he
        simp only [LogEntry.toEntryM]
        congr 1; omega
    have HidxA : ∀ (n : Nat) (m : EntryModel), A'[n]? = some m →
        uint.Z m.index = uint.Z E.γr.raft.ai0 + 1 + n := by
      intro n m hm
      rw [HA', List.getElem?_map, List.getElem?_drop] at hm
      cases hx : l.dlv[γ.pre.length + n]? with
      | none => rw [hx] at hm; cases hm
      | some x =>
        rw [hx] at hm
        simp only [Option.map_some, Option.some.injEq] at hm
        subst hm
        have hb : γ.pre.length + n < l.dlv.length := (List.getElem?_eq_some_iff.1 hx).1
        have hI := hkI _ x hx
        simp only [EntryModel.ofM, hI, Hai0]
        have : ((γ.pre.length + n + 1 : Nat) : Int) < 2 ^ 61 := by
          have := Hdl; have := uint_nat_eq l.snap.Metadata'.Index'; omega
        word
    have HsrvLE : srvLE E.γr.raft A' = srvLE γ.srv A' := by
      unfold srvLE RNNames.srv; rw [Hpre]
    -- (2026-10-31, #3) the last term of `A'`: the snapshot's (its certificate's committed log)
    ihave #HisCl : isCluster γ.node.cl srvClusterN $$ []
    · iunfold srvClusterOk at Hcl; icases Hcl with ⟨#H, -⟩; rw [Hraft]; iexact H
    ihave #HsvV := snapshotCert_valid γ.node.cl srvClusterN l.snap Hpos H61 $$ [HisCl Hcert]
    · iframe HisCl Hcert
    ihave #HsvV0 := HsvV
    iunfold snapshotValid at HsvV
    icases HsvV with ⟨%lc, %mc, #Hlc, -, -, %Hlcf⟩
    ihave %Hag := isCommittedLogLb_agree γ.node.cl lc (strip l.dlv) $$ [Hlc Hcom2]
    · iframe Hlc Hcom2
    have hlastA : Option.map EntryModel.term A'.getLast? = some l.snap.Metadata'.Term' := by
      have hl1 : lc.length = (strip l.dlv).length := by
        rw [Hlcf.1]; unfold strip; rw [List.length_map, Hdl]
      have hlc : lc = strip l.dlv := by
        rcases Hag with hp | hp
        · exact hp.eq_of_length hl1
        · exact (hp.eq_of_length hl1.symm).symm
      have hlast := Hlcf.2.2.1
      rw [hlc, ← hA'] at hlast
      have hne : A' ≠ [] := by intro h; rw [h] at hLA; simp at hLA
      obtain ⟨Ai, a, hAeq⟩ : ∃ Ai a, A' = Ai ++ [a] :=
        ⟨A'.dropLast, A'.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
      rw [hAeq] at hlast ⊢
      simp only [srvLE, ← List.append_assoc, List.map_append, List.map_cons, List.map_nil,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some] at hlast ⊢
      exact hlast
    icases entsPts_elim _ _ _ $$ Hce with ⟨%ceL, #HceL, #Hcero⟩
    imod ownSlice_persist _ _ _ $$ Hmsgs with #Hmsgs
    ihave #Hcom' : isCommittedLogLb E.γr.raft.raft.cl (srvLE E.γr.raft A') $$ []
    · rw [HsrvLE, hA', Hraft]; iexact Hcom2
    imod srvRLogLb_intro E.γr.raft ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full) A'
        HidxA $$ Hinv Hcom' with #HLb
    ihave %HLiW := srvRLogLb_idx E.γr.raft _ $$ HLb
    imod HC $$ %A' HLb [] with #HEC
    · ipureintro
      rw [Hai0]
      have h := hlen'
      have := Hdl; have := uint_nat_eq l.snap.Metadata'.Index'
      simp only [List.length_append] at h
      omega
    imodintro
    iright
    iexists es.map EntryModel.ofM, A', phsNext p h, l, readyDurable S (phsNext p h) (some l) es,
      roleAfter r ss, ms
    isplitl [Hown Hold Hgiv Hmo Hlead]
    · iunfold rnReadySnap
      iexists ceL, esL, ms.map QMsg.loc, HardStateModel.ofM h
      rw [EntryModel.map_toM_ofM]
      ihave #Hinstalled : nodeInstalledIndex γ.node.cl γ.nl l.snap.Metadata'.Index' $$ []
      · iapply readySnapSources_installed γ.node.cl γ.nl γ.id (phsNext p h).Term'
          l.snap.Metadata'.Index' ms (strip l.dlv).length
        iExactEq Hsource; rfl
      iframe Hmsgs HEC HesL HceL HsvV0 Hinstalled
      isplitl [Hown Hold Hgiv]
      · iexists S, r
        simp only [readySnap, rnDrvSt]
        iframe Hown Hcom2 Hcert Hold Hgiv
        ipureintro; exact ⟨Hdlv, Hptr, trivial, Hpfx, Hlt, Hdl, Hpos, H61, Hfl, Hli⟩
      isplitr
      · ipureintro
        rw [HardStateModel.toM_ofM]
        have Hst := walSnapSteps_ready (rnDrvSt γ L p S r) [] es h l (srvLE γ.srv A') Hrrf
          ?Hcons ?Hpfx ?Hlen ?Hlast
        · obtain ⟨Hst1, Hst2⟩ := Hst
          refine ⟨by simpa only [rnDrvSt] using Hst1, by simpa only [rnDrvSt] using Hst2, rfl, ?_⟩
          · have h2 := Hrrf.2.1
            simp only [rnDrvSt] at h2
            exact h2
        · intro j e he
          have := Hli j e he
          simp only [snapId] at this
          word
        · simpa only [rnDrvSt, hA'] using Hpfx
        · rw [hA']; simpa only [strip, List.length_map] using Hdl
        · have hne : A' ≠ [] := by intro h0; simp [h0] at hLA
          simp only [srvLE, List.getLast?_map, List.getLast?_append, hne] at hlastA ⊢
          obtain ⟨m, hm, ht⟩ : ∃ m, A'.getLast? = some m ∧ m.term = l.snap.Metadata'.Term' := by
            cases h1 : A'.getLast? with
            | none => rw [h1] at hlastA; cases hlastA
            | some m => rw [h1] at hlastA; exact ⟨m, rfl, Option.some.inj hlastA⟩
          simp [hm, ht, EntryModel.toLE]
      isplitr
      · have h0 : (LogEntry.toEntries [] (srvLE γ.srv L).length).map EntryModel.ofM = [] := by
          simp [LogEntry.toEntries]
        rw [← h0]
        iapply entriesAt_of_entRO ceL _ $$ Hcero
      isplitr
      · ipureintro; exact ⟨hA', hLA, Hfit61, hlastA, List.pairwise_map.mpr Hrrf.2.2.2.2.2⟩
      isplitr
      · iapply entriesAt_of_entRO esL es $$ Hesro
      isplitr
      · iexact Hesz
      isplitr
      · ipureintro; rfl
      isplitl [Hmo Hlead]
      · iunfold rnRawMsgs; iframe Hmo HmsgSrc; iexact Hlead
      isplitr
      · iexists ss; iframe Hss; ipureintro; rfl
      isplitr
      · iunfold hardStateAt
        rw [HardStateModel.toM_ofM]
        iapply hsOptC_hsOpt; iexact Hhs
      isplitr
      · rw [HardStateModel.toM_ofM]; iexact Hhs
      isplitr
      · rw [HardStateModel.toM_ofM]; ipureintro; rfl
      iunfold readStatesPts at Hrs
      icases Hrs with ⟨%vs, #Hvs, #Hrs2⟩
      iexists vs
      iframe Hvs
      iapply rnReadStates_of_api E γ vs sts $$ Hbr Hrs2 Hrsok
    isplitl [Hcfg Henter]
    · iunfold rnBusySP
      iframe Hcfg
      isplitl [Henter]
      · iunfold rnPendEnter
        iExactEq Henter
        simp only [rnBusyStS, rnDrvSt, EntryModel.map_toM_ofM, hA']
      ipureintro
      exact ⟨hA', Hpfx, Hdl, Hpos, H61, Hwa.imp_right (fun h => h l rfl)⟩
    isplitr
    · iunfold rnHsC
      isplitr
      · iunfold rnBatchSource
        iexists ms, (some l.snap.Metadata'.Index')
        rw [hA']
        iExactEq Hsource; rfl
      icases Hhsc with (%Hz | ⟨#Hc, %Hle⟩)
      · ileft; ipureintro; rw [hA']; simpa only [strip, List.length_map] using Hz
      · iright; iframe Hc; ipureintro; rw [hA']
        exact ⟨by simpa only [strip, List.length_map] using Hle.1, Hle.2 Hbpos⟩
    ipureintro; exact ⟨HLiW, Hcm⟩
  | none =>
  simp only [NodeDriverState.afterReady]
  ihave #Hfits : readyFits γ.node.cl srvClusterN $$ []
  · iunfold srvClusterOk at Hcl; icases Hcl with ⟨-, -, -, #H, -⟩; rw [Hraft]; iexact H
  icases readyRest_fits γ.node.cl srvClusterN γ.id rd _ ce es h none ms ss $$ [Hfits Hrest]
    with ⟨Hrest, %Hfit61⟩
  · iframe Hfits Hrest
  simp only [readyRest, readySnap]
  icases Hrest with ⟨#HesO, Hmsgs, Hmo, -, #Hhs, #Hss, %Hbnd, ⟨%Hsnap, Happ, #Hcf, %Hidx⟩, %Hrrf⟩
  icases readyEnts_rn _ _ _ _ Hmd' $$ HesO with ⟨%esL, #HesL, #Hesz, #Hesro⟩
  obtain ⟨Lx, HLx, Hes0, Hdl, -⟩ := Hbnd
  obtain ⟨ce', Hce'def⟩ : ∃ ce', ce' = rnCe (srvLE γ.srv L).length ce := ⟨_, rfl⟩
  have Hce'LE : ce'.map EntryModel.toLE = ce := by rw [Hce'def]; exact rnCe_toLE _ ce
  have Hce'len : ce'.length = ce.length := by rw [Hce'def]; exact rnCe_length _ ce
  have Hdel : srvLE γ.srv (L ++ ce') = srvLE γ.srv L ++ ce := by
    rw [srvLE_append, Hce'LE]
  have HsrvLE : srvLE E.γr.raft (L ++ ce') = srvLE γ.srv (L ++ ce') := by
    unfold srvLE RNNames.srv; rw [Hpre]
  have Hlen : ((srvLE γ.srv (L ++ ce')).length : Int) ≤ Lx := by
    rw [Hdel]; simpa [rnDrvSt] using Hdl
  have hfit : (γ.pre.length : Int) + L.length + ce'.length < 2 ^ 64 := by
    have : (srvLE γ.srv (L ++ ce')).length = γ.pre.length + L.length + ce'.length := by
      simp [srvLE]; omega
    omega
  icases entsPts_elim _ _ _ $$ Hce with ⟨%ceL, #HceL, #Hcero⟩
  imod ownSlice_persist _ _ _ $$ Hmsgs with #Hmsgs
  -- `E.C (L ++ ce)` from the committed log, the next index fitting
  ihave #Hcom' : isCommittedLogLb E.γr.raft.raft.cl (srvLE E.γr.raft (L ++ ce')) $$ []
  · rw [HsrvLE, Hdel, Hraft]; iexact Hcom
  ihave #Hfits' : readyFits E.γr.raft.raft.cl srvClusterN $$ []
  · first | (rw [Hraft]; iexact Hfits) | (rw [← Hraft]; iexact Hfits)
  ihave %Hnext := isCommittedLogLb_length E.γr.raft.raft.cl srvClusterN _ $$ [Hfits' Hcom']
  · iframe Hfits' Hcom'
  have HLi' : ∀ (n : Nat) (m : EntryModel), (L ++ ce')[n]? = some m →
      uint.Z m.index = uint.Z E.γr.raft.ai0 + 1 + n := by
    intro n m hm
    rcases Nat.lt_or_ge n L.length with hn | hn
    · rw [List.getElem?_append_left hn] at hm
      exact (HLi n m hm).1
    · rw [List.getElem?_append_right hn] at hm
      have hl : (n - L.length) < ce'.length := (List.getElem?_eq_some_iff.1 hm).1
      rw [Hce'def] at hm
      have hi := rnCe_index _ ce _ m hm
      have hl' : (srvLE γ.srv L).length = γ.pre.length + L.length := by
        simp [srvLE, RNNames.srv]
      rw [hi, hl']
      have : ((γ.pre.length + L.length : Nat) : Int) + ((n - L.length : Nat) : Int) + 1 < 2 ^ 64 := by
        push_cast
        omega
      rw [Hai0]
      word
  imod srvRLogLb_intro E.γr.raft ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full) (L ++ ce') HLi' $$ Hinv Hcom'
    with #HLb
  ihave %HLiW := srvRLogLb_idx E.γr.raft _ $$ HLb
  imod HC $$ %(L ++ ce') HLb [] with #HEC
  · ipureintro
    rw [HsrvLE, srvLE_length] at Hnext
    simp only [RNNames.srv] at Hnext
    rw [Hai0]
    simp only [List.length_append] at Hnext ⊢
    omega
  imodintro
  ileft
  iexists ce', es.map EntryModel.ofM, phsNext p h, readyDurable S (phsNext p h) none es,
    roleAfter r ss, ms
  isplitl [Happ Hmo Hlead]
  · iunfold rnReadyData
    iexists ceL, esL, ms.map QMsg.loc, HardStateModel.ofM h
    iframe HceL HesL Hmsgs HEC
    isplitr
    · rw [Hce'def]; unfold rnCe
      iapply entriesAt_of_entRO ceL _ $$ Hcero
    isplitr
    · iapply entriesAt_of_entRO esL es $$ Hesro
    isplitr
    · iexact Hesz
    isplitl [Happ]
    · iunfold rnAppendRight
      rw [EntryModel.map_toM_ofM]
      iframe Happ
      ipureintro
      constructor
      · intro e0 He0
        rw [List.head?_map] at He0
        cases Hh : es.head? with
        | none => rw [Hh] at He0; cases He0
        | some x =>
          rw [Hh] at He0; cases He0
          have := Hfit61 x Hh
          simp only [List.length_map]
          show uint.Z x.Index' + (es.length : Int) ≤ 2 ^ 61
          omega
      · intro e0 He0 j e He
        rw [List.head?_map] at He0
        rw [List.getElem?_map] at He
        cases Hh : es.head? with
        | none => rw [Hh] at He0; cases He0
        | some x =>
          rw [Hh] at He0; cases He0
          cases Hj : es[j]? with
          | none => rw [Hj] at He; cases He
          | some y =>
            rw [Hj] at He; cases He
            exact (Hidx x Hh).1 j y Hj
    isplitr
    · ipureintro; rfl
    isplitl [Hmo Hlead]
    · iunfold rnRawMsgs; iframe Hmo HmsgSrc; iexact Hlead
    isplitr
    · iexists ss; iframe Hss; ipureintro; rfl
    isplitr
    · iunfold hardStateAt
      rw [HardStateModel.toM_ofM]
      iapply hsOptC_hsOpt; iexact Hhs
    isplitr
    · rw [HardStateModel.toM_ofM]; iexact Hhs
    isplitr
    · rw [HardStateModel.toM_ofM]; ipureintro; rfl
    isplitr
    · iunfold readStatesPts at Hrs
      icases Hrs with ⟨%vs, #Hvs, #Hrs2⟩
      iexists vs
      iframe Hvs
      iapply rnReadStates_of_api E γ vs sts $$ Hbr Hrs2 Hrsok
    isplitr
    · ipureintro
      refine ⟨List.pairwise_map.mpr Hrrf.2.2.2.2.2.2.2, ?_⟩
      intro e he
      rw [List.head?_map] at he
      cases hx : es.head? with
      | none => simp [hx] at he
      | some x =>
        simp [hx] at he
        subst e
        exact Hrrf.2.2.2.2.2.1 x hx
    isplitr
    · ipureintro; exact Hsnap
    iunfold rnCeFrozen
    rw [EntryModel.map_toM_ofM, Hce'LE]
    iframe Hcf
    ipureintro
    refine ⟨Hidx, ?_, ?_⟩
    · -- (R2b-1 stage 4) the batch a WAL `Save` step (`walSaveStep_ready`)
      rw [HardStateModel.toM_ofM, Hdel]
      have Hst := walSaveStep_ready (rnDrvSt γ L p S r) ce es h Hrrf
        (fun j e e0 he0 hj => (Hidx e0 he0).1 j e hj)
      simpa only [rnDrvSt] using Hst
    · refine ⟨?_, ?_⟩
      · first | rfl | simp only [EntryModel.map_toM_ofM, HardStateModel.toM_ofM]
      · have h2 := Hrrf.2.1
        simp only [rnDrvSt] at h2
        first | exact h2 | (simp only [EntryModel.map_toM_ofM]; exact h2)
  isplitl [Hcfg Henter]
  · iunfold rnBusyP
    iframe Hcfg
    iunfold rnPendEnter
    iExactEq Henter
    simp only [rnBusyStN, rnDrvSt, EntryModel.map_toM_ofM, Hdel]
  isplitr
  · iExactEq Hdlb0; rw [Hdel]
  isplitr
  · iunfold rnHsC
    isplitr
    · iunfold rnBatchSource
      iexists ms, (none)
      rw [Hdel]
      iExactEq Hsource; rfl
    icases Hhsc with (%Hz | ⟨#Hc, %Hle⟩)
    · ileft; ipureintro; rw [Hdel]; simpa only [List.length_append] using Hz
    · iright; iframe Hc; ipureintro; rw [Hdel]
      exact ⟨by simpa only [List.length_append] using Hle.1, Hle.2 Hbpos⟩
  ipureintro; exact ⟨HLiW, Hcm⟩

/-! ## The other components -/

/-- **The `*raft.MemoryStorage` `ms`**: `Append` of the `Ready`'s entries turns the right into the
receipt (raft's `MemoryStorage.Append.spec`, `node_contract_memstor`; 2026-10-30, the repair: over
the range contract, the receipt with nothing frozen). (out_size C2) The entries as frozen objects at
contents of bounded size (`entsROz true`: each `entSizeOk`), in place of `entriesAt`: the server's
cluster bounds proposed data (`maxData = some 2^30`), so its storage is sized (the node API's
`isStorage`), and a `Ready`'s entries come so (`readyEnts`, `Cluster.outEnt_size`). -/
def isRNMemStor (γ : RNNames GF) (ms : Loc) : IProp GF :=
  iprop(□ (∀ (sl : GoSlice) (es : List EntryModel),
    {{ entsROz true sl (es.map EntryModel.toM) ∗ rnAppendRight γ es }}
      (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #sl))
    {{ RET #(GoInterface.nil); rnAppendReceipt γ es }}))

instance isRNMemStor_persistent (γ : RNNames GF) (ms : Loc) :
    Persistent (isRNMemStor (GF := GF) γ ms) := by
  unfold isRNMemStor; infer_instance

/-- (2026-10-31) **The wrapper `r`'s WAL open, at the fraction `q`**: the open token
(`storage.walOpen`) of the WAL of `r`'s storage. The raft loop holds a half, the apply thread the
other (for its disk snapshot's `SaveSnap`), which `stopped` brings back to the loop for `Close`.
(wal-link L3) The WAL is the names' (`γ.wal.h`), which the storage's contract is over (`isRaftNode`). -/
def rnWalTok (γ : RNNames GF) (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ st : GoInterface, rnStorageAddr r ↦□ st ∗ storage.walOpen γ.wal.h q)

theorem rnWalTok_half (γ : RNNames GF) (r : Loc) :
    rnWalTok (GF := GF) γ r (1 : Qp).half ∗ rnWalTok γ r (1 : Qp).half ⊢ rnWalTok γ r 1 := by
  unfold rnWalTok
  iintro ⟨⟨%st1, #H1, T1⟩, ⟨%st2, #H2, T2⟩⟩
  iexists st1
  iframe H1
  have h := ((storage.walOpen_fractional (GF := GF) γ.wal.h).fractional
    (1 : Qp).half (1 : Qp).half).2
  rw [Qp.half_add_half] at h
  iapply h
  iframe T1 T2

/-- The token at the storage `st` the wrapper `r` holds. -/
theorem rnWalTok_open (γ : RNNames GF) (r : Loc) (q : Qp) :
    rnWalTok (GF := GF) γ r q ⊢ storage.walOpen γ.wal.h q := by
  unfold rnWalTok
  iintro ⟨%st', -, T⟩
  iexact T

/-- The token back from the WAL's open share. -/
theorem rnWalTok_close (γ : RNNames GF) (r : Loc) (st : GoInterface) (q : Qp) :
    rnStorageAddr r ↦□ st ∗ storage.walOpen γ.wal.h q ⊢ rnWalTok (GF := GF) γ r q := by
  unfold rnWalTok
  iintro ⟨#Hst, T⟩
  iexists st
  iframe Hst T

/-- The loop's half and the half `stopped` brings back (`rnStopBag`'s, at the WAL of `r`'s
storage `st`) make the whole token (`onStop`'s `Close`). -/
theorem rnWalTok_join (γ : RNNames GF) (r : Loc) (st : GoInterface) :
    rnStorageAddr r ↦□ st ∗ rnWalTok (GF := GF) γ r (1 : Qp).half ∗
      storage.walOpen γ.wal.h (1 : Qp).half ⊢ rnWalTok γ r 1 := by
  iintro ⟨#Hst, T1, T2⟩
  iapply rnWalTok_half γ r
  iframe T1
  iunfold rnWalTok
  iexists st
  iframe Hst T2

theorem rnWalTok_split (γ : RNNames GF) (r : Loc) :
    rnWalTok (GF := GF) γ r 1 ⊢ rnWalTok γ r (1 : Qp).half ∗ rnWalTok γ r (1 : Qp).half := by
  unfold rnWalTok
  iintro ⟨%st, #H, T⟩
  icases ((storage.walOpen_fractional (GF := GF) γ.wal.h).fractional (1 : Qp).half
      (1 : Qp).half).1 $$ [T] with ⟨T1, T2⟩
  · rw [Qp.half_add_half]; iexact T
  isplitl [T1]
  · iexists st; iframe H T1
  · iexists st; iframe H T2

/-- (2026-11-03, R2b-1 stage 5; review M3) **The apply side's share of the WAL** at the fraction `q`
(its disk snapshot's `SaveSnap`): the open token's share, the apply thread's token `ν.app` (which
rules out the stop's taken state), and the durability invariant; `run` gives it to the loop with
`raftNode.stop` (`rnStopBag`). (wal-link L3) With the apply thread's reader token of the storage's lock
(`walStorRd`, `NewStorage`'s second), which its `SaveSnap` and `Release` take, and the storage's contract
(`isRaftNode`'s, which the apply thread's snapshot path does not otherwise hold). -/
def rnWalTokA (γ : RNNames GF) (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ st : GoInterface, rnStorageAddr r ↦□ st ∗ storage.walOpen γ.wal.h q ∗
    token γ.wal.app ∗ rnDurInvK γ.node γ.id γ.walK γ.wal.h ∗ walStorRd st γ.wal.h ∗
    isWalStorage st γ.wal.h γ.ss ∗
    -- (P5, T6 placeholder) the snapshot directory's durability the trivial one, until T6 links it
    ⌜γ.walK.sd = fun _ => iprop(True)⌝)

/-- (2026-11-03, R2b-1 stage 6) **The loop's share of the WAL**: half the open token, the stop's
claim (`ν.stop`) and what `Close` takes besides the records (the member's metadata, the purge's
right), from `bootstrap` (`wal.bootOk_start`), kept until `onStop`. (wal-link L3) With the loop's reader
token of the storage's lock (`walStorRd`, `NewStorage`'s first), which its `Save`, `SaveSnap` and `Sync` take. -/
def rnWalTokL (γ : RNNames GF) (r : Loc) : IProp GF :=
  iprop(rnWalTok γ r (1 : Qp).half ∗ token γ.wal.stop ∗
    -- (2026-11-03, R2b-3b) the metadata naming the member `γ.id` (the stop image's `walFiles`)
    ∃ (st : GoInterface) (cid : w64), rnStorageAddr r ↦□ st ∗
      walMetaIs γ.wal.h γ.id cid ∗ walPurgeRight γ.wal.h ∗ walStorRd st γ.wal.h)

/-- **The transport `tr`** (`rafthttp.Transporter`): `Send` takes the slice of messages, each one
raft may send, borrowing `E.S` (2026-10-24); `Stop` returns, taking `E.ST` (D43 M5c). -/
def isRNTransport (E : RNEnv GF) (tr : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tr = GoInterface.ok ti⌝ ∗
    □ (∀ (sl : GoSlice) (msL : List Loc),
      {{ sl ↦* msL ∗ ([∗list] m ∈ msL, rnMsgOk E m) ∗ E.S }}
        (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #sl))
      {{ RET #(); E.S }}) ∗
    □ ({{ E.ST }} (App (Val #(methods ti.ty go!"Stop" ti.v)) (Val #())) {{ RET #(); True }}))

instance isRNTransport_persistent (E : RNEnv GF) (tr : GoInterface) :
    Persistent (isRNTransport E tr) := by
  unfold isRNTransport; infer_instance

/-- **The timeout detector `td`** (`*contention.TimeoutDetector`, trust boundary: names-only;
the raft loop's alone): `Reset` and `Observe` return. -/
def isRNTimeoutDetector (td : Loc) : IProp GF :=
  iprop(⌜td ≠ null⌝ ∗
    □ ({{ True }}
        (App (Val (td @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.contention.TimeoutDetector.ty
          @!! go!"Reset")) (Val #()))
      {{ RET #(); True }}) ∗
    □ (∀ to : w64, {{ True }}
        (App (Val (td @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.contention.TimeoutDetector.ty
          @!! go!"Observe")) (Val #to))
      {{ (ok : Bool) (d : time.Duration), RET (PairV #ok #d); True }}))

instance isRNTimeoutDetector_persistent (td : Loc) :
    Persistent (isRNTimeoutDetector (GF := GF) td) := by
  unfold isRNTimeoutDetector; infer_instance

/-- **The `isIDRemoved` closure** (the server's): returns some `bool`. -/
def isRNIDRemoved (f : GoFunc) : IProp GF :=
  iprop(□ (∀ id : w64, {{ True }} (App (Val #f) (Val #id)) {{ (b : Bool), RET #b; True }}))

instance isRNIDRemoved_persistent (f : GoFunc) : Persistent (isRNIDRemoved (GF := GF) f) := by
  unfold isRNIDRemoved; infer_instance

/-- **The ready handler `rh`** (the server's four closures, `run`): each returns; and
`updateCommittedIndex` keeps the raft loop's resource `R` (2026-10-13, the request path's unit
4c: the server's `R` is the committed index's writer half, `∃ v, srvCommittedOwn γr v`, which the
raft loop owns across its iterations; the wrapper's proofs are parametric in `R`), and (2026-10-14,
unit C2a) leaves the committed index at least its argument (`committedAtLeast γr v`: the server's
closure raises it to `v` if it is below), given (2026-10-16, stage R7b) a committed log reaching
the argument. -/
def isReadyHandler (rh : Loc) (R : IProp GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ (gl ul uls uci : GoFunc),
    structFieldRef raftReadyHandler go!"getLead" rh ↦□ gl ∗
    structFieldRef raftReadyHandler go!"updateLead" rh ↦□ ul ∗
    structFieldRef raftReadyHandler go!"updateLeadership" rh ↦□ uls ∗
    structFieldRef raftReadyHandler go!"updateCommittedIndex" rh ↦□ uci ∗
    □ ({{ True }} (App (Val #gl) (Val #())) {{ (v : w64), RET #v; True }}) ∗
    □ (∀ v : w64, {{ True }} (App (Val #ul) (Val #v)) {{ RET #(); True }}) ∗
    □ (∀ b : Bool, {{ True }} (App (Val #uls) (Val #b)) {{ RET #(); True }}) ∗
    -- (2026-10-16, stage R7b) with a committed log reaching the index (the committed index's
    -- invariant keeps one, `srvCommittedInv`)
    □ (∀ (v : w64) (L : List EntryModel),
      {{ R ∗ srvRLogLb γr.raft L ∗ ⌜uint.Z v ≤ uint.Z γr.raft.ai0 + L.length⌝ }}
        (App (Val #uci) (Val #v))
      {{ RET #(); R ∗ committedAtLeast γr v }}))

instance isReadyHandler_persistent (rh : Loc) (R : IProp GF) (γr : ReadNames) :
    Persistent (isReadyHandler (GF := GF) rh R γr) := by
  unfold isReadyHandler; infer_instance

/-- **The ticker `tk`** (what `newRaftNode` makes: since 2026-11-03 from Perennial's proved
`time.NewTicker`, `isRNTicker_of_time`): its `C` is a channel on which a receive yields some time
and nothing else (2026-11-05, the user's S1: until then a tick's resource `E.T`, the environment's,
from stage R7b, 2026-10-16, when raft's tick credit came with the tick; since D19b, 2026-10-18,
`E.T` was `True` for the server, `raftNode.tick` taking the credit, a time receipt, from a Go step
of its own, and the tick receive in `raftNode.start` drops what the bag gives), or nil
(`newRaftNode`'s `&time.Ticker{}` when `heartbeat == 0`: dead since 2026-11-03, the specs
requiring a positive heartbeat, a scope restriction; kept for covering it later); `Stop`
returns. -/
def isRNTicker (tk : Loc) : IProp GF :=
  iprop(∃ c : Loc, structFieldRef time.Ticker go!"C" tk ↦□ c ∗
    (⌜c = chan.nil⌝ ∨ ∃ γc : ChanNames, isChanBag γc c (V := time.Time) (fun _ => iprop(True))) ∗
    □ ({{ True }} (App (Val (tk @!! go.GoType.PointerType time.Ticker.ty @!! go!"Stop")) (Val #()))
      {{ RET #(); True }}))

instance isRNTicker_persistent (tk : Loc) : Persistent (isRNTicker (GF := GF) tk) := by
  unfold isRNTicker; infer_instance

/-- `tickMu`'s resource: `latestTickTs`, a `q`-fraction. -/
def rnTickInv (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ t : time.Time, rnLatestTickTsAddr r ↦{DFrac.own q} t)

/-- **The levels of a thread token that borrow a reader slot of `tickMu`** (`rnTickPool`; srvloops2,
2026-11-21, bounds B2 for `tickMu`): its only reader is `ensureLeadership`'s `isActive`, called by the
revocation's outer goroutine with its level 3 (levels 1 and 2 lent to its pools for the round,
`RevokeCtx.lean`) and by `LeaseRenew` on a gRPC run with its spare level 4 (`v3rpc.ctxErrLvl`; level 3
is the run pool's for the run). The read lock is held only inside `getLatestTickTs`. -/
abbrev rnTickLvlOk (l : Nat) : Prop := l = 3 ∨ l = 4

/-- The namespace of `tickMu`'s pools of reader slots. -/
def rnTickPoolN0 : Namespace := nroot .@ "etcdserver_tick_pool"

/-- The namespace of `tickMu`'s pool of reader slots at level `l`. -/
def rnTickPoolN (l : Nat) : Namespace := rnTickPoolN0 .@ l

/-- **`tickMu`'s pools of reader slots** (persistent; srvloops2, 2026-11-21, bounds B2 for `tickMu`):
at each level `rnTickLvlOk` admits, a thread pool of the lock's reader slots
(`sync.ownRWMutex mu (rnTickInv r)`), made when the wrapper is installed (`isRaftNode_of_rnParts`,
half of the fresh lock's slots each), from which a reader of `latestTickTs` borrows one around
`getLatestTickTs` (until then the slots were dropped, and `ensureLeadership.spec` assumed its read
lock needed none). -/
def rnTickPool (r mu : Loc) : IProp GF :=
  iprop(∀ l : Nat, ⌜rnTickLvlOk l⌝ → ∃ γ : GName,
    threadPool.isThreadPoolL (rnTickPoolN l) l γ (sync.ownRWMutex mu (rnTickInv r)))

instance rnTickPool_persistent (r mu : Loc) : Persistent (rnTickPool (GF := GF) r mu) := by
  unfold rnTickPool; infer_instance


/-! ## `applyc` -/

/-- A unit channel with no logical content (`notifyc`, `stopped`). -/
def isUnitBag (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Unit) (fun _ => iprop(True)))

instance isUnitBag_persistent (c : Loc) : Persistent (isUnitBag (GF := GF) c) := by
  unfold isUnitBag; infer_instance

/-- `stopped` (D43 M5c): a unit channel each of whose values carries `E.ST`, the right to stop
the transport, which the loop's `onStop` uses; and (2026-10-30, the repair) the apply side's half
of the node's running token (`rnRunHalf`'s other half: `raftNode.stop` is called once the scheduler
is drained, so the apply thread no longer needs it), which with the loop's makes the whole token
`node.Stop` takes; (2026-10-31) and the apply side's half of the WAL `w`'s open token, which with
the loop's makes the whole `Close` takes (etcd closes the WAL only once the apply thread is done,
`server.go:819-831`). -/
def rnStopBag (E : RNEnv GF) (γ : RNNames GF) (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Unit) (fun _ => iprop(E.ST ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
    storage.walOpen γ.wal.h (1 : Qp).half ∗
    -- (2026-11-03, R2b-1 stage 6; review M3) the apply thread's WAL token, with its half
    token γ.wal.app)))

instance rnStopBag_persistent (E : RNEnv GF) (γ : RNNames GF) (c : Loc) :
    Persistent (rnStopBag E γ c) := by
  unfold rnStopBag; infer_instance

/-- `raftAdvancedC` (D19i part 1, 2026-10-18: the fork closes it after every `Advance`, and
`applyAll` waits for it before snapshotting or compacting): a broadcast channel, never sent on,
closed once (`make(chan struct{}, 1)`: a `stopChan`), its close carrying `P` (the node's applied
index past the batch, `rnApP`; until the repair the storage's floor); a reader's view of it. -/
def rnAdvChan (c : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ γc : ChanNames, ownStopChan c γc P .Unknown)

instance rnAdvChan_persistent (c : Loc) (P : IProp GF) : Persistent (rnAdvChan (GF := GF) c P) := by
  unfold rnAdvChan; infer_instance


/-- (D22 S-b, item 2) **The raft term a batch carries** (`toApply.raftTerm`, the term of the last
non-empty `HardState`, raft.go:222), for the snapshot sender's merged snapshot: `0` (no hard state
yet), or a term the log through some index `c` was committed at (raft's `committedAtTerm`), `c` at
least the batch's log, `n` entries long. (2026-10-27 to 2026-10-31 `True`; 2026-10-31, from the
node API's `nodeDriver_hardStateCommitted`.) -/
def rnRtOk (γ : RNNames GF) (t : w64) (n : Nat) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(
    -- (keepfix (c) step 1, 2026-11-28) a zero term carries no log, or the restart's term `t0` is not
    -- zero (Go's `raftTerm` is still `0` only before the first non-empty `HardState`, while raft's
    -- `prevHardSt` is the restored one): with the apply thread's mirror, a non-empty batch raises it
    -- to a nonzero term
    ⌜t = W64 0 → n = 0 ∨ γ.t0 ≠ W64 0⌝ ∗
    (⌜t = W64 0⌝ ∨ ∃ c : w64, committedAtTerm γ.node.cl srvClusterN t c ∗ ⌜(n : Int) ≤ uint.Z c⌝ ∗ ⌜(γ.a0.length : Int) ≤ uint.Z c⌝ ∗ rnBatchSource γ t n))

instance rnRtOk_persistent (γ : RNNames GF) (t : w64) (n : Nat) :
    Persistent (rnRtOk (GF := GF) γ t n) := by
  unfold rnRtOk; infer_instance

/-- Before evaluating GetTerm the worker can retain a conditional index
bound. Its first Go step discharges the storage tag's later modality. -/
theorem srv_merge_index (γ : RNNames GF) (rd : ReadNames) (pin : GName)
    (q : QMsg) (sv : SnapshotM) (term : w64) (bound : Nat)
    (ht : q.st.msg.Type' = MsgSnap) (hs : q.st.snap = some sv)
    (hb : γ.snap0 ≤ bound) :
    letI := srvStor (GF := GF) γ.node
    rnMessageSource γ q ⊢ rnRtOk γ term bound -∗ sentMsg γ.node.cl srvClusterN γ.id q.st -∗
      dghostVar pin DFrac.discard γ.nl.installs -∗ nodeTagPin γ.node.cl γ.nl
        (fun s => iprop(snapshotValid γ.node.cl s ∗ srvStoredOrigin γ.node.cl rd.cursor pin γ.snap0 s)) -∗
      ▷ (⌜q.st.msg.Term' = term⌝ -∗ monoNatAuthOwn rd.cursor 1 bound -∗ monoNatAuthOwn rd.cursor 1 bound ∗
        ⌜uint.nat sv.Metadata'.Index' ≤ bound⌝) := by
  letI := srvStor (GF := GF) γ.node
  iintro #Hsrc #Hrt #Hsent #Hloc #Hpin
  by_cases he : q.st.msg.Term' = term
  · subst term
    iunfold rnRtOk at Hrt
    icases Hrt with ⟨-, (%hzero | ⟨%c, -, -, -, #Hbatch⟩)⟩
    · ihave %shape := sentMsg_shape γ.node.cl srvClusterN γ.id q.st $$ Hsent
      exact False.elim (shape.1.2.2.2.1 (by rw [ht]; exact msgSnap_not_termless) hzero)
    · ihave Hle := srv_snapshot_index_le γ rd pin q sv bound ht hs hb
        $$ Hsrc Hbatch Hsent Hloc Hpin
      inext; iintro -; iexact Hle
  · inext; iintro %he'; exact False.elim (he he')

/-- A durable apply can outlive the last WAL commit. In that case the old
incarnation's commit receipt covers the image. The new Ready still supplies
the receipt for the batch and its snapshot-source observation. (keepfix (c) step 1) With the zero
term's fact `hz`. -/
theorem rnRtOk_of_commit (γ : RNNames GF) (rt cur : w64) (n : Nat)
    (hn : (n : Int) ≤ uint.Z cur) (hz : rt = W64 0 → n = 0 ∨ γ.t0 ≠ W64 0) :
    letI := srvStor (GF := GF) γ.node
    committedAtTerm γ.node.cl srvClusterN rt cur -∗ rnBatchSource γ rt n -∗
    (⌜(γ.a0.length : Int) ≤ uint.Z cur⌝ ∨ ∃ old cover : w64,
      committedAtTerm γ.node.cl srvClusterN old cover ∗
      ⌜uint.Z old ≤ uint.Z rt ∧ (γ.a0.length : Int) ≤ uint.Z cover⌝) -∗
    rnRtOk γ rt n := by
  letI := srvStor (GF := GF) γ.node
  iintro #Hcur #Hsrc Hboot
  iunfold rnRtOk
  isplitr
  · ipureintro; exact hz
  iright
  icases Hboot with (%within | ⟨%old, %cover, #Hprior, %prior⟩)
  · iexists cur; iframe Hcur Hsrc; isplit <;> ipureintro <;> assumption
  · by_cases within : (γ.a0.length : Int) ≤ uint.Z cur
    · iexists cur; iframe Hcur Hsrc; isplit <;> ipureintro <;> assumption
    · ihave #Hcover := committedAtTerm_mono_term γ.node.cl srvClusterN old rt cover cur prior.1 $$ Hprior Hcur
      iexists cover; iframe Hcover Hsrc
      isplit <;> ipureintro <;> omega

/-- Build the apply job from the receive's hard state. A graceful restart
provides the first disjunct. A retained pre-crash receipt supplies the second
even when the recovered commit is below the backend index. (keepfix (c) step 1, 2026-11-28) The
loop's term `rt` is `prevHardSt`'s, or `0` while `prevHardSt` is still the restored one (term `t0`):
so a zero term with a non-empty log has `t0 ≠ 0`. -/
theorem rnRtOk_of_hsC (γ : RNNames GF) (rt : w64) (L : List EntryModel) (p : HardStateM)
    (Hrt : rt = p.Term' ∨ (uint.Z rt = 0 ∧ p.Term' = γ.t0)) :
    letI := srvStor (GF := GF) γ.node
    rnHsC γ p L -∗
    (⌜(γ.a0.length : Int) ≤ uint.Z p.Commit'⌝ ∨ ∃ old cover : w64,
      committedAtTerm γ.node.cl srvClusterN old cover ∗
      ⌜uint.Z old ≤ uint.Z rt ∧ (γ.a0.length : Int) ≤ uint.Z cover⌝) -∗
    rnRtOk γ rt (rnLogOf γ L).length := by
  letI := srvStor (GF := GF) γ.node
  iintro #Hc Hboot
  iunfold rnHsC at Hc
  icases Hc with ⟨#Hsrc, #Hc⟩
  have hlen : ((rnLogOf γ L).length : Int) = ((srvLE γ.srv L).length : Int) := by
    simp [srvLE, rnLogOf, RNNames.srv]
  ihave %Hp : ⌜((srvLE γ.srv L).length : Int) ≤ uint.Z p.Commit' ∧
      (1 ≤ uint.Z p.Commit' → p.Term' ≠ W64 0)⌝ $$ []
  · icases Hc with (%Hz | ⟨-, %Hle⟩)
    · ipureintro
      refine ⟨Hz.2, fun h1 => ?_⟩
      rw [Hz.1] at h1; exfalso; revert h1; simp only [hsZero]; word
    · ipureintro; exact Hle
  have hz : rt = W64 0 → (rnLogOf γ L).length = 0 ∨ γ.t0 ≠ W64 0 := by
    intro h0
    by_cases hl : (rnLogOf γ L).length = 0
    · exact Or.inl hl
    · right
      have h1 : 1 ≤ uint.Z p.Commit' := by omega
      have hT := Hp.2 h1
      rcases Hrt with Hrt | ⟨-, Ht⟩
      · exact absurd (Hrt ▸ h0) hT
      · rw [← Ht]; exact hT
  by_cases h0 : rt = W64 0
  · iunfold rnRtOk
    isplitr
    · ipureintro; exact hz
    ileft; ipureintro; exact h0
  · have Hrt' : rt = p.Term' := by
      rcases Hrt with Hrt | ⟨Hz, -⟩
      · exact Hrt
      · exact absurd (by word) h0
    subst Hrt'
    icases Hc with (%Hz | ⟨#Hc, %Hle⟩)
    · exfalso; apply h0; rw [Hz.1]
    · ihave #Hsrc' : rnBatchSource γ p.Term' (rnLogOf γ L).length $$ []
      · iExactEq Hsrc; simp [srvLE, rnLogOf, RNNames.srv]
      iapply rnRtOk_of_commit γ p.Term' p.Commit' (rnLogOf γ L).length (by omega) hz $$ Hc Hsrc' Hboot

/-- (D22l) `prevHardSt`'s update by a `Ready` of the server's hard state `hs`. -/
theorem phsNext_toM_empty (p : HardStateM) (hs : HardStateModel) (h : hs = HardStateModel.empty) :
    phsNext p hs.toM = p := by
  have h' := (HardStateModel.toM_zero_iff hs).2 h
  rw [h']; exact phsNext_zero p

theorem phsNext_toM_ne (p : HardStateM) (hs : HardStateModel) (h : hs ≠ HardStateModel.empty) :
    phsNext p hs.toM = hs.toM := by
  apply phsNext_ne
  intro ⟨h1, h2, h3⟩
  apply h
  apply (HardStateModel.toM_zero_iff hs).1
  cases hhs : hs.toM
  rw [hhs] at h1 h2 h3
  simp only at h1 h2 h3
  rw [h1, h2, h3]

/-- (D43 M3, 2026-10-25) A batch has a `ConfChange` entry (raft.go's `confChanged` scan). -/
def ccIn [GooseExts] (ce : List EntryModel) : Bool := ce.any (fun m => decide (m.typ = W32 1))

/-- (D43 M3) The driver's view goes to the apply thread with the batch `ce`: a conf entry in it
(the apply thread applies it; the second `notifyc` send brings the view back). (2026-10-30, the
repair: in every cluster; until then only in raft's dynamic mode.) -/
def rnHands (_γ : RNNames GF) (ce : List EntryModel) : Bool := ccIn ce

/-- (2026-11-03, R2b-1 stage 5) **The handed log is at least `n` long** (persistent): a committed log
of length at least `n` the loop handed at a `Save` (`walCommitLb`); what the apply thread's own
snapshot at an applied index `n` takes (the batch's `raftAdvancedC`, closed after the `Save`). -/
def rnWalHanded (γ : RNNames GF) (n : Nat) : IProp GF :=
  iprop(∃ l : List LogEntry, walCommitLb γ.wal l ∗ isCommittedLogLb γ.node.cl l ∗ ⌜n ≤ l.length⌝)

instance rnWalHanded_persistent (γ : RNNames GF) (n : Nat) : Persistent (rnWalHanded (GF := GF) γ n) := by
  unfold rnWalHanded; infer_instance

/-- `rnWalHanded` at the server's log `L` handed at a `Save` (its lower bound, committed). -/
theorem rnWalHanded_intro (γ : RNNames GF) (L : List EntryModel) :
    walCommitLb (GF := GF) γ.wal (srvLE γ.srv L) -∗ isCommittedLogLb γ.node.cl (srvLE γ.srv L) -∗
      rnWalHanded γ (γ.pre ++ L).length := by
  iintro #Hlb #Hc
  iunfold rnWalHanded
  iexists srvLE γ.srv L
  iframe Hlb Hc
  ipureintro
  simp [srvLE, RNNames.srv]

/-- (D43 M3) What the apply thread's `notifyc` receive deposits: the view after the batch, if it
went along. -/
def rnApR (γ : RNNames GF) (F ce : List EntryModel) : IProp GF :=
  if rnHands γ ce then rnView γ (F ++ ce) else iprop(True)

/-- (D43 M3) What goes along with the batch: the view after `F` and the committed log handed out
through the batch (`dlvLb`), if `rnHands`. -/
def rnApGive (γ : RNNames GF) (F ce : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  if rnHands γ ce then
    iprop(rnView γ F ∗ deliveredLogLb γ.nl γ.node.cl srvClusterN (srvLE γ.srv (F ++ ce)))
  else iprop(True)

/-- (R2d'a A6, 2026-11-06) No conf entry in a range of a log, in its prefix. -/
theorem NoConfChangeIn_prefix (l r : List LogEntry) (lo : Nat)
    (h : NoConfChangeIn (l ++ r) lo (l ++ r).length) : NoConfChangeIn l lo l.length := by
  intro k e hk1 hk2 he
  exact h k e hk1 (by simp; omega) (by rw [List.getElem?_append_left hk2]; exact he)

/-- (R2d'a A6, 2026-11-06) **At a first start (`a0 = []`) the view, what goes along with a batch and
what comes back are today's texts** (until A6: `rnCfgAt γ L := srvCfgView γ.srv γ.nl γ.pre L`,
`rnApR`'s and `rnApGive`'s over it). (A10 item 5, Q28 (i)) The view's part takes the start term
`t0 = 0` too (`rnRestartOk`'s first disjunct; S1: and `commit0 = snap0 = 0`). -/
theorem rnView_first (γ : RNNames GF) (h : γ.a0 = []) :
    (γ.t0 = W64 0 ∧ γ.commit0 = 0 ∧ γ.snap0 = 0 →
      ∀ L, rnCfgAt (GF := GF) γ L ⊣⊢ srvCfgView γ.srv γ.nl γ.pre L) ∧
    (∀ F ce, rnApR (GF := GF) γ F ce =
      if rnHands γ ce then srvCfgView γ.srv γ.nl γ.pre (F ++ ce) else iprop(True)) ∧
    (∀ F ce, rnApGive (GF := GF) γ F ce =
      letI := srvStor (GF := GF) γ.node
      if rnHands γ ce then
        iprop(srvCfgView γ.srv γ.nl γ.pre F ∗
          deliveredLogLb γ.nl γ.node.cl srvClusterN (srvLE γ.srv (F ++ ce)))
      else iprop(True)) := by
  have hv : ∀ L, rnView (GF := GF) γ L = srvCfgView γ.srv γ.nl γ.pre L := by
    intro L
    unfold rnView rnGhost srvCfgView
    rw [h]
    simp
  refine ⟨fun _ L => ?_, fun F ce => ?_, fun F ce => ?_⟩
  · unfold rnCfgAt
    rw [hv L]
    exact .rfl
  · unfold rnApR; rw [hv]
  · unfold rnApGive; rw [hv]

/-- An ordinary Ready that sends a same-term snapshot during recovery can
read the durable image's last entry term from this particular immutable slice. -/
def rnReplayState (γ : RNNames GF) (view : GoSlice) (n : Nat) : IProp GF :=
  iprop(∃ runs : List replayTermRun, view ↦*□ runs ∗ ⌜replayPending runs γ.a0 n⌝)

instance rnReplayState_persistent (γ : RNNames GF) (view : GoSlice) (n : Nat) :
    Persistent (rnReplayState (GF := GF) γ view n) := by
  unfold rnReplayState; infer_instance

/-- The replay terms an apply job carries, for a `MsgSnap` this node sent at the job's raft term `rt`
in the replay window (`n < |a0|`): they cover the consistent index with `a0`'s last term.
(2026-11-24, the lifetime law: `notes/etcd-dist-d6.md`, T4 round 5) Only for a `MsgSnap` of this run
of the node: one a `Ready` handed out (`rnMessageSource`, which `rnSnapMsg` carries), so that its term
is past the restart's (`rnReplayJob_lifetime`). An earlier run's `MsgSnap`s, whose `sentMsg` persists,
are not covered: for them the claim is false (a leader at `rt` that crashed before saving what it
committed restarts at `t0 = rt`). -/
def rnReplayJob (γ : RNNames GF) (terms : GoSlice) (rt : w64) (n : Nat) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(□ ∀ (sm : MsgSt) (ci : w64),
    ⌜sm.msg.Type' = MsgSnap ∧ sm.msg.Term' = rt ∧ n < γ.a0.length ∧ uint.Z ci = γ.a0.length⌝ -∗
    sentMsg γ.node.cl srvClusterN γ.id sm -∗
    ∀ ml : Loc, rnMessageSource γ ⟨ml, sm⟩ -∗
    -- (2026-11-24, option (a)) an update: raft's `raftState_leadAgree` is one
    |={⊤}=> ∃ (runs : List replayTermRun) (r : replayTermRun), terms ↦*□ runs ∗
      ⌜replayRunCovers runs ci = true ∧ replayRunAt runs ci = some r ∧
        r.term' = (γ.a0.getLast?.map EntryModel.term).getD (W64 0)⌝)

instance rnReplayJob_persistent (γ : RNNames GF) (terms : GoSlice) (rt : w64) (n : Nat) :
    Persistent (rnReplayJob γ terms rt n) := by
  unfold rnReplayJob; infer_instance

/-- The `i`th payload on `applyc` with committed entries: the log `F` forwarded before it (`cum[i]`)
and the batch `ce` it extends it with (`cum[i + 1] = F ++ ce`, committed), no snapshot, and its two
channels; and (2026-10-14, unit C2a) the committed index at least the batch's last index
(`committedLast`: `updateCommittedIndex` raised it before the send); and (D22 S-b) its raft term
(`rnRtOk`). (D22 J6a: `rnApP`'s first case; until then `rnApP` itself.) -/
def rnApN (E : RNEnv GF) (γ : RNNames GF) (i : Int) (ap : toApply) : IProp GF :=
  iprop(∃ (F ce : List EntryModel) (ceL : List Loc),
    monoListIdxOwn γ.cum i.toNat F ∗ monoListIdxOwn γ.cum (i.toNat + 1) (F ++ ce) ∗
    ap.entries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (F ++ ce) ∗ ⌜ap.snapshot' = null⌝ ∗
    -- (D43 M3, 2026-10-25) `notifyc`, with the receive's right: the receive deposits `rnApR`
    (∃ γnc : NotifyNames, isNotify γnc ap.notifyc' (rnApR γ F ce) ∗ notifyRcv γnc) ∗
    -- (D43 M3) a batch the driver's view goes with (`rnHands`): the view after `F`
    rnApGive γ F ce ∗
    -- (D19i part 1) closed once `Advance` returned: (2026-10-30, the repair) the node's applied
    -- index past the batch (until then the storage's floor)
    rnAdvChan ap.raftAdvancedC'
      (letI := srvStor (GF := GF) γ.node
       iprop(nodeAppliedLb γ.node.cl γ.key (γ.pre ++ F ++ ce).length ∗ nodeCommitLb γ.node.cl γ.key (γ.pre ++ F ++ ce).length ∗
        -- (2026-10-30, the repair) the batch's entries frozen in the storage (`CreateSnapshot`'s)
        srvFrozenRange γ.γs ((γ.pre ++ F).length + 1) ((γ.pre ++ F ++ ce).length + 1) ∗
        -- (2026-10-31, the snapshot track: #11's S3) with their terms
        srvFrozenTerms γ.γs (γ.pre.length + 1) (F ++ ce) ∗
        -- (2026-11-03, R2b-1 stage 5) the batch's log handed at its WAL `Save` (`Advance` is after
        -- it), which the apply thread's own snapshot takes
        rnWalHanded γ (γ.pre ++ F ++ ce).length)) ∗
    committedLast E.γr ce ∗
    -- (D22 S-b) the raft term it carries; (D22l) whose witness's commit index bounds the batch
    rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length ∗
    rnReplayJob γ ap.replayTerms' ap.raftTerm' (rnLogOf γ (F ++ ce)).length)

/-- (D22 J6a, 2026-10-26) **The `i`th payload on `applyc` with a snapshot** (raft's snapshot `Ready`,
`readySnapData`; `raftNode.start` hands the apply thread its own clone of `rd.Snapshot`): the log
`F` forwarded before it (`cum[i]`) and the committed log up to the snapshot `A'` it jumps to
(`cum[i + 1] = A'`, extending `F` strictly, `pre ++ A'` the snapshot's index long), no committed
entries, the clone read-only (`ownSnapM … DFrac.discard`), `E.C A'`, the snapshot local to the node
(`nodeSnapLocal`, the node API's `readySnap`, 2026-11-01: for the server, saved in the member's
snapshot directory), the snapshot's id the last
of the committed log (raft's `Ready` states it, `readySnapData`: so its term is the term of the
entry at its index), its two channels, the committed index at least the snapshot's
(`updateCommittedIndex`), its raft term. Only outside raft's no-snapshot mode. `notifyc` is as in
the entries' case (`isNotify … True`, one receive); the snapshot branch's two sends and the apply
thread's two receives need a two-receive variant (J6b, J8a). -/
def rnApSnap (E : RNEnv GF) (γ : RNNames GF) (i : Int) (ap : toApply) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  -- (2026-10-30, the repair: snapshots allowed, until then `False`)
  iprop(∃ (F A' : List EntryModel) (sv : SnapshotM),
    monoListIdxOwn γ.cum i.toNat F ∗ monoListIdxOwn γ.cum (i.toNat + 1) A' ∗
    ⌜F.length < A'.length ∧ (γ.pre ++ A').length = uint.nat sv.Metadata'.Index' ∧
      -- (2026-11-01, J8a-5) the index's bound (raft's `readySnap`)
      uint.Z sv.Metadata'.Index' < 2 ^ 61 ∧
      -- (J8b, 2026-11-01) past the boot log (`rnReadySnap_bootLen`, open)
      (γ.node.boot.length : Int) ≤ uint.Z sv.Metadata'.Index' ∧
      -- (R2d'a task 4) above the restart point (A8's bound, from the receive: `rnBusySP`)
      (γ.a0 = [] ∨ γ.a0.length < (γ.pre ++ A').length) ∧
      -- (auth-lease S4, 2026-11-16) outside the cluster's no-snapshot mode (`readySnap_mode`)
      ¬ clusterNoSnap γ.node.cl⌝ ∗
    -- (2026-11-01, J8a-5) no committed entries with a snapshot (raft's `readySnap`: `ce = []`)
    ap.entries' ↦*□ ([] : List Loc) ∗
    ownSnapM ap.snapshot' DFrac.discard sv ∗
    snapshotCert γ.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
    -- (2026-11-01, J8a) the snapshot's index in the member's snapshot directory (raft's `readySnap`)
    nodeSnapLocal γ.node.cl γ.id sv.Metadata'.Index' ∗ □ E.C A' ∗
    -- `notifyc`: two sends for a snapshot batch (raft.go:274,302), two receives (`applySnapshot`'s,
    -- `applyAll`'s): the two-receive notify (`NotifyC2.lean`; 2026-10-31, #3); (sweep repairs 1,
    -- W2) the first send after the snapshot's `SaveSnap` (raft.go:257), with the WAL's records
    -- starting at or above the snapshot's index (what `applySnapshot`'s `Release` takes)
    (∃ γnc : NotifyNames, isNotify2 γnc ap.notifyc'
      iprop(∃ (j : Nat) (m : SnapshotMetadataM), walSnapRec γ.wal.h j m ∗ ⌜m.Index' = sv.Metadata'.Index'⌝)
      iprop(True) ∗ notifyRcvN γnc 0) ∗
    -- closed once `Advance` returned: the node's applied index at the snapshot
    rnAdvChan ap.raftAdvancedC' iprop(nodeAppliedLb γ.node.cl γ.key (γ.pre ++ A').length ∗ nodeCommitLb γ.node.cl γ.key (γ.pre ++ A').length ∗
      -- the snapshot's dummy entry frozen, everything below compacted (`ApplySnapshot`'s)
      srvFrozenAt γ.γs (γ.pre ++ A').length ∗ srvFrozenBelow γ.γs (γ.pre ++ A').length ∗
      -- (2026-11-03, R2b-1 stage 5) the snapshot's log handed at its WAL `Save`
      rnWalHanded γ (γ.pre ++ A').length) ∗
    committedAtLeast E.γr sv.Metadata'.Index' ∗
    rnRtOk γ ap.raftTerm' (rnLogOf γ A').length)

/-- **The `i`th payload on `applyc`** (D22 J6a, 2026-10-26: with or without a snapshot): committed
entries (`rnApN`) or a snapshot (`rnApSnap`, only outside raft's no-snapshot mode). -/
def rnApP (E : RNEnv GF) (γ : RNNames GF) (i : Int) (ap : toApply) : IProp GF :=
  iprop(rnApN E γ i ap ∨ rnApSnap E γ i ap)

/-- (D22 S-b) A batch's raft term, read off its payload (for `applyAll`'s merged snapshot); (D22l)
with the batch's log `F ++ ce` (`cum`'s element `i + 1`) within its witness's commit index. -/
theorem rnApP_rtOk (E : RNEnv GF) (γ : RNNames GF) (i : Int) (ap : toApply) :
    ⊢ rnApP E γ i ap -∗ rnApP E γ i ap ∗ ∃ (F ce : List EntryModel),
      monoListIdxOwn γ.cum (i.toNat + 1) (F ++ ce) ∗
      rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length := by
  iintro H
  iunfold rnApP at H
  icases H with (H | H)
  · iunfold rnApN at H
    icases H with ⟨%F, %ce, %ceL, #H1, #H2, #H3, #H4, #H5, %H6, H7, HG, #H8, #H9, #Hrt, #Hjob⟩
    isplitl [H7 HG]
    · iunfold rnApP
      ileft
      iunfold rnApN
      iexists F, ce, ceL
      iframe H1 H2 H3 H4 H5 H7 HG H8 H9 Hrt Hjob
      ipureintro; exact H6
    iexists F, ce
    iframe H2 Hrt
  · -- (D22 J6a) a snapshot (2026-10-30, the repair: allowed): `cum[i+1] = A'`, as `A' ++ []`
    iunfold rnApSnap at H
    icases H with ⟨%F, %A', %sv, #H1, #H2, %H3, #Hes, #H4, #H5, #H5l, #H6, H7, #H8, #H9, #Hrt⟩
    isplitl [H7]
    · iunfold rnApP
      iright
      iunfold rnApSnap
      iexists F, A', sv
      iframe H1 H2 Hes H4 H5 H5l H6 H7 H8 H9 Hrt
      ipureintro; exact H3
    iexists A', []
    rw [List.append_nil]
    iframe H2 Hrt

/-- `applyc` (persistent): an SPSC channel of `rnApP` payloads, never closed (its close's
resource is `False`: 2026-10-13, the request path's unit 4c, `True` until then; the loop never
closes it, and the apply side's receive needs that it is not closed). -/
def isRNApplyc (E : RNEnv GF) (γ : RNNames GF) (c : Loc) : IProp GF :=
  isSspsc γ.ap c (V := toApply) (rnApP E γ) (fun _ => iprop(False))

instance isRNApplyc_persistent (E : RNEnv GF) (γ : RNNames GF) (c : Loc) :
    Persistent (isRNApplyc E γ c) := by
  unfold isRNApplyc; infer_instance

/-- (2026-11-03, R2b-1 stage 4) **The loop's view of the WAL's durability** at `v` (its half of the
view, `rnDurInv`'s the other), with its "not stopped" token (`ν.ok`). -/
def rnWalView (γ : RNNames GF) (v : WalView) : IProp GF :=
  rnWalViewK γ.walK (v, none)

/-- The loop's ghost state: the driver at the node's delivered log `L`, `applyc`'s producer
half, and `cum`'s authority, one element per payload sent after the first, ending at `L`; and
(2026-10-30, the repair) the loop's half of the node's running token. -/
def rnLoopTokP (γ : RNNames GF) (L : List EntryModel) (p : HardStateM) (b : Bool) : IProp GF :=
  iprop(∃ (sent : List toApply) (cums : List (List EntryModel)) (S : RaftState) (r : StateType),
    rnDrv γ L p S r ∗
    -- (2026-11-03, R2b-3: *enter* at the `Save`) the loop's `islead` (`b`) true only at role leader,
    -- for a leader's early `Send` (`readyLeaderMsgs`)
    ⌜b = true → r = StateLeader⌝ ∗
    -- (2026-11-03, R2b-1 stage 4) the loop's view of the WAL's durability, at the driver's state
    rnWalView γ ⟨S, p, none, srvLE γ.srv L⟩ ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗ sspscProducer γ.ap sent ∗ monoListAuthOwn γ.cum 1 cums ∗
    ⌜cums.length = sent.length + 1 ∧ cums.getLast? = some L⌝ ∗
    -- (2026-10-27) the log's indices consecutive from the start's (`rn_ready_recv`'s premise)
    ⌜∃ ai : w64, uint.Z ai = γ.pre.length ∧ srvIdxOkW ai L⌝ ∗
    -- (2026-10-31, the snapshot track: #11's S3) the log handed out so far frozen, with its terms
    srvFrozenTerms γ.γs (γ.pre.length + 1) L ∗
    -- (S1, Q31, 2026-11-11) raft's commit never below the restart point's (`RestartNode` starts the
    -- driver at the restored hard state, whose commit is `commit0`; `readyRest_commit_mono` keeps
    -- it); `0` at a first start. Crash-proof: it needs no graceful fact.
    ⌜γ.commit0 ≤ uint.nat p.Commit'⌝ ∗
    -- (S1) the log handed out committed (`deliveredLogLb_committed`), for the stop's image
    isCommittedLogLb γ.node.cl (srvLE γ.srv L))

/-- The loop's ghost state at some `prevHardSt` (D22l: `rnLoopTokP`, the loop keeps it tied to
the raft term it records). -/
def rnLoopTok (γ : RNNames GF) (L : List EntryModel) : IProp GF :=
  -- (keepfix (c) step 1, T1, 2026-11-28) `prevHardSt` at the loop's start has the restored term `t0`
  -- (`RestartNode`'s storage hard state; a first start's empty one, term `0`)
  iprop(⌜γ.snap0 ≤ (rnLogOf γ L).length⌝ ∗ ∃ p : HardStateM, rnLoopTokP γ L p false ∗ ⌜p.Term' = γ.t0⌝)

/-- The apply side's ghost state: `applyc`'s consumer half, and `cum` at the number of
payloads received, the log `A` forwarded so far. -/
def rnApplyTok (γ : RNNames GF) (A : List EntryModel) : IProp GF :=
  iprop(∃ rcv : List toApply, sspscConsumer γ.ap rcv ∗ monoListIdxOwn γ.cum rcv.length A)

/-- `msgSnapC`: a channel of messages raft may send, each a `MsgSnap` (D19p, 2026-10-18: so that
a server whose raft sends none knows the channel never delivers); (D22 S-l sender, 2026-10-22)
each owned with its protocol facts (`rnSnapMsg`), for `applyAll`'s merge, which writes it. -/
def isRNMsgSnapC (γ : RNNames GF) (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Loc) (rnSnapMsg γ))

instance isRNMsgSnapC_persistent (γ : RNNames GF) (c : Loc) :
    Persistent (isRNMsgSnapC (GF := GF) γ c) := by
  unfold isRNMsgSnapC; infer_instance

/-- `readStateC`: a channel of read states, each answering the registrations of its request id
(the read loop's `isReadStateC`; 2026-10-13, the request path's unit 4b: no content until then). -/
def isRNReadStateC (E : RNEnv GF) (c : Loc) : IProp GF := isReadStateC c E.γr.raft E.RQ

instance isRNReadStateC_persistent (E : RNEnv GF) (c : Loc) : Persistent (isRNReadStateC E c) := by
  unfold isRNReadStateC; infer_instance

/-! ## The stop's escrow (2026-11-03, R2b-3b) -/

/-- The namespace of the raft loop's stop escrow. -/
def rnStopN : Namespace := nroot.@"rnStop"

/-- **The WAL `w`, closed, its files holding the records `σ`** (R2b-3b; until then an opaque draft):
`Close`'s files (`walFiles`) in the WAL's directory, its metadata naming the member `γ.id`. What
the stop image's `srvFiles` is made of (R2b-3c). (out_size C3, MAJ-2) Sized (`walFiles … true`): the
records the durability invariant holds are (`walAsViewed`), and `Close` keeps the flag. -/
def rnWalClosedW (γ : RNNames GF) (σ : StorContents) : IProp GF :=
  iprop(∃ cid : w64, walFiles γ.wal.h.toWalA γ.id cid σ true)

/-- **The wrapper `r`'s WAL, closed, its records `σ`** (`raftNode.stop.spec`'s): `rnWalClosedW` at
the WAL of `r`'s storage. -/
def rnWalClosed (γ : RNNames GF) (r : Loc) (σ : StorContents) : IProp GF :=
  iprop(∃ st : GoInterface, rnStorageAddr r ↦□ st ∗ rnWalClosedW γ σ)

/-- **What the stopped loop leaves** (R2b-3b), at the WAL `w`: the node's id vacant (`node.Stop`'s),
its durable state `S`, the WAL closed with records `σ` holding it, between whose base and commit the
log `L` handed to the apply thread ends; `applyc`'s producer token at the count `sent` of payloads,
`cum` at it `L` (the stop's caller, the apply side, with its consumer token, learns that it
received every payload, `sspsc_sync`, so that its log is `L`: review M2). -/
def rnStopImage (γ : RNNames GF) : IProp GF :=
  iprop((∃ x, nodeVacantA γ.node.cl γ.id x) ∗
    ∃ (S : RaftState) (σ : StorContents) (sent : List toApply) (L : List EntryModel),
      raftState γ.node.cl γ.id S ∗ rnWalClosedW γ σ ∗
      sspscProducer γ.ap sent ∗ monoListIdxOwn γ.cum sent.length L ∗
      ⌜StorageHolds S σ ∧ σ.b ≤ (γ.pre ++ L).length ∧ (γ.pre ++ L).length ≤ σ.commit ∧
        -- (S1) the restart point's backend log at or below the records' commit (`rnRestartOk_a0_le`)
        γ.a0.length ≤ σ.commit⌝ ∗
      -- (R2d, Q14 (a), DRAFT) the records' snapshot certificate (`rnDur_take`'s)
      walSnapCert γ.node.cl σ ∗
      -- (S1, r2db §4.1) a committed log reaching the records' base, which their durable state's log
      -- agrees with (`rnDur_take`'s `DurAgrees`): for the restart's `wal.restartOk` (S2)
      (∃ l', isCommittedLogLb γ.node.cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝))

/-- **`done`'s close announces the stop's escrow** (persistent, R2b-3b; until then `True`): the stop
image, or the claim (`rnStopClaim`) once its holder took the image. `onStop` allocates it with the
image as it closes `done`. -/
def rnDoneEsc (γ : RNNames GF) : IProp GF :=
  inv rnStopN iprop(rnStopImage γ ∨ token γ.sc)

instance rnDoneEsc_persistent (γ : RNNames GF) : Persistent (rnDoneEsc (GF := GF) γ) := by
  unfold rnDoneEsc; infer_instance

/-- **The claim on the raft loop's stop escrow** (R2b-3b; until then an opaque draft): `newRaftNode`
allocates it, and `raftNode.stop`'s spec takes it, to take the image out of
`done`'s escrow. -/
def rnStopClaim (γ : RNNames GF) : IProp GF := token γ.sc

/-! ## The wrapper -/

/-- **The raft wrapper `r`** (persistent): its fields, read-only once started (`start`'s
comment), with their components; `latestTickTs` under `tickMu`; and (2026-10-16, stage R7b) the
discharge's facts of `E` (`rnEnvOk`), the run's premise on the `Ready`s (`rnLogFits`), the read
states' bridge, the `MemoryStorage`'s registration (the `raftStorage` field is the names'). -/
def isRaftNode (E : RNEnv GF) (γ : RNNames GF) (r : Loc) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  iprop(∃ (lg mu ms td tk : Loc) (n st tr : GoInterface) (idr : GoFunc)
      (hb : time.Duration) (msc apc rsc stc dnc : GoChan),
    "#Henv" ∷ rnEnvOk E γ ∗ "#Hfits" ∷ rnLogFits γ ∗ "#Hrsb" ∷ rnReadStateBridge E γ ∗
    -- (restart S3 item 7, review 5, 2026-11-11) the restart data (until then in the loop's view,
    -- `rnCfgAt`, where `raftNode.stop` could not reach it)
    "#Hrok" ∷ rnRestartOk γ ∗
    "#Hreg" ∷ memStorReg γ.ms γ.γs ∗
    "#Hlg" ∷ rnLgAddr r ↦□ lg ∗ "#Hlgnn" ∷ zapLoggerOk lg ∗
    "#Hmu" ∷ rnTickMuAddr r ↦□ mu ∗ "#Hmug" ∷ sync.isRWMutexGuard mu (rnTickInv r) ∗
    "#Hn" ∷ rnNodeAddr r ↦□ n ∗ "#Hni" ∷ isRaftNodeIfc E γ n ∗
    "#Hidr" ∷ rnIsIDRemovedAddr r ↦□ idr ∗ "#Hidri" ∷ isRNIDRemoved idr ∗
    "#Hms" ∷ rnRaftStorageAddr r ↦□ ms ∗ "%Hmsγ" ∷ ⌜ms = γ.ms⌝ ∗ "#Hmsi" ∷ isRNMemStor γ ms ∗
    "#Hst" ∷ rnStorageAddr r ↦□ st ∗ "#Hsti" ∷ isWalStorage st γ.wal.h γ.ss ∗
    -- (2026-11-03, R2b-1 stage 3c) the WAL's durability invariant
    "#Hdur" ∷ rnDurInvK γ.node γ.id γ.walK γ.wal.h ∗
    -- (P5) the node's arm (`StartNode`'s/`RestartNode`'s), which a pending batch's record names (`rnPendRec`)
    "#Harm" ∷ (letI := srvStor (GF := GF) γ.node; nodeArm γ.nl γ.node.cl γ.walK.x) ∗
    -- (P5, T6 placeholder) the snapshot directory's durability (`WalNamesK.sd`) the trivial one, until T6
    -- links it to the snapshotter's `snapDurable`
    "%Hsd" ∷ ⌜γ.walK.sd = fun _ => iprop(True)⌝ ∗
    "#Hhb" ∷ rnHeartbeatAddr r ↦□ hb ∗
    "#Htr" ∷ rnTransportAddr r ↦□ tr ∗ "#Htri" ∷ isRNTransport E tr ∗
    "#Hmsc" ∷ rnMsgSnapCAddr r ↦□ msc ∗
    "#Hmsci" ∷ isRNMsgSnapC γ msc ∗
    "#Hapc" ∷ rnApplycAddr r ↦□ apc ∗ "#Hapci" ∷ isRNApplyc E γ apc ∗
    "#Hrsc" ∷ rnReadStateCAddr r ↦□ rsc ∗
    "#Hrsci" ∷ isRNReadStateC E rsc ∗
    "#Htk" ∷ rnTickerAddr r ↦□ tk ∗ "#Htki" ∷ isRNTicker tk ∗
    "#Htd" ∷ rnTdAddr r ↦□ td ∗ "#Htdi" ∷ isRNTimeoutDetector td ∗
    "#Hstc" ∷ rnStoppedAddr r ↦□ stc ∗ "#Hstci" ∷ rnStopBag E γ stc ∗
    "#Hdnc" ∷ rnDoneAddr r ↦□ dnc ∗
    -- (2026-11-03, R2b-3b) its close announces the stop's escrow (until then `True`)
    "#Hdnci" ∷ ownBroadcastChan dnc γ.done (rnDoneEsc γ) .Unknown ∗
    -- (srvloops2, 2026-11-21) the node is raft's (`rnNodeIface`), and `tickMu`'s pool of reader slots
    "%Hnif" ∷ ⌜n = interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.node.ty) #γ.nl.loc⌝ ∗
    "#Htp" ∷ rnTickPool r mu)

instance isRaftNode_persistent (E : RNEnv GF) (γ : RNNames GF) (r : Loc) :
    Persistent (isRaftNode E γ r) where
  persistent := by
    unfold isRaftNode
    iintro H
    iNamed H
    imodintro
    iexists lg, mu, ms, td, tk, n, st, tr, idr, hb, msc, apc, rsc, stc, dnc
    simp only [named]
    iframe #
    isplitr
    · ipureintro; exact Hmsγ
    isplitr
    · ipureintro; exact Hsd
    ipureintro; exact Hnif

/-- The right to close `done` (the loop's: its deferred `onStop`). -/
def rnDoneTok (γ : RNNames GF) (r : Loc) : IProp GF :=
  iprop(∃ (dnc : GoChan) (st : GoInterface), rnDoneAddr r ↦□ dnc ∗ rnStorageAddr r ↦□ st ∗
    ownBroadcastChan dnc γ.done (rnDoneEsc γ) .Pending)

/-- The worker takes the bootstrapped replay terms out of the config before its first Ready. -/
def rnWorkerStartTok (γ : RNNames GF) (r : Loc) : IProp GF :=
  iprop(rnDoneTok γ r ∗ ∃ terms : GoSlice, rnReplayTermsAddr r ↦ terms ∗ rnReplayState γ terms γ.snap0)


/-- (2026-11-03, R2b-3b; review M2) **The stop's caller takes the image out of `done`'s escrow**: with
the claim and the apply side's token at the log `A` it was handed, the image the loop left, its
handed log `A` (the producer's and the consumer's tokens agree, `applyc` being synchronous,
`sspsc_sync`: every payload sent was received). -/
theorem rn_esc_take (E : RNEnv GF) (γ : RNNames GF) (c : Loc) (A : List EntryModel) :
    ⊢ isRNApplyc E γ c -∗ rnDoneEsc γ -∗ rnStopClaim γ -∗ rnApplyTok γ A -∗ £ 1 -∗ £ 1 ={⊤}=∗
      (∃ x, nodeVacantA γ.node.cl γ.id x) ∗ ∃ (S : RaftState) (σ : StorContents),
        raftState γ.node.cl γ.id S ∗ rnWalClosedW γ σ ∗
        ⌜StorageHolds S σ ∧ σ.b ≤ (γ.pre ++ A).length ∧ (γ.pre ++ A).length ≤ σ.commit ∧
          γ.a0.length ≤ σ.commit⌝ ∗
        walSnapCert γ.node.cl σ ∗
        (∃ l', isCommittedLogLb γ.node.cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝) := by
  iintro #Hapc #Hesc Hsc Happ Hlc1 Hlc2
  iunfold rnStopClaim at Hsc
  iunfold rnDoneEsc at Hesc
  iinv Hesc with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑rnStopN) $$ Hlc1 Hi with Hi
  icases Hi with (Himg | Htok)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hsc Htok
  imod Hclose $$ [Hsc] with -
  · inext; iright; iexact Hsc
  iunfold rnStopImage at Himg
  icases Himg with ⟨Hvac, %S, %σ, %sent, %L, HrS, Hcl, Hprod, #Hidx, %Hord, #Hσc, #Hl'⟩
  iunfold rnApplyTok at Happ
  icases Happ with ⟨%rcv, Hcons, #HidxA⟩
  iunfold isRNApplyc at Hapc
  imod sspsc_sync γ.ap c (rnApP E γ) _ sent rcv $$ Hapc Hlc2 Hprod Hcons with ⟨%Heq, -, -⟩
  subst Heq
  ihave %HLA := mono_list_idx_agree γ.cum sent.length L A $$ Hidx HidxA
  subst HLA
  imodintro
  iframe Hvac
  iexists S, σ
  iframe HrS Hcl Hσc Hl'
  ipureintro; exact Hord

end defs

end EtcdGrove
end Perennial
