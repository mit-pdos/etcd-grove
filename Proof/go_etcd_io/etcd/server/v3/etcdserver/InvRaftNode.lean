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
public import Perennial.Golang.Theory.Chan.Idioms.Idioms
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopChan
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Perennial.Ghost.MonoList
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NotifyC2
public import Proof.go_etcd_io.raft.v3.MemstorageApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi

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
  countableOfLeftInverse (fun a : toApply => (a.entries', a.snapshot', a.notifyc', a.raftAdvancedC', a.raftTerm'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

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
structure RNNames [GooseExts] where
  node : SrvRaft
  id : w64
  nl : Loc
  pre : List EntryModel
  ms : Loc
  γs : MemStorNames
  ap : SpscNames
  cum : GName
  done : ChanNames
  key : GName
  -- (2026-11-03, R2b-1 stage 3c) the WAL's durability (the slot convention's field group)
  wal : WalNames
  -- (2026-11-03, R2b-3b) the claim on the loop's stop escrow (`rnStopClaim`, `rnDoneEsc`)
  sc : GName
  -- (R2d'a A6, 2026-11-06; DRAFT) the restart point's backend log `A₀` (the backend's ghost applied
  -- log through its consistent index, `bootstrap.go:255-273` at the etcd pin `673da07c8`), over
  -- which the driver's view is stated (`rnCfgAt`); `[]` at a first start (`newRaftNode`'s)
  a0 : List EntryModel
  -- (R2d'a A10 item 5, 2026-11-06; DRAFT, approved by 82) the restart point's restored `HardState`
  -- term `T₀` (`RestartNode`'s, R2d'b), which bounds this incarnation's `MsgSnap`s from below
  -- (`rnSnapMsg`) and `Hwpend`'s guard; `W64 0` at a first start (`newRaftNode`'s)
  t0 : w64

/-- The `MemoryStorage` registry's name: the cluster's (2026-10-27; until then a field). -/
abbrev RNNames.reg [GooseExts] (γ : RNNames) : GName := γ.node.reg

/-- The cluster's names at the wrapper's start log (for `srvLE`/`srvCfgView`, which read only the
cluster and the start log). -/
abbrev RNNames.srv [GooseExts] (γ : RNNames) : ServerRaftNames := ⟨γ.node, γ.pre, W64 0⟩

/-- Raft's full committed log holding the server's `L` after its start (`srvLogOf`, by the
wrapper's names). -/
def rnLogOf [GooseExts] (γ : RNNames) (L : List EntryModel) : List EntryM :=
  (γ.pre ++ L).map EntryModel.toM

theorem rnLogOf_append [GooseExts] (γ : RNNames) (A B : List EntryModel) :
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

/-- (D22 S-l sender, 2026-10-22; 2026-10-30, the repair: snapshots allowed, until then `False`)
**A `MsgSnap` raft handed out, owned**: the message, whole (a `Ready`'s: `readyDq`, a
`MsgSnap` being no response; 2026-10-31, S1: until then at some fraction, which
`createMergedSnapshotMessage`'s write of `m.Snapshot` cannot take), of type `MsgSnap`, sent by the
node, with its credits (`sentMsg_snapshot` gives its snapshot's certificate): what
`processMessages` hands to `msgSnapC` and `applyAll`'s merge rewrites. (R2d'a A10 item 5, approved by
82; DRAFT) Its term is above this incarnation's start term `γ.t0` (`W64 0` at a first start, where
`sentMsg_shape`'s nonzero term gives it; at a restart `rnRestartOk`'s `rnSnapTermAbove`, R2d'b's
target): `applyAll`'s merged-send case at a batch term `rt ≤ t0` reads it (`winNoMergedSendR`). -/
def rnSnapMsg (γ : RNNames) (m : Loc) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ st : MsgSt, msgOwn m (DFrac.own 1) st ∗
    ⌜st.msg.Type' = MsgSnap ∧ uint.Z γ.t0 < uint.Z st.msg.Term'⌝ ∗
    sentMsg γ.node.cl srvClusterN γ.id st ∗ msgCredits γ.node.cl srvClusterN st)

/-- (D22 S-l sender) **A message of a `Ready`, as the server receives it**: any but a `MsgSnap`
read-only with `E.M` (`rnMsgOk`'s, with its type not `MsgSnap`), a `MsgSnap` owned
(`rnSnapMsg`). `processMessages` turns the first into `rnMsgOk` for the transport and hands the
second to `msgSnapC`. -/
def rnMsgR (E : RNEnv GF) (γ : RNNames) (m : Loc) : IProp GF :=
  iprop((∃ (to : w64) (ty : w32), msgAt m to ty ∗ ⌜ty ≠ MsgSnap⌝ ∗ E.M m) ∨ rnSnapMsg γ m)

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

/-- The right to append `es` to the `MemoryStorage` (from a `Ready`): raft's storage API's
`appendRight` at the storage (the range from the batch's first index owned), and the indices'
bound. -/
def rnAppendRight (γ : RNNames) (es : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(appendRight (memStorIface γ.ms) (es.map EntryModel.toM) ∗ ⌜rnFits es ∧ rnConsec es⌝)

/-- The receipt of the append of `es` (for `Advance`): raft's storage API's `appendReceipt`, with
nothing frozen (2026-10-30, the repair: `appendReceipt`'s frozen prefix `a` is `[]`, which
`Advance`'s `advReceipt` admits; the server makes no snapshot, D2(i), so needs no frozen entry). -/
def rnAppendReceipt (γ : RNNames) (es : List EntryModel) : IProp GF :=
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
def rnAdvReceipt (γ : RNNames) (d ce es : List EntryModel) : IProp GF :=
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
def rnCeFrozen (γ : RNNames) (d ce es : List EntryModel) : IProp GF :=
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

instance rnCeFrozen_persistent (γ : RNNames) (d ce es : List EntryModel) :
    Persistent (rnCeFrozen (GF := GF) γ d ce es) := by
  unfold rnCeFrozen; infer_instance

/-- A `Ready`'s `SoftState`: nil, or read-only fields (raft's `softStateRO`). -/
def softStateAt (p : Loc) : IProp GF := softStateRO p

instance softStateAt_persistent (p : Loc) : Persistent (softStateAt (GF := GF) p) := by
  unfold softStateAt; infer_instance

/-- (R2d'a A10 item 5, Q29 (d)) **A `Ready`'s `MsgSnap`s within this incarnation's terms** (pure): a
first start's (`t0 = 0`: `sentMsg_shape` bounds them), or each above `t0` (`rnSnapTermAbove`). -/
def rnSnapTermOk (γ : RNNames) (ms : List QMsg) : Prop :=
  γ.t0 = W64 0 ∨ ∀ q ∈ ms, q.st.msg.Type' = MsgSnap → uint.Z γ.t0 < uint.Z q.st.msg.Term'

theorem rnSnapTermOk_cons {γ : RNNames} {q : QMsg} {ms : List QMsg} (h : rnSnapTermOk γ (q :: ms)) :
    rnSnapTermOk γ ms :=
  h.imp_right fun h' q' hq' => h' q' (List.mem_cons_of_mem _ hq')

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **A `Ready`'s messages `ms`, not yet sent**: each
owned as the node API hands it out, with its credits, and at role leader (`r' = StateLeader`, the
role after the `Ready`) their sends (raft's `readyLeaderMsgs`: a leader may send before the batch is
durable). Otherwise *enter* gives the sends (`readyMsgs`), after the WAL `Save`. -/
def rnRawMsgs (γ : RNNames) (ms : List QMsg) (r' : StateType) : IProp GF :=
  iprop(([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ msgCredits γ.node.cl srvClusterN q.st) ∗
    (⌜r' = StateLeader⌝ -∗ readyMsgs γ.node.cl srvClusterN γ.id ms) ∗
    -- (R2d'a A10 item 5, Q29 (d)) a first start (`t0 = 0`), or every `MsgSnap` above `t0`
    -- (`rnSnapTermAbove`, at the receive)
    ⌜rnSnapTermOk γ ms⌝)

/-- What a `Ready` gives the driver, after the committed log `d` handed out before it: the
committed entries `ce` to apply next (`C (d ++ ce)`), the entries `es` to append with the right
to, the messages, each one raft may send; a `SoftState`, a `HardState` (`p'` the last non-empty
one, `p` before); the read states, each answering the registrations of its request id
(`srvReadStateOk E.RQ`); no snapshot. (2026-10-27: raft's commit witness of the hard state,
`hsWit`, is gone: the snapshot sender that needed it is unreachable, `rnSnapMsg`.) -/
def rnReadyData (E : RNEnv GF) (γ : RNNames) (rd : Ready) (d ce es : List EntryModel)
    (p p' : HardStateM) (S S' : RaftState) (r r' : StateType) (ms : List QMsg) : IProp GF :=
  iprop(∃ (ceL esL msL : List Loc) (hs : HardStateModel),
    rd.CommittedEntries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (d ++ ce) ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗ rnAppendRight γ es ∗
    -- (2026-11-03, R2b-3: *enter* at the `Save`) the messages as the node API hands them out, not yet
    -- sent (`rnRawMsgs`: *enter* sends them, or at role leader `readyLeaderMsgs`)
    rd.Messages' ↦*□ msL ∗ ⌜msL = ms.map QMsg.loc⌝ ∗ rnRawMsgs γ ms r' ∗
    -- the soft state, and the role after it (`r'`, from the driver's `r`)
    (∃ ss, softStateIs rd.SoftState' ss ∗ ⌜r' = roleAfter r ss⌝) ∗ hardStateAt rd.HardState' hs ∗
    ⌜p' = phsNext p hs.toM⌝ ∗
    (∃ rsL : List ReadState, rd.ReadStates' ↦*□ rsL ∗ [∗list] rs ∈ rsL, srvReadStateOk E.γr.raft E.RQ rs) ∗
    ⌜rd.Snapshot' = null⌝ ∗
    -- (2026-10-30, the repair, stage P) the committed entries as the node API freezes them
    rnCeFrozen γ d ce es ∗
    -- (2026-11-03, R2b-1 stage 4) the batch a WAL `Save` step, from the loop's view at the driver's
    -- durable state `S` to the entered one `S'` (`walSaveStep_ready`)
    ⌜WalSaveStep ⟨S, p, none, srvLE γ.srv d⟩ ⟨S', p', none, srvLE γ.srv (d ++ ce)⟩ hs.toM
      (es.map EntryModel.toM)⌝)

/-- (R2d'a A6, 2026-11-06; DRAFT) **The ghost log after the committed log `L`**: the log handed out,
`pre ++ L`, completed by the restart point's backend log past it (`γ.a0`; ViewR's `ghostOf ⟨|pre|,
a0⟩ (pre ++ L)`). At a first start (`a0 = []`) it is `pre ++ L`. -/
def rnGhost (γ : RNNames) (L : List EntryModel) : List EntryModel :=
  (γ.pre ++ L) ++ γ.a0.drop (γ.pre ++ L).length

/-- (R2d'a A6, 2026-11-06; DRAFT) **The driver's view of the configuration after the committed log
`L`, over the ghost log** (ViewR's `rnCfgAtR`): the view after `rnGhost γ L`, every conf entry of it
applied (`srvCfgView`, `InvCfgView.lean`). At a restart, raft's view is at the backend's consistent
index (`RestartNode`, `bootstrap.go:597`; `notes/restart-plan.md`, R2d' finding 1), past Go's log
while the replay window is open; at a first start it is the view after `pre ++ L`. -/
def rnView (γ : RNNames) (L : List EntryModel) : IProp GF :=
  srvCfgView γ.srv γ.nl [] (rnGhost γ L)

/-- (R2d'a A10 item 3, Q27 (i), 2026-11-06; DRAFT, approved by the user; a restart-only premise)
**The WAL's stored commit is never below the restart point's backend log**: whatever durable state
`S` the node has, records `σ` holding it (`StorageHolds S σ`) have a stored commit at least `|a0|`.
True of Go: the restored WAL's commit is at least the backend's consistent index
(`bootstrapRestartContract`), `σ.commit ≥ S.wcommit` (`StorageHolds`), and the commit raft writes
only grows. Raft's API does not say so; **R2d'b's target** (`RestartNode` supplies it, from the
restored records). At a first start it is not needed (`rnRestartOk`'s first disjunct, `a0 = []`).
The stop's image takes the bound (`rnRestartOk_commit`). -/
def rnWalCommitAbove (γ : RNNames) : IProp GF :=
  iprop(□ ∀ (S : RaftState) (σ : StorContents), raftState γ.node.cl γ.id S -∗ ⌜StorageHolds S σ⌝ -∗
    raftState γ.node.cl γ.id S ∗ ⌜γ.a0.length ≤ σ.commit⌝)

instance rnWalCommitAbove_persistent (γ : RNNames) :
    Persistent (rnWalCommitAbove (GF := GF) γ) := by
  unfold rnWalCommitAbove; infer_instance

/-- The driver's state at the committed log `L` handed out and the hard state `p`, idle, at the
storage's key `γ.key`, the durable state `S` and the role `r` (2026-11-01, durability layer 4). -/
def rnDrvSt (γ : RNNames) (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType) :
    NodeDriverState :=
  ⟨memStorIface γ.ms, srvLE γ.srv L, p, none, γ.key, S, r⟩

/-- (R2d'a A6, 2026-11-06; DRAFT; R2d'a's A8, a restart-only assumption; A10 item 5, approved by 82:
strict, until then `≤`; task 4, 2026-11-06, approved by 82 as a hub decision: anchored at the
receive's `readyRest`, until then on the busy `nodeDriver`, which the raft loop holds only after it
has sent the payload on `applyc`) **No snapshot at or below the restart point**: every snapshot
`Ready` this incarnation's node hands its driver (`readyRest` at the driver's idle state `rnDrvSt γ …`,
this incarnation's storage and key, as `rnSnapTermAbove`) is strictly above the backend's log `a0`
(`|a0| < snapIdx`). Why `<` is true of Go: **raft's commit at restart is `≥ |a0|`, and `restore`
rejects a snapshot at or below committed** (raft v3.7.0 `raft.go:1861`; the fork `565c2bd`'s
`raft.go:1877`). The restored `HardState`'s commit is `σ.commit ≥ |a0|` (`wal.stopImage`'s
`i ≤ σ.commit`, the fact `rnWalCommitAbove` states), and raft's commit only grows, so every snapshot
raft installs has `snapIdx > |a0|`. A snapshot that matches a local entry's term is not installed
either: raft fast-forwards its commit and returns (v3.7.0 `raft.go:1912-1918`, the fork's
`raft.go:1928-1934`). The snapshot a
`Ready` carries is the one the driver installs (etcd at `673da07c8`).

Raft's API does not say so (`notes/restart-plan.md`, R2d' finding 2, H5 (b): "a snapshot's index
is above the receiver's commit"). R2d'b's obligation for it: `RestartNode` supplies raft's commit at
the start `≥ |a0|` (the same restart fact as `rnWalCommitAbove`), from which this follows with H5
(b). R2e's closed theorem must not carry it. -/
def rnWinInstallAbove (γ : RNNames) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(□ ∀ (rd : Ready) (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType)
      (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (Lo : Option SnapLoan)
      (ms : List QMsg) (ss : Option (w64 × StateType)),
    readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss -∗
      readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss ∗
      ⌜∀ l, Lo = some l → γ.a0.length < uint.nat l.snap.Metadata'.Index'⌝)

instance rnWinInstallAbove_persistent (γ : RNNames) :
    Persistent (rnWinInstallAbove (GF := GF) γ) := by
  unfold rnWinInstallAbove; infer_instance

/-- (R2d'a A10 item 5, Q29 (d), 2026-11-06; DRAFT, approved by 82 as hub owner; a restart-only
premise) **This incarnation's `MsgSnap`s are above its start term**: every `MsgSnap` in a `Ready`
this incarnation's node hands its driver (`readyRest` at the driver's idle state `rnDrvSt γ …`,
which names this incarnation's storage `γ.ms` and key `γ.key`; the receive consumes the
`nodeDriver γ.nl`, so the anchor is the driver state the receive was at) has a term above `γ.t0`,
the restored `HardState` term. True of Go (raft v3.7.0 at `565c2bd`, etcd at `673da07c8`): only a
leader sends `MsgSnap`, at its term, and a restarted node leads only after `becomeCandidate` at
`T₀ + 1` or later (`raft.go:902-911`); a `MsgSnap` queued at `T` by a leader that then steps down
still has `T ≥ T₀ + 1`. The main session's probe: 0 of ~7,300 `MsgSnap`s per run from restarted
incarnations had `Term ≤` the restored term (`notes/restart-plan.md`, "Probe follow-ups"). Raft's
API does not say so: `reset(term)` does not clear `r.msgs`, so the per-instance law needs a
raft-struct invariant and a `StartNode` post change. **R2d'b's target** (5-8 d, est.). At a first
start it is not needed: `rnRestartOk`'s first disjunct has `t0 = 0`, and `sentMsg_shape` gives a
`MsgSnap` a nonzero term (`rnMsgOk_of_api`). R2e's closed theorem must not carry it. -/
def rnSnapTermAbove (γ : RNNames) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(□ ∀ (rd : Ready) (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType)
      (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (Lo : Option SnapLoan)
      (ms : List QMsg) (ss : Option (w64 × StateType)),
    readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss -∗
      readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss ∗
      ⌜∀ q ∈ ms, q.st.msg.Type' = MsgSnap → uint.Z γ.t0 < uint.Z q.st.msg.Term'⌝)

instance rnSnapTermAbove_persistent (γ : RNNames) :
    Persistent (rnSnapTermAbove (GF := GF) γ) := by
  unfold rnSnapTermAbove; infer_instance

/-- (R2d'a A6, 2026-11-06; DRAFT) **The restart data** (persistent): a first start (`a0 = []`, and
(A10 item 5, Q28 (i)) the start term `t0 = 0`), or a restart before the WAL's first snapshot
(`pre = []`, R2d'a's `σ.b = 0` restriction) whose backend log `a0` is committed (`srvRLogLb`), with
R2d'a's A8 (`rnWinInstallAbove`), (A10 item 3, Q27 (i)) the WAL's stored commit above `a0`
(`rnWalCommitAbove`) and (A10 item 5, Q29 (d)) this incarnation's `MsgSnap`s above `t0`
(`rnSnapTermAbove`). -/
def rnRestartOk (γ : RNNames) : IProp GF :=
  iprop(⌜γ.a0 = [] ∧ γ.t0 = W64 0⌝ ∨
    (⌜γ.pre = []⌝ ∗ srvRLogLb γ.srv γ.a0 ∗ rnWinInstallAbove γ ∗ rnWalCommitAbove γ ∗
      rnSnapTermAbove γ))

instance rnRestartOk_persistent (γ : RNNames) : Persistent (rnRestartOk (GF := GF) γ) := by
  unfold rnRestartOk; infer_instance

/-- (R2d'a A10 item 3, Q27 (i)) **The stop's records are at or above the restart point**: from the
restart data, records `σ` holding the node's durable state have a stored commit at least `|a0|`;
at a first start (`a0 = []`) trivially. -/
theorem rnRestartOk_commit (γ : RNNames) (S : RaftState) (σ : StorContents)
    (h : StorageHolds S σ) :
    rnRestartOk (GF := GF) γ ⊢ raftState γ.node.cl γ.id S -∗
      raftState γ.node.cl γ.id S ∗ ⌜γ.a0.length ≤ σ.commit⌝ := by
  unfold rnRestartOk
  iintro #Hr HS
  icases Hr with (%Ha | ⟨-, -, -, #Hc, -⟩)
  · iframe HS; ipureintro; rw [Ha.1]; exact Nat.zero_le _
  · iunfold rnWalCommitAbove at Hc
    iapply Hc $$ HS %h

/-- (R2d'a A10 item 5, Q29 (d)) **A `Ready`'s `MsgSnap`s within this incarnation's terms**: from the
restart data, at a first start `t0 = 0`, at a restart `rnSnapTermAbove`. -/
theorem rnRestartOk_snapTerm (γ : RNNames) (L : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) (rd : Ready) (ce : List LogEntry) (es : List EntryM) (h : HardStateM)
    (Lo : Option SnapLoan) (ms : List QMsg) (ss : Option (w64 × StateType)) :
    rnRestartOk (GF := GF) γ ⊢
      (letI := srvStor (GF := GF) γ.node;
        readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss) -∗
      (letI := srvStor (GF := GF) γ.node;
        readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss) ∗
      ⌜rnSnapTermOk γ ms⌝ := by
  letI := srvStor (GF := GF) γ.node
  unfold rnRestartOk
  iintro #Hr H
  icases Hr with (%Ha | ⟨-, -, -, -, #Hs⟩)
  · iframe H; ipureintro; exact Or.inl Ha.2
  · iunfold rnSnapTermAbove at Hs
    ihave ⟨H, %hb⟩ := Hs $$ %rd %L %p %S %r %ce %es %h %Lo %ms %ss H
    iframe H; ipureintro; exact Or.inr hb

/-- (R2d'a task 4) **A `Ready`'s snapshot above the restart point**: from the restart data, at a
first start `a0 = []`, at a restart `rnWinInstallAbove`. -/
theorem rnRestartOk_winAbove (γ : RNNames) (L : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) (rd : Ready) (ce : List LogEntry) (es : List EntryM) (h : HardStateM)
    (Lo : Option SnapLoan) (ms : List QMsg) (ss : Option (w64 × StateType)) :
    rnRestartOk (GF := GF) γ ⊢
      (letI := srvStor (GF := GF) γ.node;
        readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss) -∗
      (letI := srvStor (GF := GF) γ.node;
        readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p S r) ce es h Lo ms ss) ∗
      ⌜γ.a0 = [] ∨ ∀ l, Lo = some l → γ.a0.length < uint.nat l.snap.Metadata'.Index'⌝ := by
  letI := srvStor (GF := GF) γ.node
  unfold rnRestartOk
  iintro #Hr H
  icases Hr with (%Ha | ⟨-, -, #Hw, -, -⟩)
  · iframe H; ipureintro; exact Or.inl Ha.1
  · iunfold rnWinInstallAbove at Hw
    ihave ⟨H, %hb⟩ := Hw $$ %rd %L %p %S %r %ce %es %h %Lo %ms %ss H
    iframe H; ipureintro; exact Or.inr hb

/-- **The driver's view of the configuration after the committed log `L`** (D43 M3; 2026-10-30,
the repair: raft's one mode, the old dynamic one's; R2d'a A6, 2026-11-06, DRAFT: over the ghost
log, `rnView`, with the restart data `rnRestartOk`; until then the view after `pre ++ L`, which it
is at a first start, `rnView_first`): every conf entry of the ghost log applied (`srvCfgView`,
`InvCfgView.lean`); until the repair nothing in a static cluster. -/
def rnCfgAt (γ : RNNames) (L : List EntryModel) : IProp GF :=
  iprop(rnView γ L ∗ rnRestartOk γ)

/-- (R2d'a A10 item 5) The view carries the restart data (persistent). -/
theorem rnCfgAt_restartOk (γ : RNNames) (L : List EntryModel) :
    rnCfgAt (GF := GF) γ L ⊢ rnCfgAt γ L ∗ rnRestartOk γ := by
  unfold rnCfgAt
  iintro ⟨Hv, #Hr⟩
  iframe Hv Hr

/-- The driver, idle, handed the committed log `L` so far: the node API's `nodeDriver` at
`pre ++ L` (2026-10-27; until then raft's), with the driver's view of the configuration after `L`
(`rnCfgAt`); `p` the hard state of the last `Ready` with a non-empty one. (2026-11-01, durability
layer 4) Beside it the node's durable state, the driver's (`raftState`): the server enters each
`Ready`'s batch after its WAL `Save` (2026-11-03, R2b-3: until then at once, at the receive), from it
and the loop's half of the running token. (R2b-3) The role `r` named: the loop keeps `islead` tied
to it (`rnLoopTokP`). (2026-11-03, R2b-1 stage 3c) The durable state `S` a parameter: the loop's
view of the WAL's durability (`rnLoopTokP`) is at it, and `Advance` keeps it. -/
def rnDrv (γ : RNNames) (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType) :
    IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(nodeDriver γ.nl γ.node.cl srvClusterN (rnDrvSt γ L p S r) ∗
    raftState γ.node.cl γ.id S ∗ rnCfgAt γ L)

/-- (2026-10-31, the snapshot track: #11's S4) The committed log handed out through `L`, at the
node's storage: the storage contract's `DL` (`nodeCommitLb`) at its length (`CreateSnapshot`'s
`J.DL`). (2026-11-02, the lean merge: from the idle driver, whose key names the storage,
`nodeDriver_nodeCommitLb`; until then from `isNode` and `deliveredLogLb`, the open `storDL`.) -/
theorem rn_storDL (γ : RNNames) (L : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) :
    rnDrv (GF := GF) γ L p S r ⊢ rnDrv γ L p S r ∗ nodeCommitLb γ.node.cl γ.key (γ.pre ++ L).length := by
  letI := srvStor (GF := GF) γ.node
  iintro Hd
  iunfold rnDrv at Hd
  icases Hd with ⟨Hd, HrS, Hcf⟩
  ihave ⟨Hd, #Hc⟩ := nodeDriver_nodeCommitLb γ.nl γ.node.cl srvClusterN _ $$ Hd
  isplitl [Hd HrS Hcf]
  · iunfold rnDrv; iframe
  · iExactEq Hc
    simp [rnDrvSt, srvLE]

/-- The driver with a `Ready` in hand, handed the committed log `d ++ ce`, to append `es`
before `Advance`: the node API's `nodeDriver` busy, without the view; (2026-11-01, durability
layer 4) the batch entered: the node's durable state the driver's. -/
def rnBusyN (γ : RNNames) (d ce es : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(nodeDriver γ.nl γ.node.cl srvClusterN
    ⟨memStorIface γ.ms, srvLE γ.srv (d ++ ce), p, some (es.map EntryModel.toM, none), γ.key, S, r⟩ ∗
    raftState γ.node.cl γ.id S)

/-- The driver with a `Ready` in hand (`rnBusyN`) and its view after the log before it, `d`. -/
def rnBusy (γ : RNNames) (d ce es : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) : IProp GF :=
  iprop(rnBusyN γ d ce es p S r ∗ rnCfgAt γ d)

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **A received `Ready`'s batch, not yet entered**: the
node's durable state `S` before it (`raftState`) and raft's *enter* (`readyEnter`), from the idle
driver's state at `d`, `p`, `S`, role `r`, to the busy one `st'`, sending the messages `ms`. The loop
fires it after the WAL `Save` (`rn_enter`); a stop before leaves the durable state at `S`, which
the WAL's records hold. -/
def rnPendEnter (γ : RNNames) (d : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType)
    (st' : NodeDriverState) (ms : List QMsg) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(raftState γ.node.cl γ.id S ∗
    readyEnter γ.nl γ.node.cl srvClusterN γ.id
      ⟨memStorIface γ.ms, srvLE γ.srv d, p, none, γ.key, S, r⟩ st' ms)

/-- (2026-11-03, R2b-3) The busy state after a `Ready` without a snapshot. -/
abbrev rnBusyStN (γ : RNNames) (d ce es : List EntryModel) (p : HardStateM) (S : RaftState)
    (r : StateType) : NodeDriverState :=
  ⟨memStorIface γ.ms, srvLE γ.srv (d ++ ce), p, some (es.map EntryModel.toM, none), γ.key, S, r⟩

/-- (2026-11-03, R2b-3) **The driver with a `Ready` received, not yet entered** (`rnBusy` before
*enter*): the pending *enter* to the busy state, and the view after the log before it. -/
def rnBusyP (γ : RNNames) (d ce es : List EntryModel) (p p' : HardStateM) (S S' : RaftState)
    (r r' : StateType) (ms : List QMsg) : IProp GF :=
  iprop(rnPendEnter γ d p S r (rnBusyStN γ d ce es p' S' r') ms ∗ rnCfgAt γ d)

/-- (2026-11-03, R2b-3) **Firing *enter* after the `Save`**: the busy driver at the entered durable
state (`rnBusyN`), with the messages' sends. -/
theorem rn_enter (γ : RNNames) (d ce es : List EntryModel) (p p' : HardStateM) (S S' : RaftState)
    (r r' : StateType) (ms : List QMsg) :
    ⊢ rnPendEnter (GF := GF) γ d p S r (rnBusyStN γ d ce es p' S' r') ms -∗
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ={⊤}=∗
      rnBusyN γ d ce es p' S' r' ∗
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      readyMsgs γ.node.cl srvClusterN γ.id ms := by
  letI := srvStor (GF := GF) γ.node
  iintro Hb Hrun
  iunfold rnPendEnter at Hb
  icases Hb with ⟨HrS, Hent⟩
  iunfold readyEnter at Hent
  imod Hent $$ %⊤ %((1 : Qp).half) %(by simp) [HrS Hrun] with ⟨HrS, Hrun, Hdrv, #Hsent⟩
  · isplitl [HrS]
    · iexact HrS
    · iexact Hrun
  imodintro
  iframe Hrun Hsent
  iunfold rnBusyN
  iframe Hdrv HrS

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
def rnEnvOk (E : RNEnv GF) (γ : RNNames) : IProp GF :=
  iprop(⌜E.T = iprop(True)⌝ ∗
    ⌜E.γr.raft.raft = γ.node ∧ E.γr.raft.pre = γ.pre ∧
      uint.Z E.γr.raft.ai0 = γ.pre.length⌝ ∗
    ⌜γ.node.rule = srvRule E.γr.kv.c0 γ.node.boot⌝ ∗
    srvRaftLogInv E.γr.raft ∗
    □ (∀ (m : Loc) (st : MsgSt), msgOwn m DFrac.discard st ∗
        sentMsg γ.node.cl srvClusterN γ.id st ∗ msgCredits γ.node.cl srvClusterN st ∗ ⌜st.msg.Type' ≠ MsgSnap⌝ -∗
        E.M m) ∗
    □ (∀ L : List EntryModel, srvRLogLb E.γr.raft L -∗
        ⌜uint.Z E.γr.raft.ai0 + 1 + L.length < 2 ^ 64⌝ ={⊤}=∗ □ E.C L) ∗
    □ (∀ L : List EntryModel, E.C L -∗ srvRLogLb E.γr.raft L ∗ ⌜srvIdxOk E.γr.raft.ai0 L⌝) ∗
    ⌜E.RQ = srvRQ E.γr.raft⌝)

instance rnEnvOk_persistent (E : RNEnv GF) (γ : RNNames) : Persistent (rnEnvOk E γ) := by
  unfold rnEnvOk; infer_instance

/-- (R2d, Q17 F6) **The environment's raft log invariant, at the node's cluster.** -/
theorem rnEnvOk_logInv (E : RNEnv GF) (γ : RNNames) :
    rnEnvOk (GF := GF) E γ ⊢ ⌜E.γr.raft.raft = γ.node⌝ ∗ srvRaftLogInv E.γr.raft := by
  iintro #H
  iunfold rnEnvOk at H
  icases H with ⟨-, %Hn, -, #HRL, -⟩
  iframe HRL
  ipureintro; exact Hn.1

/-- **The run's premise on raft's `Ready`s** (pure, D19b stage 5): the time-receipt bound past
the bootstrap log. (2026-10-27: the node API bounds a `Ready`'s indices itself, `readyRest`; kept
for the wrapper's statements.) -/
def rnLogFits (γ : RNNames) : IProp GF :=
  iprop(⌜receiptBound GF + γ.node.boot.length ≤ 2 ^ 61⌝)

instance rnLogFits_persistent (γ : RNNames) : Persistent (rnLogFits (GF := GF) γ) := by
  unfold rnLogFits; infer_instance

/-- **The read states' bridge** (persistent): a `ReadState` the node API hands out (`readStateOk`
of its context `c` at its index, its cells read-only) answers the server's registrations
(`srvReadStateOk`). `srvReadStateOk_of_raft` proves it from `rnEnvOk`. -/
def rnReadStateBridge (E : RNEnv GF) (γ : RNNames) : IProp GF :=
  iprop(□ ∀ (c : List w8) (i : w64) (v : ReadState),
    readStateOk γ.node.cl srvClusterN c i -∗ ⌜v.Index' = i⌝ -∗ v.RequestCtx' ↦*□ c -∗
      srvReadStateOk E.γr.raft E.RQ v)

instance rnReadStateBridge_persistent (E : RNEnv GF) (γ : RNNames) :
    Persistent (rnReadStateBridge E γ) := by
  unfold rnReadStateBridge; infer_instance


/-- **A read state, in the server's terms** (what `rnReadStateBridge` states, under `rnEnvOk`):
its context was committed (`srvCtxDeposited`), and for each registration of it, the read state's
index is past the registration's bound (`readStateOk_after`) and the read's witness holds at it
(`srvReadWit_of`). -/
theorem srvReadStateOk_of_raft [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames)
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
theorem rnReadStateBridge_of_raft [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames) :
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
def rnReadySnap (E : RNEnv GF) (γ : RNNames) (rd : Ready) (d es A' : List EntryModel)
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
        hs.toM (es.map EntryModel.toM)⌝ ∗
    -- (2026-10-31, #3) no committed entries
    rd.CommittedEntries' ↦*□ ceL ∗ entriesAt ceL [] ∗
    ⌜srvLE γ.srv A' = strip l.dlv ∧ d.length < A'.length ∧
      (∀ e0, (es.map EntryModel.toM).head? = some e0 →
        uint.Z e0.Index' + ((es.map EntryModel.toM).length : Int) ≤ 2 ^ 61) ∧
      Option.map EntryModel.term A'.getLast? = some l.snap.Metadata'.Term'⌝ ∗ □ E.C A' ∗
    snapshotValid γ.node.cl l.snap ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗
    rd.Messages' ↦*□ msL ∗ ⌜msL = ms.map QMsg.loc⌝ ∗ rnRawMsgs γ ms r' ∗
    (∃ ss, softStateIs rd.SoftState' ss ∗ ⌜r' = roleAfter r ss⌝) ∗
    hardStateAt rd.HardState' hs ∗ ⌜p' = phsNext p hs.toM⌝ ∗
    (∃ rsL : List ReadState, rd.ReadStates' ↦*□ rsL ∗
      [∗list] rs ∈ rsL, srvReadStateOk E.γr.raft E.RQ rs))

/-- (J8b, 2026-11-01) **A snapshot `Ready` is past the boot log**: its index is at least the boot
log's length. True of raft: a node restores a snapshot only above its committed index
(`raft.restore`), which is at least the boot log's length, so every snapshot a `Ready` hands out is
past it. From raft's `readySnap_bootLen` and the server's cluster at its bootstrap log
(`srvClusterOk`, through `rnEnvOk`). What `applyAll.specSnap` takes (`|boot| ≤ i`, through
`rnApSnap`). -/
theorem rnReadySnap_bootLen (E : RNEnv GF) (γ : RNNames) (rd : Ready) (d es A' : List EntryModel)
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
def rnBusyS (γ : RNNames) (d A' es : List EntryModel) (p : HardStateM) (l : SnapLoan)
    (S : RaftState) (r : StateType) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop((nodeDriver γ.nl γ.node.cl srvClusterN
      ⟨memStorIface γ.ms, srvLE γ.srv A', p, some (es.map EntryModel.toM, some l), γ.key, S, r⟩ ∗
      raftState γ.node.cl γ.id S) ∗
    rnCfgAt γ d ∗
    ⌜srvLE γ.srv A' = strip l.dlv ∧ srvLE γ.srv d <+: strip l.dlv ∧
      l.dlv.length = uint.nat l.snap.Metadata'.Index' ∧
      0 < uint.Z l.snap.Metadata'.Index' ∧ uint.Z l.snap.Metadata'.Index' < 2 ^ 61 ∧
      -- (R2d'a task 4) the snapshot above the restart point (A8, `rnWinInstallAbove`)
      (γ.a0 = [] ∨ γ.a0.length < uint.nat l.snap.Metadata'.Index')⌝)

/-- (2026-11-03, R2b-3) The busy state after a snapshot `Ready`. -/
abbrev rnBusyStS (γ : RNNames) (A' es : List EntryModel) (p : HardStateM) (l : SnapLoan) (S : RaftState)
    (r : StateType) : NodeDriverState :=
  ⟨memStorIface γ.ms, srvLE γ.srv A', p, some (es.map EntryModel.toM, some l), γ.key, S, r⟩

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **The driver with a snapshot `Ready` received, not yet
entered** (`rnBusyS` before *enter*). -/
def rnBusySP (γ : RNNames) (d A' es : List EntryModel) (p p' : HardStateM) (l : SnapLoan)
    (S S' : RaftState) (r r' : StateType) (ms : List QMsg) : IProp GF :=
  iprop(rnPendEnter γ d p S r (rnBusyStS γ A' es p' l S' r') ms ∗
    rnCfgAt γ d ∗
    ⌜srvLE γ.srv A' = strip l.dlv ∧ srvLE γ.srv d <+: strip l.dlv ∧
      l.dlv.length = uint.nat l.snap.Metadata'.Index' ∧
      0 < uint.Z l.snap.Metadata'.Index' ∧ uint.Z l.snap.Metadata'.Index' < 2 ^ 61 ∧
      -- (R2d'a task 4) the snapshot above the restart point (A8, `rnWinInstallAbove`)
      (γ.a0 = [] ∨ γ.a0.length < uint.nat l.snap.Metadata'.Index')⌝)

/-- (2026-11-03, R2b-3) **Firing *enter* after a snapshot `Ready`'s `Save`** (`rn_enter`'s): the busy
driver and the entered durable state (`rnBusyS`'s first part). -/
theorem rn_enterS (γ : RNNames) (d A' es : List EntryModel) (p p' : HardStateM) (l : SnapLoan)
    (S S' : RaftState) (r r' : StateType) (ms : List QMsg) :
    ⊢ rnPendEnter (GF := GF) γ d p S r (rnBusyStS γ A' es p' l S' r') ms -∗
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ={⊤}=∗
      (letI := srvStor (GF := GF) γ.node; iprop(nodeDriver γ.nl γ.node.cl srvClusterN
        ⟨memStorIface γ.ms, srvLE γ.srv A', p', some (es.map EntryModel.toM, some l), γ.key, S', r'⟩ ∗
        raftState γ.node.cl γ.id S')) ∗
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      readyMsgs γ.node.cl srvClusterN γ.id ms := by
  letI := srvStor (GF := GF) γ.node
  iintro Hb Hrun
  iunfold rnPendEnter at Hb
  icases Hb with ⟨HrS, Hent⟩
  iunfold readyEnter at Hent
  imod Hent $$ %⊤ %((1 : Qp).half) %(by simp) [HrS Hrun] with ⟨HrS, Hrun, Hdrv, #Hsent⟩
  · isplitl [HrS]
    · iexact HrS
    · iexact Hrun
  imodintro
  iframe Hrun Hsent HrS
  iexact Hdrv

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
def isRaftNodeIfc (E : RNEnv GF) (γ : RNNames) (n : GoInterface) : IProp GF :=
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
      {{ RET #(); nodeStopped γ.nl γ.node.cl srvClusterN ∗ nodeVacant γ.node.cl γ.id }}) ∗
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

instance isRaftNodeIfc_persistent (E : RNEnv GF) (γ : RNNames) (n : GoInterface) :
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
server's clusters send no `MsgSnap`, `srv_sentMsg_notSnap`). (R2d'a A10 item 5, Q29 (d)) A `MsgSnap`'s
term above `γ.t0` combines the two cases of `rnSnapTermOk`: at a first start (`t0 = 0`) its nonzero
term (`sentMsg_shape`), at a restart the receive's bound (`rnSnapTermAbove`). -/
theorem rnMsgOk_of_api [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames) :
    ∀ ms : List QMsg, rnSnapTermOk γ ms →
      ⊢ □ (∀ (m : Loc) (st : MsgSt), msgOwn m DFrac.discard st ∗
          sentMsg γ.node.cl srvClusterN γ.id st ∗ msgCredits γ.node.cl srvClusterN st ∗ ⌜st.msg.Type' ≠ MsgSnap⌝ -∗
          E.M m) -∗ srvClusterOk E.γr.raft -∗ ⌜E.γr.raft.raft = γ.node⌝ -∗
        ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗
          sentMsg γ.node.cl srvClusterN γ.id q.st ∗ msgCredits γ.node.cl srvClusterN q.st)
          ={⊤}=∗
        [∗list] m ∈ ms.map QMsg.loc, rnMsgR E γ m
  | [], _ => by
    iintro #HM - - -
    imodintro
    simp only [List.map_nil]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | q :: ms, hb => by
    iintro #HM #Hcl %Hraft H
    icases (BigSepL.bigSepL_cons (Φ := fun _ (q : QMsg) => iprop(msgOwn (GF := GF) q.loc
      (readyDq q.st) q.st ∗ sentMsg γ.node.cl srvClusterN γ.id q.st ∗
      msgCredits γ.node.cl srvClusterN q.st))).1 $$ H with ⟨⟨Hm, #Hsm, Hc⟩, Hrest⟩
    imod rnMsgOk_of_api E γ ms (rnSnapTermOk_cons hb) $$ HM Hcl %Hraft Hrest with Hrest
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
      ihave %Hsh := (letI := srvStor (GF := GF) γ.node;
        sentMsg_shape (GF := GF) γ.node.cl srvClusterN γ.id q.st) $$ Hsm
      iframe Hm Hsm Hc
      ipureintro
      refine ⟨hsn, ?_⟩
      rcases hb with h0 | hb
      · -- a first start: `t0 = 0` and the `MsgSnap`'s term nonzero
        have hne : q.st.msg.Term' ≠ W64 0 := Hsh.1.2.2.2.1 (by
          rw [hsn]; exact msgSnap_not_termless)
        rw [h0]
        have : uint.Z q.st.msg.Term' ≠ 0 := fun h => hne (by word)
        word
      · exact hb q List.mem_cons_self hsn
    imod msgOwn_persist_fupd q.loc _ q.st ⊤ $$ Hm with #Hm
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := fun _ m => rnMsgR (GF := GF) E γ m)).2
    iframe Hrest
    iunfold rnMsgR
    ileft
    iexists q.st.msg.To', q.st.msg.Type'
    isplitr
    · iunfold msgAt
      iexists q.st
      iframe Hm
      ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · ipureintro; exact hsn
    iapply HM $$ %q.loc %q.st
    iframe Hm Hsm Hc
    ipureintro; exact hsn

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **A `Ready`'s messages, sent**: the raw messages
(`rnRawMsgs`) with their sends (`readyMsgs`, from *enter*) are each one the transport takes
(`rnMsgR`). -/
theorem rnRawMsgs_sent [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames)
    (ms : List QMsg) (r' : StateType) :
    ⊢ rnEnvOk E γ -∗ rnRawMsgs γ ms r' -∗
      (letI := srvStor (GF := GF) γ.node; readyMsgs γ.node.cl srvClusterN γ.id ms) ={⊤}=∗
      [∗list] m ∈ ms.map QMsg.loc, rnMsgR E γ m := by
  letI := srvStor (GF := GF) γ.node
  iintro #Henv Hraw #Hsent
  iunfold rnRawMsgs at Hraw
  icases Hraw with ⟨Hmo, -, %Hb⟩
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, -, #Hinv, #HM, -⟩
  ihave #Hcl : srvClusterOk E.γr.raft $$ []
  · iunfold srvRaftLogInv at Hinv; icases Hinv with ⟨-, #H, -⟩; iexact H
  ihave Hmo := readyMsgs_sent γ.node.cl srvClusterN γ.id ms $$ [$Hmo $Hsent]
  iapply rnMsgOk_of_api E γ ms Hb $$ HM Hcl %Hn.1 Hmo

/-- (2026-11-03, R2b-3) **A leader's messages, sent before *enter*** (raft's `readyLeaderMsgs`). -/
theorem rnRawMsgs_leader [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames)
    (ms : List QMsg) (r' : StateType) (hr : r' = StateLeader) :
    ⊢ rnEnvOk E γ -∗ rnRawMsgs γ ms r' ={⊤}=∗ [∗list] m ∈ ms.map QMsg.loc, rnMsgR E γ m := by
  letI := srvStor (GF := GF) γ.node
  iintro #Henv Hraw
  iunfold rnRawMsgs at Hraw
  icases Hraw with ⟨Hmo, Hl, %Hb⟩
  ihave #Hsent := Hl $$ %hr
  iapply rnRawMsgs_sent E γ ms r' $$ Henv [Hmo] Hsent
  iunfold rnRawMsgs
  iframe Hmo
  isplitr
  · iintro -
    iexact Hsent
  ipureintro; exact Hb

/-- The read states a `Ready` hands out, each answering the server's registrations (through
the bridge). -/
theorem rnReadStates_of_api (E : RNEnv GF) (γ : RNNames) :
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

/-- (2026-11-03, R2b-3: *enter* at the `Save`) **The hard state `p` committed** (persistent), for a
batch of the log `pre ++ L`: empty, or its commit index committed at its term and at least
`|pre ++ L|` (what raft's receive gives without *enter*; `rnRtOk_of_hsC` makes the loop's
`rnRtOk` of it). -/
def rnHsC (γ : RNNames) (p : HardStateM) (L : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(⌜p = hsZero⌝ ∨ committedAtTerm γ.node.cl srvClusterN p.Term' p.Commit' ∗
    ⌜((srvLE γ.srv L).length : Int) ≤ uint.Z p.Commit'⌝)

instance rnHsC_persistent (γ : RNNames) (p : HardStateM) (L : List EntryModel) :
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
theorem rn_ready_recv [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames)
    (L : List EntryModel) (p : HardStateM) (S : RaftState) (r : StateType) (rd : Ready)
    (HLi : srvIdxOkW E.γr.raft.ai0 L) :
    letI := srvStor (GF := GF) γ.node
    rnEnvOk E γ -∗ rnReadStateBridge E γ -∗ rnCfgAt γ L -∗
      raftState γ.node.cl γ.id S -∗
      readyGot γ.nl γ.node.cl srvClusterN γ.id (rnDrvSt γ L p S r) rd ={⊤}=∗
      ((∃ ce' es' p' S' r' ms, rnReadyData E γ rd L ce' es' p p' S S' r r' ms ∗
        rnBusyP γ L ce' es' p p' S S' r r' ms ∗
        deliveredLogLb γ.nl γ.node.cl srvClusterN (srvLE γ.srv (L ++ ce')) ∗
        rnHsC γ p' (L ++ ce') ∗
        ⌜srvIdxOkW E.γr.raft.ai0 (L ++ ce')⌝) ∨
      -- (2026-10-30, the repair: snapshots allowed) a `Ready` with a snapshot
      (∃ (es' A' : List EntryModel) (p' : HardStateM) (l : SnapLoan) (S' : RaftState)
          (r' : StateType) (ms : List QMsg),
        rnReadySnap E γ rd L es' A' p p' l S S' r r' ms ∗ rnBusySP γ L A' es' p p' l S S' r r' ms ∗
        rnHsC γ p' A' ∗
        ⌜srvIdxOkW E.γr.raft.ai0 A'⌝)) := by
  letI := srvStor (GF := GF) γ.node
  iintro #Henv #Hbr Hcfg HrS Hgot
  iunfold readyGot at Hgot
  icases Hgot with ⟨%ce, %es, %h, %Lo, %ms, %ss, #Hce, #Hcom, ⟨%sts, #Hrs, #Hrsok⟩, Hrest, Hlead,
    Henter, #Hdlb0, #Hhsc⟩
  -- (R2d'a A10 item 5, Q29 (d)) the `MsgSnap`s' terms, from the restart data
  ihave ⟨Hcfg, #Hrok⟩ := rnCfgAt_restartOk γ L $$ Hcfg
  ihave ⟨Hrest, %Hsb⟩ := rnRestartOk_snapTerm γ L p S r rd ce es h Lo ms ss $$ Hrok Hrest
  -- (R2d'a task 4) a snapshot's index above the restart point (A8)
  ihave ⟨Hrest, %Hwa⟩ := rnRestartOk_winAbove γ L p S r rd ce es h Lo ms ss $$ Hrok Hrest
  iunfold readyLeaderMsgs at Hlead
  simp only [committedEntriesAt, rnDrvSt]
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hn, -, #Hinv, #HM, #HC, -, -⟩
  obtain ⟨Hraft, Hpre, Hai0⟩ := Hn
  ihave #Hcl : srvClusterOk E.γr.raft $$ []
  · iunfold srvRaftLogInv at Hinv; icases Hinv with ⟨-, #H, -⟩; iexact H
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
    icases Hrest with ⟨#Hes, Hmsgs, Hmo, #Hhs, #Hss, -, ⟨%Hsp, Hown, #Hcom2, #Hcert, Hold,
      Hgiv⟩, %Hrrf⟩
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
    icases entsPts_elim _ _ _ $$ Hes with ⟨%esL, #HesL, #Hesro⟩
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
      iframe Hmsgs HEC HesL HceL HsvV0
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
        · simpa only [rnDrvSt] using Hst
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
      · ipureintro; exact ⟨hA', hLA, Hfit61, hlastA⟩
      isplitr
      · iapply entriesAt_of_entRO esL es $$ Hesro
      isplitr
      · ipureintro; rfl
      isplitl [Hmo Hlead]
      · iunfold rnRawMsgs; iframe Hmo; isplitl [Hlead]; iexact Hlead; ipureintro; exact Hsb
      isplitr
      · iexists ss; iframe Hss; ipureintro; rfl
      isplitr
      · iunfold hardStateAt
        rw [HardStateModel.toM_ofM]
        iexact Hhs
      isplitr
      · rw [HardStateModel.toM_ofM]; ipureintro; rfl
      iunfold readStatesPts at Hrs
      icases Hrs with ⟨%vs, #Hvs, #Hrs2⟩
      iexists vs
      iframe Hvs
      iapply rnReadStates_of_api E γ vs sts $$ Hbr Hrs2 Hrsok
    isplitl [Hcfg Henter HrS]
    · iunfold rnBusySP
      iframe Hcfg
      isplitl [Henter HrS]
      · iunfold rnPendEnter
        iframe HrS
        iExactEq Henter
        simp only [rnBusyStS, rnDrvSt, EntryModel.map_toM_ofM, hA']
      ipureintro
      exact ⟨hA', Hpfx, Hdl, Hpos, H61, Hwa.imp_right (fun h => h l rfl)⟩
    isplitr
    · iunfold rnHsC
      icases Hhsc with (%Hz | ⟨#Hc, %Hle⟩)
      · ileft; ipureintro; exact Hz
      · iright; iframe Hc; ipureintro; rw [hA']; simpa only [strip, List.length_map] using Hle
    ipureintro; exact HLiW
  | none =>
  simp only [NodeDriverState.afterReady]
  ihave #Hfits : readyFits γ.node.cl srvClusterN $$ []
  · iunfold srvClusterOk at Hcl; icases Hcl with ⟨-, -, -, #H, -⟩; rw [Hraft]; iexact H
  icases readyRest_fits γ.node.cl srvClusterN γ.id rd _ ce es h none ms ss $$ [Hfits Hrest]
    with ⟨Hrest, %Hfit61⟩
  · iframe Hfits Hrest
  simp only [readyRest, readySnap]
  icases Hrest with ⟨#Hes, Hmsgs, Hmo, #Hhs, #Hss, %Hbnd, ⟨%Hsnap, Happ, #Hcf, %Hidx⟩, %Hrrf⟩
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
  icases entsPts_elim _ _ _ $$ Hes with ⟨%esL, #HesL, #Hesro⟩
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
    · iunfold rnRawMsgs; iframe Hmo; isplitl [Hlead]; iexact Hlead; ipureintro; exact Hsb
    isplitr
    · iexists ss; iframe Hss; ipureintro; rfl
    isplitr
    · iunfold hardStateAt
      rw [HardStateModel.toM_ofM]
      iexact Hhs
    isplitr
    · rw [HardStateModel.toM_ofM]; ipureintro; rfl
    isplitr
    · iunfold readStatesPts at Hrs
      icases Hrs with ⟨%vs, #Hvs, #Hrs2⟩
      iexists vs
      iframe Hvs
      iapply rnReadStates_of_api E γ vs sts $$ Hbr Hrs2 Hrsok
    isplitr
    · ipureintro; exact Hsnap
    iunfold rnCeFrozen
    rw [EntryModel.map_toM_ofM, Hce'LE]
    iframe Hcf
    ipureintro
    refine ⟨Hidx, ?_⟩
    -- (R2b-1 stage 4) the batch a WAL `Save` step (`walSaveStep_ready`)
    rw [HardStateModel.toM_ofM, Hdel]
    have Hst := walSaveStep_ready (rnDrvSt γ L p S r) ce es h Hrrf
      (fun j e e0 he0 hj => (Hidx e0 he0).1 j e hj)
    simpa only [rnDrvSt] using Hst
  isplitl [Hcfg Henter HrS]
  · iunfold rnBusyP
    iframe Hcfg
    iunfold rnPendEnter
    iframe HrS
    iExactEq Henter
    simp only [rnBusyStN, rnDrvSt, EntryModel.map_toM_ofM, Hdel]
  isplitr
  · iExactEq Hdlb0; rw [Hdel]
  isplitr
  · iunfold rnHsC
    icases Hhsc with (%Hz | ⟨#Hc, %Hle⟩)
    · ileft; ipureintro; exact Hz
    · iright; iframe Hc; ipureintro; rw [Hdel]; simpa only [List.length_append] using Hle
  ipureintro; exact HLiW

/-! ## The other components -/

/-- **The `*raft.MemoryStorage` `ms`**: `Append` of the `Ready`'s entries turns the right into the
receipt (raft's `MemoryStorage.Append.spec`, `node_contract_memstor`; 2026-10-30, the repair: over
the range contract, the receipt with nothing frozen). -/
def isRNMemStor (γ : RNNames) (ms : Loc) : IProp GF :=
  iprop(□ (∀ (sl : GoSlice) (esL : List Loc) (es : List EntryModel),
    {{ sl ↦*□ esL ∗ entriesAt esL es ∗ rnAppendRight γ es }}
      (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #sl))
    {{ RET #(GoInterface.nil); rnAppendReceipt γ es }}))

instance isRNMemStor_persistent (γ : RNNames) (ms : Loc) :
    Persistent (isRNMemStor (GF := GF) γ ms) := by
  unfold isRNMemStor; infer_instance

/-- (2026-10-31) **The wrapper `r`'s WAL open, at the fraction `q`**: the open token
(`storage.walOpen`) of the WAL of `r`'s storage. The raft loop holds a half, the apply thread the
other (for its disk snapshot's `SaveSnap`), which `stopped` brings back to the loop for `Close`. -/
def rnWalTok (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ st : GoInterface, rnStorageAddr r ↦□ st ∗ storage.walOpen (storage.walOf st) q)

theorem rnWalTok_half (r : Loc) :
    rnWalTok (GF := GF) r (1 : Qp).half ∗ rnWalTok r (1 : Qp).half ⊢ rnWalTok r 1 := by
  unfold rnWalTok
  iintro ⟨⟨%st1, #H1, T1⟩, ⟨%st2, #H2, T2⟩⟩
  icombine H1 H2 gives %Heq
  have Heq' : st1 = st2 := by first | exact Heq | exact Heq.2
  subst Heq'
  iexists st1
  iframe H1
  have h := ((storage.walOpen_fractional (GF := GF) (storage.walOf st1)).fractional
    (1 : Qp).half (1 : Qp).half).2
  rw [Qp.half_add_half] at h
  iapply h
  iframe T1 T2

/-- The token at the storage `st` the wrapper `r` holds. -/
theorem rnWalTok_open (r : Loc) (st : GoInterface) (q : Qp) :
    rnStorageAddr r ↦□ st ∗ rnWalTok (GF := GF) r q ⊢ storage.walOpen (storage.walOf st) q := by
  unfold rnWalTok
  iintro ⟨#Hst, ⟨%st', #Hst', T⟩⟩
  icombine Hst Hst' gives %Heq
  have Heq' : st' = st := by first | exact Heq.symm | exact Heq.2.symm
  subst Heq'
  iexact T

/-- The loop's half and the half `stopped` brings back (`rnStopBag`'s, at the WAL of `r`'s
storage `st`) make the whole token (`onStop`'s `Close`). -/
theorem rnWalTok_join (r : Loc) (st : GoInterface) :
    rnStorageAddr r ↦□ st ∗ rnWalTok (GF := GF) r (1 : Qp).half ∗
      storage.walOpen (storage.walOf st) (1 : Qp).half ⊢ rnWalTok r 1 := by
  iintro ⟨#Hst, T1, T2⟩
  iapply rnWalTok_half r
  iframe T1
  iunfold rnWalTok
  iexists st
  iframe Hst T2

theorem rnWalTok_split (r : Loc) :
    rnWalTok (GF := GF) r 1 ⊢ rnWalTok r (1 : Qp).half ∗ rnWalTok r (1 : Qp).half := by
  unfold rnWalTok
  iintro ⟨%st, #H, T⟩
  icases ((storage.walOpen_fractional (GF := GF) (storage.walOf st)).fractional (1 : Qp).half
      (1 : Qp).half).1 $$ [T] with ⟨T1, T2⟩
  · rw [Qp.half_add_half]; iexact T
  isplitl [T1]
  · iexists st; iframe H T1
  · iexists st; iframe H T2

/-- (2026-11-03, R2b-1 stage 5; review M3) **The apply side's share of the WAL** at the fraction `q`
(its disk snapshot's `SaveSnap`): the open token's share, the apply thread's token `ν.app` (which
rules out the stop's taken state), and the durability invariant; `run` gives it to the loop with
`raftNode.stop` (`rnStopBag`). -/
def rnWalTokA (γ : RNNames) (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ st : GoInterface, rnStorageAddr r ↦□ st ∗ storage.walOpen (storage.walOf st) q ∗
    token γ.wal.app ∗ rnDurInv γ.node.cl γ.wal (storage.walOf st))

/-- (2026-11-03, R2b-1 stage 6) **The loop's share of the WAL**: half the open token, the stop's
claim (`ν.stop`) and what `Close` takes besides the records (the member's metadata, the purge's
right), from `bootstrap` (`wal.bootOk_start`), kept until `onStop`. -/
def rnWalTokL (γ : RNNames) (r : Loc) : IProp GF :=
  iprop(rnWalTok r (1 : Qp).half ∗ token γ.wal.stop ∗
    -- (2026-11-03, R2b-3b) the metadata naming the member `γ.id` (the stop image's `walFiles`)
    ∃ (st : GoInterface) (cid : w64), rnStorageAddr r ↦□ st ∗
      walMetaIs (storage.walOf st) γ.id cid ∗ walPurgeRight (walDirOf (storage.walOf st)))

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
def rnStopBag (E : RNEnv GF) (γ : RNNames) (w : Loc) (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Unit) (fun _ => iprop(E.ST ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
    storage.walOpen w (1 : Qp).half ∗
    -- (2026-11-03, R2b-1 stage 6; review M3) the apply thread's WAL token, with its half
    token γ.wal.app)))

instance rnStopBag_persistent (E : RNEnv GF) (γ : RNNames) (w : Loc) (c : Loc) :
    Persistent (rnStopBag E γ w c) := by
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
def rnRtOk (γ : RNNames) (t : w64) (n : Nat) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(⌜t = W64 0⌝ ∨ ∃ c : w64, committedAtTerm γ.node.cl srvClusterN t c ∗ ⌜(n : Int) ≤ uint.Z c⌝)

instance rnRtOk_persistent (γ : RNNames) (t : w64) (n : Nat) :
    Persistent (rnRtOk (GF := GF) γ t n) := by
  unfold rnRtOk; infer_instance

/-- (2026-10-31) The term the `Ready` loop records (`0` or the driver's hard state's) is good for a
batch of the log the driver was delivered, `pre ++ L` (`nodeDriver_hardStateCommitted`). -/
theorem rn_rtOk_st (γ : RNNames) (rt : w64) (L : List EntryModel) (st : NodeDriverState)
    (hd : st.delivered = srvLE γ.srv L) (Hrt : uint.Z rt = 0 ∨ rt = st.hardState.Term') :
    (letI := srvStor (GF := GF) γ.node; nodeDriver (GF := GF) γ.nl γ.node.cl srvClusterN st) ⊢
      (letI := srvStor (GF := GF) γ.node; nodeDriver γ.nl γ.node.cl srvClusterN st) ∗
        rnRtOk γ rt (rnLogOf γ L).length := by
  letI := srvStor (GF := GF) γ.node
  iintro Hd
  ihave ⟨Hd, #Hc⟩ := nodeDriver_hardStateCommitted _ _ _ _ $$ Hd
  iframe Hd
  iunfold rnRtOk
  rcases Hrt with Hrt | Hrt
  · ileft; ipureintro; word
  · icases Hc with (%Hz | ⟨#Hc, %Hle⟩)
    · ileft; ipureintro; rw [Hrt, Hz]
    · iright
      iexists st.hardState.Commit'
      rw [Hrt]
      iframe Hc
      ipureintro
      rw [hd] at Hle
      simp only [srvLE, rnLogOf, RNNames.srv, List.length_map, List.length_append] at Hle ⊢
      omega

/-- (2026-11-03, R2b-3: *enter* at the `Save`) The term the `Ready` loop records (`0` or the hard
state's after the batch) is good for the batch's log, from the receive's committed hard state
(`rnHsC`; until then the busy driver's, `nodeDriver_hardStateCommitted`). -/
theorem rnRtOk_of_hsC (γ : RNNames) (rt : w64) (L : List EntryModel) (p : HardStateM)
    (Hrt : uint.Z rt = 0 ∨ rt = p.Term') :
    rnHsC (GF := GF) γ p L ⊢ rnRtOk γ rt (rnLogOf γ L).length := by
  iintro #Hc
  iunfold rnRtOk
  rcases Hrt with Hrt | Hrt
  · ileft; ipureintro; word
  · iunfold rnHsC at Hc
    icases Hc with (%Hz | ⟨#Hc, %Hle⟩)
    · ileft; ipureintro; rw [Hrt, Hz]
    · iright
      iexists p.Commit'
      rw [Hrt]
      iframe Hc
      ipureintro
      simp only [srvLE, rnLogOf, RNNames.srv, List.length_map, List.length_append] at Hle ⊢
      omega

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
def rnHands (_γ : RNNames) (ce : List EntryModel) : Bool := ccIn ce

/-- (2026-11-03, R2b-1 stage 5) **The handed log is at least `n` long** (persistent): a committed log
of length at least `n` the loop handed at a `Save` (`walCommitLb`); what the apply thread's own
snapshot at an applied index `n` takes (the batch's `raftAdvancedC`, closed after the `Save`). -/
def rnWalHanded (γ : RNNames) (n : Nat) : IProp GF :=
  iprop(∃ l : List LogEntry, walCommitLb γ.wal l ∗ isCommittedLogLb γ.node.cl l ∗ ⌜n ≤ l.length⌝)

instance rnWalHanded_persistent (γ : RNNames) (n : Nat) : Persistent (rnWalHanded (GF := GF) γ n) := by
  unfold rnWalHanded; infer_instance

/-- `rnWalHanded` at the server's log `L` handed at a `Save` (its lower bound, committed). -/
theorem rnWalHanded_intro (γ : RNNames) (L : List EntryModel) :
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
def rnApR (γ : RNNames) (F ce : List EntryModel) : IProp GF :=
  if rnHands γ ce then rnView γ (F ++ ce) else iprop(True)

/-- (D43 M3) What goes along with the batch: the view after `F` and the committed log handed out
through the batch (`dlvLb`), if `rnHands`. -/
def rnApGive (γ : RNNames) (F ce : List EntryModel) : IProp GF :=
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
`t0 = 0` too (`rnRestartOk`'s first disjunct). -/
theorem rnView_first (γ : RNNames) (h : γ.a0 = []) :
    (γ.t0 = W64 0 → ∀ L, rnCfgAt (GF := GF) γ L ⊣⊢ srvCfgView γ.srv γ.nl γ.pre L) ∧
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
  refine ⟨fun ht L => ?_, fun F ce => ?_, fun F ce => ?_⟩
  · unfold rnCfgAt rnRestartOk
    rw [hv L]
    constructor
    · iintro ⟨H, -⟩; iexact H
    · iintro H; iframe H; ileft; ipureintro; exact ⟨h, ht⟩
  · unfold rnApR; rw [hv]
  · unfold rnApGive; rw [hv]

/-- The `i`th payload on `applyc` with committed entries: the log `F` forwarded before it (`cum[i]`)
and the batch `ce` it extends it with (`cum[i + 1] = F ++ ce`, committed), no snapshot, and its two
channels; and (2026-10-14, unit C2a) the committed index at least the batch's last index
(`committedLast`: `updateCommittedIndex` raised it before the send); and (D22 S-b) its raft term
(`rnRtOk`). (D22 J6a: `rnApP`'s first case; until then `rnApP` itself.) -/
def rnApN (E : RNEnv GF) (γ : RNNames) (i : Int) (ap : toApply) : IProp GF :=
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
    rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length)

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
def rnApSnap (E : RNEnv GF) (γ : RNNames) (i : Int) (ap : toApply) : IProp GF :=
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
      (γ.a0 = [] ∨ γ.a0.length < (γ.pre ++ A').length)⌝ ∗
    -- (2026-11-01, J8a-5) no committed entries with a snapshot (raft's `readySnap`: `ce = []`)
    ap.entries' ↦*□ ([] : List Loc) ∗
    ownSnapM ap.snapshot' DFrac.discard sv ∗
    snapshotCert γ.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
    -- (2026-11-01, J8a) the snapshot's index in the member's snapshot directory (raft's `readySnap`)
    nodeSnapLocal γ.node.cl γ.id sv.Metadata'.Index' ∗ □ E.C A' ∗
    -- `notifyc`: two sends for a snapshot batch (raft.go:274,302), two receives (`applySnapshot`'s,
    -- `applyAll`'s): the two-receive notify (`NotifyC2.lean`; 2026-10-31, #3)
    (∃ γnc : NotifyNames, isNotify2 γnc ap.notifyc' iprop(True) iprop(True) ∗ notifyRcvN γnc 0) ∗
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
def rnApP (E : RNEnv GF) (γ : RNNames) (i : Int) (ap : toApply) : IProp GF :=
  iprop(rnApN E γ i ap ∨ rnApSnap E γ i ap)

/-- (D22 S-b) A batch's raft term, read off its payload (for `applyAll`'s merged snapshot); (D22l)
with the batch's log `F ++ ce` (`cum`'s element `i + 1`) within its witness's commit index. -/
theorem rnApP_rtOk (E : RNEnv GF) (γ : RNNames) (i : Int) (ap : toApply) :
    ⊢ rnApP E γ i ap -∗ rnApP E γ i ap ∗ ∃ (F ce : List EntryModel),
      monoListIdxOwn γ.cum (i.toNat + 1) (F ++ ce) ∗
      rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length := by
  iintro H
  iunfold rnApP at H
  icases H with (H | H)
  · iunfold rnApN at H
    icases H with ⟨%F, %ce, %ceL, #H1, #H2, #H3, #H4, #H5, %H6, H7, HG, #H8, #H9, #Hrt⟩
    isplitl [H7 HG]
    · iunfold rnApP
      ileft
      iunfold rnApN
      iexists F, ce, ceL
      iframe H1 H2 H3 H4 H5 H7 HG H8 H9 Hrt
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
def isRNApplyc (E : RNEnv GF) (γ : RNNames) (c : Loc) : IProp GF :=
  isSspsc γ.ap c (V := toApply) (rnApP E γ) (fun _ => iprop(False))

instance isRNApplyc_persistent (E : RNEnv GF) (γ : RNNames) (c : Loc) :
    Persistent (isRNApplyc E γ c) := by
  unfold isRNApplyc; infer_instance

/-- (2026-11-03, R2b-1 stage 4) **The loop's view of the WAL's durability** at `v` (its half of the
view, `rnDurInv`'s the other), with its "not stopped" token (`ν.ok`). -/
def rnWalView (γ : RNNames) (v : WalView) : IProp GF :=
  iprop(ghostVar γ.wal.view (1 : Qp).half v ∗ token γ.wal.ok)

/-- The loop's ghost state: the driver at the node's delivered log `L`, `applyc`'s producer
half, and `cum`'s authority, one element per payload sent after the first, ending at `L`; and
(2026-10-30, the repair) the loop's half of the node's running token. -/
def rnLoopTokP (γ : RNNames) (L : List EntryModel) (p : HardStateM) (b : Bool) : IProp GF :=
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
    srvFrozenTerms γ.γs (γ.pre.length + 1) L)

/-- The loop's ghost state at some `prevHardSt` (D22l: `rnLoopTokP`, the loop keeps it tied to
the raft term it records). -/
def rnLoopTok (γ : RNNames) (L : List EntryModel) : IProp GF :=
  iprop(∃ p : HardStateM, rnLoopTokP γ L p false)

/-- (R2d'a A10 item 3) **The loop's token carries the restart data** (persistent, in its view,
`rnCfgAt`): `run` reads it before handing the token to `raftNode.start`, for the stop's bound
(`rnRestartOk_commit`). -/
theorem rnLoopTok_restartOk (γ : RNNames) (L : List EntryModel) :
    rnLoopTok (GF := GF) γ L ⊢ rnLoopTok γ L ∗ rnRestartOk γ := by
  iintro H
  iunfold rnLoopTok at H
  icases H with ⟨%p, H⟩
  iunfold rnLoopTokP at H
  icases H with ⟨%sent, %cums, %S, %r, Hdrv, Hrest⟩
  iunfold rnDrv at Hdrv
  icases Hdrv with ⟨Hd, HrS, Hcfg⟩
  iunfold rnCfgAt at Hcfg
  icases Hcfg with ⟨Hv, #Hr⟩
  isplitl [Hd HrS Hv Hrest]
  · iunfold rnLoopTok
    iexists p
    iunfold rnLoopTokP
    iexists sent, cums, S, r
    isplitl [Hd HrS Hv]
    · iunfold rnDrv
      iframe Hd HrS
      iunfold rnCfgAt
      iframe Hv Hr
    iexact Hrest
  iexact Hr

/-- The apply side's ghost state: `applyc`'s consumer half, and `cum` at the number of
payloads received, the log `A` forwarded so far. -/
def rnApplyTok (γ : RNNames) (A : List EntryModel) : IProp GF :=
  iprop(∃ rcv : List toApply, sspscConsumer γ.ap rcv ∗ monoListIdxOwn γ.cum rcv.length A)

/-- `msgSnapC`: a channel of messages raft may send, each a `MsgSnap` (D19p, 2026-10-18: so that
a server whose raft sends none knows the channel never delivers); (D22 S-l sender, 2026-10-22)
each owned with its protocol facts (`rnSnapMsg`), for `applyAll`'s merge, which writes it. -/
def isRNMsgSnapC (γ : RNNames) (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Loc) (rnSnapMsg γ))

instance isRNMsgSnapC_persistent (γ : RNNames) (c : Loc) :
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
the stop image's `srvFiles` is made of (R2b-3c). -/
def rnWalClosedW (γ : RNNames) (w : Loc) (σ : StorContents) : IProp GF :=
  iprop(∃ cid : w64, walFiles (walDirOf w) γ.id cid σ)

/-- **The wrapper `r`'s WAL, closed, its records `σ`** (`raftNode.stop.spec`'s): `rnWalClosedW` at
the WAL of `r`'s storage. -/
def rnWalClosed (γ : RNNames) (r : Loc) (σ : StorContents) : IProp GF :=
  iprop(∃ st : GoInterface, rnStorageAddr r ↦□ st ∗ rnWalClosedW γ (storage.walOf st) σ)

/-- **What the stopped loop leaves** (R2b-3b), at the WAL `w`: the node's id vacant (`node.Stop`'s),
its durable state `S`, the WAL closed with records `σ` holding it, between whose base and commit the
log `L` handed to the apply thread ends; `applyc`'s producer token at the count `sent` of payloads,
`cum` at it `L` (the stop's caller, the apply side, with its consumer token, learns that it
received every payload, `sspsc_sync`, so that its log is `L`: review M2). -/
def rnStopImage (γ : RNNames) (w : Loc) : IProp GF :=
  iprop(nodeVacant γ.node.cl γ.id ∗
    ∃ (S : RaftState) (σ : StorContents) (sent : List toApply) (L : List EntryModel),
      raftState γ.node.cl γ.id S ∗ rnWalClosedW γ w σ ∗
      sspscProducer γ.ap sent ∗ monoListIdxOwn γ.cum sent.length L ∗
      ⌜StorageHolds S σ ∧ σ.b ≤ (γ.pre ++ L).length ∧ (γ.pre ++ L).length ≤ σ.commit⌝ ∗
      -- (R2d, Q14 (a), DRAFT) the records' snapshot certificate (`rnDur_take`'s)
      walSnapCert γ.node.cl σ)

/-- **`done`'s close announces the stop's escrow** (persistent, R2b-3b; until then `True`): the stop
image, or the claim (`rnStopClaim`) once its holder took the image. `onStop` allocates it with the
image as it closes `done`. -/
def rnDoneEsc (γ : RNNames) (w : Loc) : IProp GF :=
  inv rnStopN iprop(rnStopImage γ w ∨ token γ.sc)

instance rnDoneEsc_persistent (γ : RNNames) (w : Loc) : Persistent (rnDoneEsc (GF := GF) γ w) := by
  unfold rnDoneEsc; infer_instance

/-- **The claim on the raft loop's stop escrow** (R2b-3b; until then an opaque draft): `newRaftNode`
allocates it, and `raftNode.stop`'s spec takes it, to take the image out of
`done`'s escrow. -/
def rnStopClaim (γ : RNNames) : IProp GF := token γ.sc

/-! ## The wrapper -/

/-- **The raft wrapper `r`** (persistent): its fields, read-only once started (`start`'s
comment), with their components; `latestTickTs` under `tickMu`; and (2026-10-16, stage R7b) the
discharge's facts of `E` (`rnEnvOk`), the run's premise on the `Ready`s (`rnLogFits`), the read
states' bridge, the `MemoryStorage`'s registration (the `raftStorage` field is the names'). -/
def isRaftNode (E : RNEnv GF) (γ : RNNames) (r : Loc) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  iprop(∃ (lg mu ms td tk : Loc) (n st tr : GoInterface) (idr : GoFunc)
      (hb : time.Duration) (msc apc rsc stc dnc : GoChan),
    "#Henv" ∷ rnEnvOk E γ ∗ "#Hfits" ∷ rnLogFits γ ∗ "#Hrsb" ∷ rnReadStateBridge E γ ∗
    "#Hreg" ∷ memStorReg γ.ms γ.γs ∗
    "#Hlg" ∷ rnLgAddr r ↦□ lg ∗ "%Hlgnn" ∷ ⌜lg ≠ null⌝ ∗
    "#Hmu" ∷ rnTickMuAddr r ↦□ mu ∗ "#Hmug" ∷ sync.isRWMutexGuard mu (rnTickInv r) ∗
    "#Hn" ∷ rnNodeAddr r ↦□ n ∗ "#Hni" ∷ isRaftNodeIfc E γ n ∗
    "#Hidr" ∷ rnIsIDRemovedAddr r ↦□ idr ∗ "#Hidri" ∷ isRNIDRemoved idr ∗
    "#Hms" ∷ rnRaftStorageAddr r ↦□ ms ∗ "%Hmsγ" ∷ ⌜ms = γ.ms⌝ ∗ "#Hmsi" ∷ isRNMemStor γ ms ∗
    "#Hst" ∷ rnStorageAddr r ↦□ st ∗ "#Hsti" ∷ isWalStorage st ∗
    -- (2026-11-03, R2b-1 stage 3c) the WAL's durability invariant
    "#Hdur" ∷ rnDurInv γ.node.cl γ.wal (storage.walOf st) ∗
    "#Hhb" ∷ rnHeartbeatAddr r ↦□ hb ∗
    "#Htr" ∷ rnTransportAddr r ↦□ tr ∗ "#Htri" ∷ isRNTransport E tr ∗
    "#Hmsc" ∷ rnMsgSnapCAddr r ↦□ msc ∗
    "#Hmsci" ∷ isRNMsgSnapC γ msc ∗
    "#Hapc" ∷ rnApplycAddr r ↦□ apc ∗ "#Hapci" ∷ isRNApplyc E γ apc ∗
    "#Hrsc" ∷ rnReadStateCAddr r ↦□ rsc ∗
    "#Hrsci" ∷ isRNReadStateC E rsc ∗
    "#Htk" ∷ rnTickerAddr r ↦□ tk ∗ "#Htki" ∷ isRNTicker tk ∗
    "#Htd" ∷ rnTdAddr r ↦□ td ∗ "#Htdi" ∷ isRNTimeoutDetector td ∗
    "#Hstc" ∷ rnStoppedAddr r ↦□ stc ∗ "#Hstci" ∷ rnStopBag E γ (storage.walOf st) stc ∗
    "#Hdnc" ∷ rnDoneAddr r ↦□ dnc ∗
    -- (2026-11-03, R2b-3b) its close announces the stop's escrow (until then `True`)
    "#Hdnci" ∷ ownBroadcastChan dnc γ.done (rnDoneEsc γ (storage.walOf st)) .Unknown)

instance isRaftNode_persistent (E : RNEnv GF) (γ : RNNames) (r : Loc) :
    Persistent (isRaftNode E γ r) where
  persistent := by
    unfold isRaftNode
    iintro H
    iNamed H
    imodintro
    iexists lg, mu, ms, td, tk, n, st, tr, idr, hb, msc, apc, rsc, stc, dnc
    simp only [named]
    iframe #
    isplit
    · ipureintro; exact Hlgnn
    · ipureintro; exact Hmsγ

/-- The right to close `done` (the loop's: its deferred `onStop`). -/
def rnDoneTok (γ : RNNames) (r : Loc) : IProp GF :=
  iprop(∃ (dnc : GoChan) (st : GoInterface), rnDoneAddr r ↦□ dnc ∗ rnStorageAddr r ↦□ st ∗
    ownBroadcastChan dnc γ.done (rnDoneEsc γ (storage.walOf st)) .Pending)


/-- (2026-11-03, R2b-3b; review M2) **The stop's caller takes the image out of `done`'s escrow**: with
the claim and the apply side's token at the log `A` it was handed, the image the loop left, its
handed log `A` (the producer's and the consumer's tokens agree, `applyc` being synchronous,
`sspsc_sync`: every payload sent was received). -/
theorem rn_esc_take (E : RNEnv GF) (γ : RNNames) (c w : Loc) (A : List EntryModel) :
    ⊢ isRNApplyc E γ c -∗ rnDoneEsc γ w -∗ rnStopClaim γ -∗ rnApplyTok γ A -∗ £ 1 -∗ £ 1 ={⊤}=∗
      nodeVacant γ.node.cl γ.id ∗ ∃ (S : RaftState) (σ : StorContents),
        raftState γ.node.cl γ.id S ∗ rnWalClosedW γ w σ ∗
        ⌜StorageHolds S σ ∧ σ.b ≤ (γ.pre ++ A).length ∧ (γ.pre ++ A).length ≤ σ.commit⌝ ∗
        walSnapCert γ.node.cl σ := by
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
  icases Himg with ⟨Hvac, %S, %σ, %sent, %L, HrS, Hcl, Hprod, #Hidx, %Hord, #Hσc⟩
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
  iframe HrS Hcl Hσc
  ipureintro; exact Hord

end defs

end EtcdGrove
end Perennial
