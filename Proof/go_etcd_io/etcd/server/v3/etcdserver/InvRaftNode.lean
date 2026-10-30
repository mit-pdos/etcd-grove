/-
The server's raft wrapper (`server/v3/etcdserver/raft.go`): the shared vocabulary of
`Spec/raftNode__*.lean`. Lean-first (no Rocq counterpart); the plan is `decisions.md`, "The
server's raft wrapper"; since 2026-10-16 (stage R7b of the raft v3.7 retarget, D10) the node's
predicates are definitions over raft's own (`Proof/go_etcd_io/raft/v3/InvNode.lean`), and the
node contract is to be discharged from raft's specs.

- **The environment** `E : RNEnv` is what the node contract is stated over: `C L`, "`L` is a
  prefix of the cluster's committed log"; `M m`, "raft may send the message `m`"; `T`, a tick's
  resource (node.go's term-budget credit); and (2026-10-13, the request path's unit 4b) the read
  names `γr` and the read-index registrations `RQ id n` (`ReadIndex` registered the request id
  `id` at a lower bound `n` of the committed index), which the read states a `Ready` carries
  answer (`srvReadStateOk`, `read/Inv.lean`). What the discharge needs of `E` is `rnEnvOk E γ`
  (persistent, in `isRaftNode`): `E.T` raft's tick credit, `E.M` of a message raft handed out
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
- **`applyc`** is an SPSC channel (`isSpsc`) of `toApply`s; the `k`th payload carries the
  mono-list `cum`'s elements `k` and `k + 1` (the log forwarded before and after it), so the
  consumer, at `cum[|received|] = A` (`rnApplyTok γ A`), learns that the batch extends `A`. The
  loop (`rnLoopTok γ L`) owns the producer half and `cum`'s authority, whose last element is
  the node's delivered log `L`.
- **The other components** are persistent predicates of triples (the WAL, the
  `MemoryStorage`, the transport, the timeout detector, the ready handler's closures, the
  ticker, whose ticks carry `E.T`), and the wrapper's fields are read-only after `start` but
  `latestTickTs`, under `tickMu` (`rnTickInv`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Perennial.Golang.Theory.Chan.Idioms.Idioms
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopChan
public import Perennial.Ghost.MonoList

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
the mono-list `cum` of the log forwarded after each payload; the broadcast channel `done`. -/
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
**A `MsgSnap` raft handed out, owned**: the message at some fraction (a `Ready`'s), of type
`MsgSnap`, sent by the node, with its credits (`sentMsg_snapshot` gives its snapshot's
certificate): what `processMessages` hands to `msgSnapC` and `applyAll`'s merge rewrites. -/
def rnSnapMsg (γ : RNNames) (m : Loc) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ (dq : DFrac) (st : MsgSt), msgOwn m dq st ∗ ⌜st.msg.Type' = MsgSnap⌝ ∗
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

/-- The right to append `es` to the `MemoryStorage` (from a `Ready`): raft's storage API's
`appendRight` at the storage (the range from the batch's first index owned), and the indices'
bound. -/
def rnAppendRight (γ : RNNames) (es : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(appendRight (memStorIface γ.ms) (es.map EntryModel.toM) ∗ ⌜rnFits es⌝)

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

/-- A `Ready`'s `SoftState`: nil, or read-only fields (raft's `softStateRO`). -/
def softStateAt (p : Loc) : IProp GF := softStateRO p

instance softStateAt_persistent (p : Loc) : Persistent (softStateAt (GF := GF) p) := by
  unfold softStateAt; infer_instance

/-- What a `Ready` gives the driver, after the committed log `d` handed out before it: the
committed entries `ce` to apply next (`C (d ++ ce)`), the entries `es` to append with the right
to, the messages, each one raft may send; a `SoftState`, a `HardState` (`p'` the last non-empty
one, `p` before); the read states, each answering the registrations of its request id
(`srvReadStateOk E.RQ`); no snapshot. (2026-10-27: raft's commit witness of the hard state,
`hsWit`, is gone: the snapshot sender that needed it is unreachable, `rnSnapMsg`.) -/
def rnReadyData (E : RNEnv GF) (γ : RNNames) (rd : Ready) (d ce es : List EntryModel)
    (p p' : HardStateM) : IProp GF :=
  iprop(∃ (ceL esL msL : List Loc) (hs : HardStateModel),
    rd.CommittedEntries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (d ++ ce) ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗ rnAppendRight γ es ∗
    rd.Messages' ↦*□ msL ∗ ([∗list] m ∈ msL, rnMsgR E γ m) ∗
    softStateAt rd.SoftState' ∗ hardStateAt rd.HardState' hs ∗
    ⌜p' = phsNext p hs.toM⌝ ∗
    (∃ rsL : List ReadState, rd.ReadStates' ↦*□ rsL ∗ [∗list] rs ∈ rsL, srvReadStateOk E.γr.raft E.RQ rs) ∗
    ⌜rd.Snapshot' = null⌝)

/-- **The driver's view of the configuration after the committed log `L`** (D43 M3; 2026-10-30,
the repair: raft's one mode, the old dynamic one's): the view after `pre ++ L`, every conf entry of
it applied (`srvCfgView`, `InvCfgView.lean`); until the repair nothing in a static cluster. -/
def rnCfgAt (γ : RNNames) (L : List EntryModel) : IProp GF :=
  srvCfgView γ.srv γ.nl γ.pre L

/-- The driver's state at the committed log `L` handed out and the hard state `p`, idle. -/
def rnDrvSt (γ : RNNames) (L : List EntryModel) (p : HardStateM) : NodeDriverState :=
  ⟨memStorIface γ.ms, srvLE γ.srv L, p, none⟩

/-- The driver, idle, handed the committed log `L` so far: the node API's `nodeDriver` at
`pre ++ L` (2026-10-27; until then raft's), with the driver's view of the configuration after `L`
(`rnCfgAt`); `p` the hard state of the last `Ready` with a non-empty one. -/
def rnDrv (γ : RNNames) (L : List EntryModel) (p : HardStateM) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(nodeDriver γ.nl γ.node.cl srvClusterN (rnDrvSt γ L p) ∗ rnCfgAt γ L)

/-- The driver with a `Ready` in hand, handed the committed log `d ++ ce`, to append `es`
before `Advance`: the node API's `nodeDriver` busy, without the view. -/
def rnBusyN (γ : RNNames) (d ce es : List EntryModel) (p : HardStateM) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  nodeDriver γ.nl γ.node.cl srvClusterN
    ⟨memStorIface γ.ms, srvLE γ.srv (d ++ ce), p, some (es.map EntryModel.toM, none)⟩

/-- The driver with a `Ready` in hand (`rnBusyN`) and its view after the log before it, `d`. -/
def rnBusy (γ : RNNames) (d ce es : List EntryModel) (p : HardStateM) : IProp GF :=
  iprop(rnBusyN γ d ce es p ∗ rnCfgAt γ d)


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
right to, the messages, soft state, hard state (`p'` after `p`) and read states as `rnReadyData`'s. -/
def rnReadySnap (E : RNEnv GF) (γ : RNNames) (rd : Ready) (d es A' : List EntryModel)
    (p p' : HardStateM) (l : SnapLoan) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ (esL msL : List Loc) (hs : HardStateModel),
    readySnap γ.node.cl srvClusterN γ.id rd (rnDrvSt γ d p) [] (es.map EntryModel.toM) (some l) ∗
    ⌜srvLE γ.srv A' = strip l.dlv ∧ d.length < A'.length⌝ ∗ □ E.C A' ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗
    rd.Messages' ↦*□ msL ∗ ([∗list] m ∈ msL, rnMsgR E γ m) ∗
    softStateAt rd.SoftState' ∗ hardStateAt rd.HardState' hs ∗ ⌜p' = phsNext p hs.toM⌝ ∗
    (∃ rsL : List ReadState, rd.ReadStates' ↦*□ rsL ∗
      [∗list] rs ∈ rsL, srvReadStateOk E.γr.raft E.RQ rs))

/-- (D22 J6a; 2026-10-30, the repair: until then `False`) **The driver with a snapshot `Ready` in
hand**: the node API's `nodeDriver` busy with the loan, delivered the snapshot's log `A'`, its view
after the log before (`rnCfgAt γ d`, replaced by `Advance`'s answer at the snapshot). -/
def rnBusyS (γ : RNNames) (d A' es : List EntryModel) (p : HardStateM) (l : SnapLoan) :
    IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(nodeDriver γ.nl γ.node.cl srvClusterN
      ⟨memStorIface γ.ms, srvLE γ.srv A', p, some (es.map EntryModel.toM, some l)⟩ ∗
    rnCfgAt γ d)

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
    □ (∀ (d ce es : List EntryModel) (p : HardStateM),
      {{ rnBusyN γ d ce es p ∗ rnCfgAt γ (d ++ ce) ∗ rnAdvReceipt γ d ce es ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) }}
        (App (Val #(methods ni.ty go!"Advance" ni.v)) (Val #()))
      -- (2026-10-30, the repair) and the node's applied index past the committed log handed out
      {{ RET #(); rnDrv γ (d ++ ce) p ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
          nodeAppliedLb γ.node.cl γ.id (γ.pre ++ d ++ ce).length }}) ∗
    -- (2026-10-30, the repair: snapshots allowed) `Advance` after a snapshot `Ready`: the storage's
    -- `snapReceipt` (the snapshot applied, the entries after it appended) and the snapshot's
    -- certificate; the idle driver at the snapshot's log `A'` with its view there
    □ (∀ (d A' es : List EntryModel) (p : HardStateM) (l : SnapLoan),
      {{ rnBusyS γ d A' es p l ∗
          snapReceipt (memStorIface γ.ms) l (es.map EntryModel.toM) ∗
          snapshotCert γ.node.cl srvClusterN (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) ∗
          nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half }}
        (App (Val #(methods ni.ty go!"Advance" ni.v)) (Val #()))
      {{ RET #(); rnDrv γ A' p ∗ nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half ∗
          nodeAppliedLb γ.node.cl γ.id (γ.pre ++ A').length }}) ∗
    □ ({{ True }} (App (Val #(methods ni.ty go!"Tick" ni.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ nodeRunning γ.nl γ.node.cl srvClusterN 1 }}
        (App (Val #(methods ni.ty go!"Stop" ni.v)) (Val #()))
      {{ RET #(); nodeStopped γ.nl γ.node.cl srvClusterN }}) ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice)
        (id n : w64) (Qr : List EntryModel → IProp GF),
      {{ context.isContext ctx cd ∗ sl ↦*□ beBytes id ∗ committedAtLeast E.γr n ∗
          srvReadAu E.γr.raft Qr ∗ srvRdFresh E.γr.raft (beBytes id) }}
        (App (App (Val #(methods ni.ty go!"ReadIndex" ni.v)) (Val #(GoInterface.ok ctx)))
          (Val #sl))
      {{ (err : GoInterface), RET #err; applyErrIs err ∗
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

/-- The messages a `Ready` hands out, each one `E.M` admits, with its credits, persisted (the
server's clusters send no `MsgSnap`, `srv_sentMsg_notSnap`). -/
theorem rnMsgOk_of_api [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames) :
    ∀ ms : List QMsg,
      ⊢ □ (∀ (m : Loc) (st : MsgSt), msgOwn m DFrac.discard st ∗
          sentMsg γ.node.cl srvClusterN γ.id st ∗ msgCredits γ.node.cl srvClusterN st ∗ ⌜st.msg.Type' ≠ MsgSnap⌝ -∗
          E.M m) -∗ srvClusterOk E.γr.raft -∗ ⌜E.γr.raft.raft = γ.node⌝ -∗
        ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗
          sentMsg γ.node.cl srvClusterN γ.id q.st ∗ msgCredits γ.node.cl srvClusterN q.st)
          ={⊤}=∗
        [∗list] m ∈ ms.map QMsg.loc, rnMsgR E γ m
  | [] => by
    iintro #HM - - -
    imodintro
    simp only [List.map_nil]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | q :: ms => by
    iintro #HM #Hcl %Hraft H
    icases (BigSepL.bigSepL_cons (Φ := fun _ (q : QMsg) => iprop(msgOwn (GF := GF) q.loc
      (readyDq q.st) q.st ∗ sentMsg γ.node.cl srvClusterN γ.id q.st ∗
      msgCredits γ.node.cl srvClusterN q.st))).1 $$ H with ⟨⟨Hm, #Hsm, Hc⟩, Hrest⟩
    imod rnMsgOk_of_api E γ ms $$ HM Hcl %Hraft Hrest with Hrest
    simp only [List.map_cons]
    by_cases hsn : q.st.msg.Type' = MsgSnap
    · -- (2026-10-30, the repair) a `MsgSnap`: owned, for `msgSnapC`
      imodintro
      iapply (BigSepL.bigSepL_cons (Φ := fun _ m => rnMsgR (GF := GF) E γ m)).2
      iframe Hrest
      iunfold rnMsgR
      iright
      iunfold rnSnapMsg
      iexists (readyDq q.st), q.st
      iframe Hm Hsm Hc
      ipureintro; exact hsn
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

/-- (2026-10-27) **Receiving a `Ready`, after the node API's receive** (`isReadyChan_recvAu`'s
postcondition): the idle driver at `L` learns the `Ready`'s data in the server's terms and is busy
with it; the messages persisted, `E.C` of the committed log (`rnEnvOk`), the read states answered
(`rnReadStateBridge`); and the committed log delivered through the batch (`deliveredLogLb`, for a
dynamic cluster's `ApplyConfChange`). A `Ready` with a snapshot is refuted (`srv_readySnap_none`). -/
theorem rn_ready_recv [go_etcd_io.raft.v3.Assumptions] (E : RNEnv GF) (γ : RNNames)
    (L : List EntryModel) (p : HardStateM) (rd : Ready) (ce : List LogEntry)
    (es : List EntryM) (h : HardStateM) (Lo : Option SnapLoan)
    (HLi : srvIdxOkW E.γr.raft.ai0 L) :
    letI := srvStor (GF := GF) γ.node
    rnEnvOk E γ -∗ rnReadStateBridge E γ -∗ rnCfgAt γ L -∗
      committedEntriesAt rd.CommittedEntries' (rnDrvSt γ L p).delivered.length ce -∗
      isCommittedLogLb γ.node.cl ((rnDrvSt γ L p).delivered ++ ce) -∗
      (∃ rs, readStatesPts rd.ReadStates' rs ∗
        [∗list] s ∈ rs, readStateOk γ.node.cl srvClusterN s.RequestCtx' s.Index') -∗
      readyRest γ.node.cl srvClusterN γ.id rd (rnDrvSt γ L p) ce es h Lo -∗
      nodeDriver γ.nl γ.node.cl srvClusterN (match Lo with
          | none => { rnDrvSt γ L p with
              delivered := (rnDrvSt γ L p).delivered ++ ce
              hardState := phsNext (rnDrvSt γ L p).hardState h
              handling := some (es, none) }
          | some l => { rnDrvSt γ L p with
              delivered := strip l.dlv
              hardState := phsNext (rnDrvSt γ L p).hardState h
              handling := some (es, some l) }) ={⊤}=∗
      (∃ ce' es' p', rnReadyData E γ rd L ce' es' p p' ∗ rnBusy γ L ce' es' p' ∗
        deliveredLogLb γ.nl γ.node.cl srvClusterN (srvLE γ.srv (L ++ ce')) ∗
        ⌜srvIdxOkW E.γr.raft.ai0 (L ++ ce')⌝) ∨
      -- (2026-10-30, the repair: snapshots allowed) a `Ready` with a snapshot
      (∃ (es' A' : List EntryModel) (p' : HardStateM) (l : SnapLoan),
        rnReadySnap E γ rd L es' A' p p' l ∗ rnBusyS γ L A' es' p' l ∗
        ⌜srvIdxOkW E.γr.raft.ai0 A'⌝) := by
  letI := srvStor (GF := GF) γ.node
  simp only [committedEntriesAt, rnDrvSt]
  iintro #Henv #Hbr Hcfg #Hce #Hcom ⟨%sts, #Hrs, #Hrsok⟩ Hrest Hdrv
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hn, -, #Hinv, #HM, #HC, -, -⟩
  obtain ⟨Hraft, Hpre, Hai0⟩ := Hn
  ihave #Hcl : srvClusterOk E.γr.raft $$ []
  · iunfold srvRaftLogInv at Hinv; icases Hinv with ⟨-, #H, -⟩; iexact H
  cases Lo with
  | some l =>
    -- SNAPSHOT-SORRY: `rnReadySnap` from `readySnap (some l)` and the messages, `rnBusyS` from
    -- the driver
    sorry
  | none =>
  ihave #Hfits : readyFits γ.node.cl srvClusterN $$ []
  · iunfold srvClusterOk at Hcl; icases Hcl with ⟨-, -, -, #H, -⟩; rw [Hraft]; iexact H
  icases readyRest_fits γ.node.cl srvClusterN γ.id rd _ ce es h none $$ [Hfits Hrest]
    with ⟨Hrest, %Hfit61⟩
  · iframe Hfits Hrest
  simp only [readyRest, readySnap]
  icases Hrest with ⟨%ms, #Hes, Hmsgs, Hmo, #Hhs, #Hss, %Hbnd, ⟨%Hsnap, Happ, -, -⟩⟩
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
  imod rnMsgOk_of_api E γ ms $$ HM Hcl %Hraft Hmo with Hmok
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
  ihave ⟨Hdrv, #Hdlb⟩ := nodeDriver_deliveredLogLb γ.nl γ.node.cl srvClusterN _ $$ Hdrv
  imodintro
  ileft
  iexists ce', es.map EntryModel.ofM, phsNext p h
  isplitl [Happ Hmok]
  · iunfold rnReadyData
    iexists ceL, esL, ms.map QMsg.loc, HardStateModel.ofM h
    iframe HceL HesL Hmsgs Hmok HEC
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
      intro e0 He0
      rw [List.head?_map] at He0
      cases Hh : es.head? with
      | none => rw [Hh] at He0; cases He0
      | some x =>
        rw [Hh] at He0; cases He0
        have := Hfit61 x Hh
        simp only [List.length_map]
        show uint.Z x.Index' + (es.length : Int) ≤ 2 ^ 61
        omega
    isplitr
    · iunfold softStateAt; iexact Hss
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
    ipureintro; exact Hsnap
  isplitl [Hcfg Hdrv]
  · iunfold rnBusy
    iframe Hcfg
    iunfold rnBusyN
    rw [EntryModel.map_toM_ofM, Hdel]
    iexact Hdrv
  · rw [Hdel]; iframe Hdlb; ipureintro; exact HLiW

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

/-- **The WAL `st`** (`serverstorage.Storage`, trust boundary: names-only): `Save` of a hard
state and entries returns some error (on which the loop exits the process, `lg.Fatal`);
`Close` succeeds (otherwise `onStop` panics in the loop's goroutine, which crashes etcd: the
contract assumes it does not). -/
def isRNWal (st : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
        (es : List EntryModel),
      {{ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; True }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ RET #(GoInterface.nil); True }}) ∗
    -- (D22 J1a, 2026-10-26) `SaveSnap(snap)`: reads the snapshot's metadata (`snap.Metadata.Index`,
    -- `.Term`, `GetConfState()`: the metadata pointer must be set) and writes the WAL's snapshot
    -- record (`storage.go`: `st.w.SaveSnapshot`; at the pin it no longer writes a `.snap` file),
    -- for the raft loop's snapshot branch and the apply thread's disk snapshot
    □ (∀ (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM),
      {{ sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPts mp dq' md }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err;
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPts mp dq' md }}) ∗
    -- (D22 J1a) `Sync()`: syncs the WAL
    □ ({{ True }} (App (Val #(methods si.ty go!"Sync" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; True }}))

instance isRNWal_persistent (st : GoInterface) : Persistent (isRNWal (GF := GF) st) := by
  unfold isRNWal; infer_instance

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

/-- **The ticker `tk`** (Perennial models no `time.Ticker`; a trust-boundary contract): its `C`
is a channel on which a receive yields some time **with a tick's resource `E.T`** (2026-10-16,
stage R7b: raft's tick credit came with the tick, "fewer than `2^64 - 1` ticks in a run" the
ticker's premise; since D19b, 2026-10-18, `E.T` is `True` for the server, `raftNode.tick` taking
the credit, a time receipt, from a Go step of its own), or nil (`newRaftNode`'s `&time.Ticker{}` when `heartbeat == 0`); `Stop`
returns. -/
def isRNTicker (E : RNEnv GF) (tk : Loc) : IProp GF :=
  iprop(∃ c : Loc, structFieldRef time.Ticker go!"C" tk ↦□ c ∗
    (⌜c = chan.nil⌝ ∨ ∃ γc : ChanNames, isChanBag γc c (V := time.Time) (fun _ => E.T)) ∗
    □ ({{ True }} (App (Val (tk @!! go.GoType.PointerType time.Ticker.ty @!! go!"Stop")) (Val #()))
      {{ RET #(); True }}))

instance isRNTicker_persistent (E : RNEnv GF) (tk : Loc) : Persistent (isRNTicker E tk) := by
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
`node.Stop` takes. -/
def rnStopBag (E : RNEnv GF) (γ : RNNames) (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Unit) (fun _ => iprop(E.ST ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half))))

instance rnStopBag_persistent (E : RNEnv GF) (γ : RNNames) (c : Loc) :
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


/-- (D22 S-b, item 2; 2026-10-27: trivial) The raft term a batch carries (`toApply.raftTerm`):
until 2026-10-27 `0` or a term with raft's commit witness, for the snapshot sender's merged
snapshot, which is unreachable on the node API (`rnSnapMsg`). -/
def rnRtOk (_γ : RNNames) (_t : w64) (_n : Nat) : IProp GF := iprop(True)

instance rnRtOk_persistent (γ : RNNames) (t : w64) (n : Nat) :
    Persistent (rnRtOk (GF := GF) γ t n) := by
  unfold rnRtOk; infer_instance

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

/-- (D43 M3) What the apply thread's `notifyc` receive deposits: the view after the batch, if it
went along. -/
def rnApR (γ : RNNames) (F ce : List EntryModel) : IProp GF :=
  if rnHands γ ce then rnCfgAt γ (F ++ ce) else iprop(True)

/-- (D43 M3) What goes along with the batch: the view after `F` and the committed log handed out
through the batch (`dlvLb`), if `rnHands`. -/
def rnApGive (γ : RNNames) (F ce : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  if rnHands γ ce then
    iprop(rnCfgAt γ F ∗ deliveredLogLb γ.nl γ.node.cl srvClusterN (srvLE γ.srv (F ++ ce)))
  else iprop(True)

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
       iprop(nodeAppliedLb γ.node.cl γ.id (γ.pre ++ F ++ ce).length ∗
        -- (2026-10-30, the repair) the batch's entries frozen in the storage (`CreateSnapshot`'s)
        srvFrozenRange γ.γs ((γ.pre ++ F).length + 1) ((γ.pre ++ F ++ ce).length + 1))) ∗
    committedLast E.γr ce ∗
    -- (D22 S-b) the raft term it carries; (D22l) whose witness's commit index bounds the batch
    rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length)

/-- (D22 J6a, 2026-10-26) **The `i`th payload on `applyc` with a snapshot** (raft's snapshot `Ready`,
`readySnapData`; `raftNode.start` hands the apply thread its own clone of `rd.Snapshot`): the log
`F` forwarded before it (`cum[i]`) and the committed log up to the snapshot `A'` it jumps to
(`cum[i + 1] = A'`, extending `F` strictly, `pre ++ A'` the snapshot's index long), no committed
entries, the clone read-only (`ownSnapM … DFrac.discard`), `E.C A'`, the snapshot local to the node
(`snapLocal`: for the server, saved in the member's snapshot directory), the snapshot's id the last
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
    ⌜F.length < A'.length ∧ (γ.pre ++ A').length = uint.nat sv.Metadata'.Index'⌝ ∗
    ownSnapM ap.snapshot' DFrac.discard sv ∗
    snapshotCert γ.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗ □ E.C A' ∗
    -- `notifyc`: two sends for a snapshot batch (raft.go:274,302); stated with the entries' one
    -- receive until the two-receive notify is written with the branch's proof (SNAPSHOT-SORRY)
    (∃ γnc : NotifyNames, isNotify γnc ap.notifyc' iprop(True) ∗ notifyRcv γnc) ∗
    -- closed once `Advance` returned: the node's applied index at the snapshot
    rnAdvChan ap.raftAdvancedC' iprop(nodeAppliedLb γ.node.cl γ.id (γ.pre ++ A').length ∗
      -- the snapshot's dummy entry frozen, everything below compacted (`ApplySnapshot`'s)
      srvFrozenAt γ.γs (γ.pre ++ A').length ∗ srvFrozenBelow γ.γs (γ.pre ++ A').length) ∗
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
    icases H with ⟨%F, %A', %sv, #H1, #H2, %H3, #H4, #H5, #H6, H7, #H8, #H9, #Hrt⟩
    isplitl [H7]
    · iunfold rnApP
      iright
      iunfold rnApSnap
      iexists F, A', sv
      iframe H1 H2 H4 H5 H6 H7 H8 H9 Hrt
      ipureintro; exact H3
    iexists A', []
    rw [List.append_nil]
    iframe H2 Hrt

/-- `applyc` (persistent): an SPSC channel of `rnApP` payloads, never closed (its close's
resource is `False`: 2026-10-13, the request path's unit 4c, `True` until then; the loop never
closes it, and the apply side's receive needs that it is not closed). -/
def isRNApplyc (E : RNEnv GF) (γ : RNNames) (c : Loc) : IProp GF :=
  isSpsc γ.ap c (V := toApply) (rnApP E γ) (fun _ => iprop(False))

instance isRNApplyc_persistent (E : RNEnv GF) (γ : RNNames) (c : Loc) :
    Persistent (isRNApplyc E γ c) := by
  unfold isRNApplyc; infer_instance

/-- The loop's ghost state: the driver at the node's delivered log `L`, `applyc`'s producer
half, and `cum`'s authority, one element per payload sent after the first, ending at `L`; and
(2026-10-30, the repair) the loop's half of the node's running token. -/
def rnLoopTokP (γ : RNNames) (L : List EntryModel) (p : HardStateM) : IProp GF :=
  iprop(∃ (sent : List toApply) (cums : List (List EntryModel)),
    rnDrv γ L p ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗ spscProducer γ.ap sent ∗ monoListAuthOwn γ.cum 1 cums ∗
    ⌜cums.length = sent.length + 1 ∧ cums.getLast? = some L⌝ ∗
    -- (2026-10-27) the log's indices consecutive from the start's (`rn_ready_recv`'s premise)
    ⌜∃ ai : w64, uint.Z ai = γ.pre.length ∧ srvIdxOkW ai L⌝)

/-- The loop's ghost state at some `prevHardSt` (D22l: `rnLoopTokP`, the loop keeps it tied to
the raft term it records). -/
def rnLoopTok (γ : RNNames) (L : List EntryModel) : IProp GF :=
  iprop(∃ p : HardStateM, rnLoopTokP γ L p)

/-- The apply side's ghost state: `applyc`'s consumer half, and `cum` at the number of
payloads received, the log `A` forwarded so far. -/
def rnApplyTok (γ : RNNames) (A : List EntryModel) : IProp GF :=
  iprop(∃ rcv : List toApply, spscConsumer γ.ap rcv ∗ monoListIdxOwn γ.cum rcv.length A)

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
    "#Hst" ∷ rnStorageAddr r ↦□ st ∗ "#Hsti" ∷ isRNWal st ∗
    "#Hhb" ∷ rnHeartbeatAddr r ↦□ hb ∗
    "#Htr" ∷ rnTransportAddr r ↦□ tr ∗ "#Htri" ∷ isRNTransport E tr ∗
    "#Hmsc" ∷ rnMsgSnapCAddr r ↦□ msc ∗
    "#Hmsci" ∷ isRNMsgSnapC γ msc ∗
    "#Hapc" ∷ rnApplycAddr r ↦□ apc ∗ "#Hapci" ∷ isRNApplyc E γ apc ∗
    "#Hrsc" ∷ rnReadStateCAddr r ↦□ rsc ∗
    "#Hrsci" ∷ isRNReadStateC E rsc ∗
    "#Htk" ∷ rnTickerAddr r ↦□ tk ∗ "#Htki" ∷ isRNTicker E tk ∗
    "#Htd" ∷ rnTdAddr r ↦□ td ∗ "#Htdi" ∷ isRNTimeoutDetector td ∗
    "#Hstc" ∷ rnStoppedAddr r ↦□ stc ∗ "#Hstci" ∷ rnStopBag E γ stc ∗
    "#Hdnc" ∷ rnDoneAddr r ↦□ dnc ∗ "#Hdnci" ∷ ownBroadcastChan dnc γ.done iprop(True) .Unknown)

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
  iprop(∃ dnc : GoChan, rnDoneAddr r ↦□ dnc ∗ ownBroadcastChan dnc γ.done iprop(True) .Pending)

end defs

end EtcdGrove
end Perennial
