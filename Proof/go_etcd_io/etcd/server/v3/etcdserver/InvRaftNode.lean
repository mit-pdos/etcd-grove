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
  registration (`srvRQ`), and the names tied (`E.γr.raft.raft = γ.node.raft`, ...).
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
public import Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
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
variable [FfiSyntax]

-- `Ready`'s countable instance: raft's (`InvNode.ready_countable`; the server's own went with
-- stage R7b, the file importing raft's node layer).

instance toApply_countable : Pos.Countable toApply :=
  countableOfLeftInverse (fun a : toApply => (a.entries', a.snapshot', a.notifyc', a.raftAdvancedC', a.raftTerm'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

-- `ReadState`'s instance (`readState_countable`): `InvRequest.lean` (2026-10-13, the read loop).

end countable

/-- The ghost names of a raft wrapper (2026-10-16, stage R7b: raft's): the node's names (raft's
`NodeNames`: its channels, the delivered log `dlv`, its record `rof`, the configuration), the
node's id and the `*raft.node` behind the interface, the committed log before the server's start
index (`ServerRaftNames.pre`, the same list), the `*MemoryStorage`, its names and the registry's
ghost name (`memStorReg`, raft's `MemstorageInstance.lean`: the registry is a class there, so that
`memStorageModel` is an instance; here its name is a field, and each predicate over raft's node
layer builds the instance from it, `letI : MemStorReg GF := ⟨γ.reg⟩`, so that no section of the
server needs the class); `applyc`'s SPSC names and the mono-list `cum` of the log forwarded after
each payload; the broadcast channel `done`. -/
structure RNNames [FfiSyntax] where
  node : NodeNames
  id : w64
  nl : Loc
  pre : List EntryModel
  ms : Loc
  γs : MemStorNames
  reg : GName
  ap : SpscNames
  cum : GName
  done : ChanNames

/-- Raft's full committed log holding the server's `L` after its start (`srvLogOf`, by the
wrapper's names). -/
def rnLogOf [FfiSyntax] (γ : RNNames) (L : List EntryModel) : List EntryM :=
  (γ.pre ++ L).map EntryModel.toM

theorem rnLogOf_append [FfiSyntax] (γ : RNNames) (A B : List EntryModel) :
    rnLogOf γ (A ++ B) = rnLogOf γ A ++ B.map EntryModel.toM := by
  simp [rnLogOf]

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- A message the node handed out, as the wrapper reads and forwards it: its destination and
type read-only, and `E.M m`. (2026-10-19, D21 stage M1: owned, no longer persistent, so that
`E.M` can carry a message's one-shot read credit to the transport; until then `□ E.M m`.) -/
def rnMsgOk (E : RNEnv GF) (m : Loc) : IProp GF :=
  iprop(∃ (to : w64) (ty : w32), msgAt m to ty ∗ E.M m)

/-- (D22 S-l sender, 2026-10-22) **A `MsgSnap` raft handed out, owned**, with its protocol facts:
raft's `Ready` hands a `MsgSnap` out whole (`readyDq`: not a response), and `applyAll`'s merge
writes its `Snapshot` field (`createMergedSnapshotMessage`), so it is not persisted like the others
(`rnMsgOk`): what `processMessages` hands `msgSnapC` (`isRNMsgSnapC`). Its read credit is `0` and
its tickets none (`stTks`: a `MsgProp`'s only), so `isRaftMsg` and `termLB` are all it carries. -/
def rnSnapMsg (γ : NodeNames) (m : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn m (DFrac.own 1) st ∗ ⌜st.msg.Type' = MsgSnap⌝ ∗
    isRaftMsg γ.raft γ.id st ∗ termLB γ.bud st.msg.Term')

/-- (D22 S-l sender) **A message of a `Ready`, as the server receives it**: any but a `MsgSnap`
read-only with `E.M` (`rnMsgOk`'s, with its type not `MsgSnap`), a `MsgSnap` owned
(`rnSnapMsg`). `processMessages` turns the first into `rnMsgOk` for the transport and hands the
second to `msgSnapC`. -/
def rnMsgR (E : RNEnv GF) (γ : NodeNames) (m : Loc) : IProp GF :=
  iprop((∃ (to : w64) (ty : w32), msgAt m to ty ∗ ⌜ty ≠ MsgSnap⌝ ∗ E.M m) ∨ rnSnapMsg γ m)

/-! ## The node's `Ready`/`Advance` exchange -/

/-- `MemoryStorage.Append`'s index bound (`Spec/go_etcd_io/raft/v3/MemoryStorage__Append.lean`):
the batch's last index at most `2^61`. -/
def rnFits (es : List EntryModel) : Prop :=
  ∀ e0, es.head? = some e0 → uint.Z e0.index + (es.length : Int) ≤ 2 ^ 61

/-- The right to append `es` to the `MemoryStorage` (from a `Ready`): raft's `appendRight` at
the storage, and the bound `Append` needs (2026-10-16, stage R7b). -/
def rnAppendRight (γ : RNNames) (es : List EntryModel) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  iprop(appendRight (memStorIface γ.ms) (es.map EntryModel.toM) ∗ ⌜rnFits es⌝)

/-- The receipt of the append of `es` (for `Advance`): raft's `appendReceipt`. -/
def rnAppendReceipt (γ : RNNames) (es : List EntryModel) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  appendReceipt (memStorIface γ.ms) (es.map EntryModel.toM)

/-- A `Ready`'s `SoftState`: nil, or read-only fields (raft's `softStateRO`). -/
def softStateAt (p : Loc) : IProp GF := softStateRO p

instance softStateAt_persistent (p : Loc) : Persistent (softStateAt (GF := GF) p) := by
  unfold softStateAt; infer_instance

/-- What a `Ready` gives the driver, after the committed log `d` handed out before it: the
committed entries `ce` to apply next (`C (d ++ ce)`), the entries `es` to append with the right
to, the messages, each one raft may send; a `SoftState`, a `HardState`; the read states, each
answering the registrations of its request id (`srvReadStateOk E.RQ`; 2026-10-13, the request path's
unit 4b: they were none until then, as node.go's `readyData`); no snapshot. -/
def rnReadyData (E : RNEnv GF) (γ : RNNames) (rd : Ready) (d ce es : List EntryModel)
    (p p' : HardStateM) : IProp GF :=
  iprop(∃ (ceL esL msL : List Loc) (hs : HardStateModel),
    rd.CommittedEntries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (d ++ ce) ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗ rnAppendRight γ es ∗
    rd.Messages' ↦*□ msL ∗ ([∗list] m ∈ msL, rnMsgR E γ.node m) ∗
    softStateAt rd.SoftState' ∗ hardStateAt rd.HardState' hs ∗
    -- (D22 S-b) raft's witness of a non-empty hard state: the node's term and commit index at the
    -- `Ready` (`commitWit`), the commit index bounding the committed log handed out; (D22l) of
    -- `prevHardSt` after the `Ready` (`p'`, `phsNext p hs`: the last non-empty one, `p` before)
    ⌜p' = phsNext p hs.toM⌝ ∗ hsWit γ.node.raft p' (rnLogOf γ (d ++ ce)).length ∗
    (∃ rsL : List ReadState, rd.ReadStates' ↦*□ rsL ∗ [∗list] rs ∈ rsL, srvReadStateOk E.γr.raft E.RQ rs) ∗
    ⌜rd.Snapshot' = null⌝)

/-- A `Ready` on the node's channel: raft's payload (`readyP`; `E` unused, kept for the
statements' shape). -/
def rnReadyP (_E : RNEnv GF) (γ : RNNames) (rd : Ready) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  readyP γ.node rd

/-- **The driver's view of the configuration after the committed log `L`** (`nodeCfg`, which
`Advance` takes and returns; D43 M3, 2026-10-25): in raft's dynamic mode the view after
`pre ++ L`, every conf entry of it applied (`srvCfgView`, `InvCfgView.lean`); in the static mode
any `nodeCfg`. -/
def rnCfgAt (γ : RNNames) (L : List EntryModel) : IProp GF :=
  if γ.node.mode.isDyn then srvCfgView γ.node γ.pre L
  else iprop(∃ (ca : Nat) (cfg : CCState), nodeCfg γ.node ca cfg)

/-- (D43 M3) The view opened for `Advance`: raft's `nodeCfg`, with in the dynamic mode every conf
entry of the log handed out applied (A1), and back. -/
theorem rnCfgAt_open (γ : RNNames) (L : List EntryModel) :
    rnCfgAt (GF := GF) γ L ⊢ ∃ (ca : Nat) (cfg : CCState), nodeCfg γ.node ca cfg ∗
      ⌜γ.node.mode.isDyn = true → NoConfIn (rnLogOf γ L) ca (rnLogOf γ L).length⌝ ∗
      (nodeCfg γ.node ca cfg -∗ rnCfgAt γ L) := by
  unfold rnCfgAt
  split
  · unfold srvCfgView
    iintro ⟨%ca, %cfg, Hc, %Hok⟩
    iexists ca, cfg
    iframe Hc
    isplitr
    · ipureintro; intro _; exact Hok.2.1
    iintro Hc
    iexists ca, cfg
    iframe Hc
    ipureintro; exact Hok
  · iintro ⟨%ca, %cfg, Hc⟩
    iexists ca, cfg
    iframe Hc
    isplitr
    · ipureintro; intro h; simp_all
    iintro Hc
    iexists ca, cfg
    iexact Hc

/-- The driver, idle, handed the committed log `L` so far: raft's `nodeDriver` at `pre ++ L`,
with the driver's view of the configuration after `L` (`rnCfgAt`); (D22l) `p` the hard state of
the last `Ready` with a non-empty one (raft's `prevHardSt`). -/
def rnDrv (γ : RNNames) (L : List EntryModel) (p : HardStateM) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  iprop(nodeDriver γ.node γ.id γ.nl (rnLogOf γ L) p ∗ rnCfgAt γ L)

/-- The driver with a `Ready` in hand, handed the committed log `d ++ ce`, to append `es`
before `Advance`: raft's `nodeDriverBusy`, without the view. -/
def rnBusyN (γ : RNNames) (d ce es : List EntryModel) (p : HardStateM) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  nodeDriverBusy γ.node γ.id γ.nl (rnLogOf γ (d ++ ce)) (es.map EntryModel.toM) p

/-- The driver with a `Ready` in hand (`rnBusyN`) and its view after the log before it, `d`. -/
def rnBusy (γ : RNNames) (d ce es : List EntryModel) (p : HardStateM) : IProp GF :=
  iprop(rnBusyN γ d ce es p ∗ rnCfgAt γ d)

/-- A read credit for one `ReadIndex` (raft's `rdCred`, by the node's names). -/
def rnReadCred (γ : RNNames) : IProp GF := rdCred γ.node.raft 1

/-- **Raft's read registration of the request id `id`** (persistent; 2026-10-16, stage R7b: what
`E.RQ id n Qr` is for the server): the read of the context `beBytes id` deposited with the
lifted result predicate (`isRead`), at a committed log `Lc` (`readReq`) at least `n` long (`n` a
lower bound of the committed index at the registration). -/
def srvRQ (γs : ServerRaftNames) (id n : w64) (Qr : List EntryModel → IProp GF) : IProp GF :=
  iprop(∃ Lc : List EntryM, isRead γs.raft (beBytes id) (srvLift γs Qr) ∗
    readReq γs.raft (beBytes id) Lc ∗ ⌜uint.Z n ≤ (Lc.length : Int)⌝)

instance srvRQ_persistent (γs : ServerRaftNames) (id n : w64) (Qr : List EntryModel → IProp GF) :
    Persistent (srvRQ (GF := GF) γs id n Qr) := by
  unfold srvRQ; infer_instance

/-- **What the discharge needs of the environment `E`** (persistent; 2026-10-16, stage R7b,
D10): a tick's resource is raft's tick credit; the names tied (the server's raft names are the
node's, the start log and index the same); the node in the static mode, its storage the
`MemoryStorage`; a message raft handed out (read-only, a protocol message at a term the budget
reached) is one `E.M` admits; `E.C` of a committed log prefix whose next index fits (the
server's composition proves it from its KV invariant), and back, the committed log and the
indices of what `E.C` holds (the ready loop's `updateCommittedIndex` needs them); `E.RQ` raft's
read registration. (2026-10-19, D21 stage M1: a message's bundle includes its read credit, one
for a `MsgReadIndex`, which raft's `readyData` hands out with it and the receiver's `Step` takes,
`netP`; until then the credit was dropped.) -/
def rnEnvOk (E : RNEnv GF) (γ : RNNames) : IProp GF :=
  iprop(⌜E.T = iprop(True)⌝ ∗
    ⌜E.γr.raft.raft = γ.node.raft ∧ E.γr.raft.pre = γ.pre ∧
      uint.Z E.γr.raft.ai0 = γ.pre.length⌝ ∗
    -- (D22 S-d4, 2026-10-21) in raft's no-snapshot mode (`RaftNames.reNoSnap`): no `Ready` hands
    -- out a snapshot (`readyP_none`), and `Advance` gives the floor's witness (`reqWit_none`)
    -- (D43 M3, 2026-10-25) the node's mode: static exactly when raft's names are (until then
    -- static only), and in the dynamic mode at the server's decoder
    ⌜(γ.node.mode = RNMode.static ↔ γ.node.raft.reDyn = none) ∧
      (∀ dec c0 h0 h1, γ.node.mode = .dyn dec c0 h0 h1 → dec = srvDec) ∧
      γ.node.stor = memStorIface γ.ms ∧ γ.node.raft.reNoSnap = true⌝ ∗
    -- (2026-10-19, D21 M3) the storage's cap at least `1` (`compactRaftLog`'s compaction at `1`)
    ⌜1 ≤ γ.γs.cap⌝ ∗
    □ (∀ (m : Loc) (st : MsgSt), msgOwn m DFrac.discard st ∗ isRaftMsg γ.node.raft γ.node.id st ∗
        termLB γ.node.bud st.msg.Term' ∗
        rdCred γ.node.raft (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗
        stTks γ.node.raft st -∗ E.M m) ∗
    □ (∀ L : List EntryModel, srvRLogLb E.γr.raft L -∗
        ⌜uint.Z E.γr.raft.ai0 + 1 + L.length < 2 ^ 64⌝ ={⊤}=∗ □ E.C L) ∗
    □ (∀ L : List EntryModel, E.C L -∗ srvRLogLb E.γr.raft L ∗ ⌜srvIdxOk E.γr.raft.ai0 L⌝) ∗
    ⌜E.RQ = srvRQ E.γr.raft⌝)

instance rnEnvOk_persistent (E : RNEnv GF) (γ : RNNames) : Persistent (rnEnvOk E γ) := by
  unfold rnEnvOk; infer_instance

/-- **The run's premise on raft's `Ready`s** (pure since 2026-10-18, D19b stage 5; until then a
trust-boundary premise on every `Ready`, D10): the time-receipt bound past the bootstrap log fits
`MemoryStorage.Append`'s index bound. Every index a `Ready` hands out is within the node's log
(`readyIdx`), whose last index has a record keeping a time receipt (`lastRec_receipt`), so the
entries fit `Append` (`rnFits`) and the committed index handed out has a successor. -/
def rnLogFits (γ : RNNames) : IProp GF :=
  iprop(⌜receiptBound GF + γ.node.raft.reBoot.length ≤ 2 ^ 61⌝)

instance rnLogFits_persistent (γ : RNNames) : Persistent (rnLogFits (GF := GF) γ) := by
  unfold rnLogFits; infer_instance

/-- **The read states' bridge** (persistent): a `ReadState` raft hands out (`readStateOk`, its
cells read-only) answers the server's registrations (`srvReadStateOk`). `srvReadStateOk_of_raft`
proves it from `rnEnvOk` and raft's commit invariant (`rnReadStateBridge_of_raft`; since B2 of
stage R7b `srvReadStateOk` states the context deposited, `srvCtxDeposited`, not its length: the
read loop derives the length from its mint, `readCtxMinted`). -/
def rnReadStateBridge (E : RNEnv GF) (γ : RNNames) : IProp GF :=
  iprop(□ ∀ (st : ReadStateM) (v : ReadState),
    readStateOk γ.node.raft st -∗ ⌜v.Index' = st.Index'⌝ -∗ v.RequestCtx' ↦*□ st.RequestCtx' -∗
      srvReadStateOk E.γr.raft E.RQ v)

instance rnReadStateBridge_persistent (E : RNEnv GF) (γ : RNNames) :
    Persistent (rnReadStateBridge E γ) := by
  unfold rnReadStateBridge; infer_instance

/-- `rnEnvOk`'s read credit, from the server's. -/
theorem rnReadCred_of_srv (E : RNEnv GF) (γ : RNNames) :
    rnEnvOk E γ ∗ srvRdCred E.γr.raft ⊢ rnReadCred γ := by
  unfold rnEnvOk srvRdCred rnReadCred
  iintro ⟨⟨-, %Hn, -⟩, H⟩
  rw [← Hn.1]
  iexact H

/-- **A read state, in the server's terms** (what `rnReadStateBridge` states, under `rnEnvOk`
and raft's commit invariant). -/
theorem srvReadStateOk_of_raft (E : RNEnv GF) (γ : RNNames) (st : ReadStateM) (v : ReadState) :
    rnEnvOk E γ ∗ srvRaftLogInv E.γr.raft ∗ readStateOk γ.node.raft st ∗ ⌜v.Index' = st.Index'⌝ ∗
      v.RequestCtx' ↦*□ st.RequestCtx' ⊢ srvReadStateOk E.γr.raft E.RQ v := by
  iintro ⟨#Henv, #Hinv, #Hst, %Hi, #Hctx⟩
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, -, -, -, -, -, %HRQ⟩
  obtain ⟨Hraft, -, -⟩ := Hn
  iunfold readStateOk at Hst
  icases Hst with ⟨%c, %Hc, #Hok⟩
  rw [HRQ]
  iunfold srvReadStateOk
  iexists st.RequestCtx'
  iframe Hctx
  isplitr
  · -- the context was deposited (its registration, `readOk`'s `readReq`)
    iunfold srvCtxDeposited
    ihave #Hok' := Hok
    iunfold readOk at Hok'
    icases Hok' with ⟨%Lc', #Hreq', -⟩
    iexists Lc'
    rw [Hraft, Hc]
    iexact Hreq'
  iintro !> %id %n %Qr %Hbs #HRQ'
  iunfold srvRQ at HRQ'
  icases HRQ' with ⟨%Lc, #Hrd, #Hreq, %HnLc⟩
  rw [Hc] at Hbs
  subst Hbs
  ihave #Hreq2 : readReq γ.node.raft (beBytes id) Lc $$ []
  · rw [← Hraft]; iexact Hreq
  ihave #Hrd2 : isRead γ.node.raft (beBytes id) (srvLift E.γr.raft Qr) $$ []
  · rw [← Hraft]; iexact Hrd
  ihave #Hok' := Hok
  iunfold readOk at Hok'
  icases Hok' with ⟨%Lc', #Hreq', %HLc'⟩
  icases readReq_agree γ.node.raft _ _ _ $$ Hreq2 Hreq' with %HLeq
  subst HLeq
  isplitr
  · ipureintro; rw [Hi]; omega
  ihave #Hw : readWit E.γr.raft.raft (beBytes id) (srvLift E.γr.raft Qr) v.Index' $$ []
  · iunfold readWit
    rw [Hi, Hraft]
    iframe Hrd2 Hok
  iapply srvReadWit_of_raft E.γr.raft (beBytes id) Qr v.Index' $$ Hinv Hw

/-- **The read states' bridge, from raft** (2026-10-16, stage R7b): under `rnEnvOk` and raft's
commit invariant (`srvRaftLogInv`). -/
theorem rnReadStateBridge_of_raft (E : RNEnv GF) (γ : RNNames) :
    ⊢ rnEnvOk E γ -∗ srvRaftLogInv E.γr.raft -∗ rnReadStateBridge E γ := by
  iintro #Henv #Hinv
  iunfold rnReadStateBridge
  iintro !> %st %v #Hst %Hi #Hctx
  iapply srvReadStateOk_of_raft E γ st v
  iframe Henv Hinv Hst Hctx
  ipureintro; exact Hi

/-- (D19i part 1) The `MemoryStorage` `ms`'s floor is at least `n` (persistent): its witness
`memFloorTok`, the application's right to compact and snapshot up to it. -/
def memFloorAtLeast (ms : Loc) (γs : MemStorNames) (n : Int) : IProp GF :=
  iprop(∃ x : w64, memFloorTok ms γs x ∗ ⌜n ≤ uint.Z x⌝)

instance memFloorAtLeast_persistent (ms : Loc) (γs : MemStorNames) (n : Int) :
    Persistent (memFloorAtLeast (GF := GF) ms γs n) := by
  unfold memFloorAtLeast memFloorTok; infer_instance

/-- **The `raft.Node` `n`** (see the file header; the trust boundary until R7's discharge):
`Ready` returns the node's handshake channel (raft's `readyP`), `Advance` takes the busy driver
and the append receipt, `Tick` a tick's resource, `Stop` returns; and (2026-10-13, the request
path's unit 4b) `ReadIndex(ctx, rctx)`, with the big-endian bytes of a request id read-only, a
lower bound `n` of the committed index (`committedAtLeast E.γr n`), the read's update, and
(2026-10-16, stage R7b) a read credit and the context's fresh token, returns an error the gRPC
layer can take, and if `nil` the registration `E.RQ id n` (persistent): a read index is at least
the committed index at the call (the read loop's `isReadRaft`). -/
def isRaftNodeIfc (E : RNEnv GF) (γ : RNNames) (n : GoInterface) : IProp GF :=
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗
    -- (D43 M3, 2026-10-25) in raft's dynamic mode, its `ApplyConfChange` (the apply thread's)
    (⌜γ.node.mode.isDyn = false⌝ ∨ raftApplyCCDyn γ.node n) ∗
    □ ({{ True }} (App (Val #(methods ni.ty go!"Ready" ni.v)) (Val #()))
      {{ (ch : Loc), RET #ch; isHandshake (V := Ready) γ.node.readyc ch (rnReadyP E γ) iprop(True) }}) ∗
    -- (D43 M3) with the view after the batch (in the dynamic mode its conf entries applied)
    □ (∀ (d ce es : List EntryModel) (p : HardStateM),
      {{ rnBusyN γ d ce es p ∗ rnCfgAt γ (d ++ ce) ∗ rnAppendReceipt γ es }}
        (App (Val #(methods ni.ty go!"Advance" ni.v)) (Val #()))
      -- (D19i part 1) and the storage's floor at least the committed log handed out
      {{ RET #(); rnDrv γ (d ++ ce) p ∗ memFloorAtLeast γ.ms γ.γs (γ.pre ++ d ++ ce).length }}) ∗
    □ ({{ ⧗ 1 }} (App (Val #(methods ni.ty go!"Tick" ni.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ni.ty go!"Stop" ni.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice)
        (id n : w64) (Qr : List EntryModel → IProp GF),
      {{ context.isContext ctx cd ∗ sl ↦*□ beBytes id ∗ committedAtLeast E.γr n ∗
          srvReadAu E.γr.raft Qr ∗ rnReadCred γ ∗ srvRdFresh E.γr.raft (beBytes id) }}
        (App (App (Val #(methods ni.ty go!"ReadIndex" ni.v)) (Val #(GoInterface.ok ctx)))
          (Val #sl))
      {{ (err : GoInterface), RET #err; applyErrIs err ∗
          (⌜err = GoInterface.nil⌝ -∗ □ E.RQ id n Qr) }}))

instance isRaftNodeIfc_persistent (E : RNEnv GF) (γ : RNNames) (n : GoInterface) :
    Persistent (isRaftNodeIfc E γ n) := by
  unfold isRaftNodeIfc; infer_instance

/-- The context the request path passes (`mvcc.txnCtx`: `Done()` nil, or Perennial's context)
is one raft's node API takes (`nodeCtx`, the same disjunction; for the discharge of
`raftPropose`, B3). -/
theorem txnCtx_nodeCtx (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    mvcc.txnCtx ctx cd ⊢ nodeCtx ctx cd := by
  unfold mvcc.txnCtx nodeCtx mvcc.doneNil doneNilCtx
  iintro (#H | #H)
  · ileft; iexact H
  · iright; iexact H

/-! ### Receiving a `Ready`: raft's data in the server's terms -/

/-- The messages a `Ready` hands out, each one `E.M` admits, with its read credit (2026-10-19, D21
stage M1), persisted; (D22 S-l sender, 2026-10-22) but a `MsgSnap`, kept owned (`rnSnapMsg`:
`readyDq` hands it out whole). -/
theorem rnMsgOk_of_raft (E : RNEnv GF) (γ : RNNames) :
    ∀ ms : List QMsg,
      ⊢ □ (∀ (m : Loc) (st : MsgSt), msgOwn m DFrac.discard st ∗ isRaftMsg γ.node.raft γ.node.id st ∗
          termLB γ.node.bud st.msg.Term' ∗
          rdCred γ.node.raft (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗
          stTks γ.node.raft st -∗ E.M m) -∗
        ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ.node.raft γ.node.id q.st ∗
          termLB γ.node.bud q.st.msg.Term') -∗
        ([∗list] q ∈ ms, rdCred γ.node.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) -∗
        ([∗list] q ∈ ms, stTks γ.node.raft q.st)
          ={⊤}=∗
        [∗list] m ∈ ms.map QMsg.loc, rnMsgR E γ.node m
  | [] => by
    iintro #HM - - -
    imodintro
    simp only [List.map_nil]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | q :: ms => by
    iintro #HM H Hc Htk
    icases (BigSepL.bigSepL_cons (Φ := fun _ (q : QMsg) => iprop(msgOwn (GF := GF) q.loc (readyDq q.st) q.st ∗
      isRaftMsg γ.node.raft γ.node.id q.st ∗ termLB γ.node.bud q.st.msg.Term'))).1 $$ H with ⟨⟨Hm, #Hrm, #Htl⟩, Hrest⟩
    icases (BigSepL.bigSepL_cons (Φ := fun _ (q : QMsg) => rdCred (GF := GF) γ.node.raft
      (if q.st.msg.Type' = MsgReadIndex then 1 else 0))).1 $$ Hc with ⟨Hc1, Hcrest⟩
    icases (BigSepL.bigSepL_cons (Φ := fun _ (q : QMsg) => stTks (GF := GF) γ.node.raft q.st)).1
      $$ Htk with ⟨Ht1, Htrest⟩
    imod rnMsgOk_of_raft E γ ms $$ HM Hrest Hcrest Htrest with Hrest
    simp only [List.map_cons]
    by_cases hsn : q.st.msg.Type' = MsgSnap
    · -- a `MsgSnap`: owned (not a response type)
      have hdq : readyDq q.st = DFrac.own 1 := by
        unfold readyDq RespType
        rw [hsn]
        decide
      rw [hdq]
      imodintro
      iapply (BigSepL.bigSepL_cons (Φ := fun _ m => rnMsgR (GF := GF) E γ.node m)).2
      iframe Hrest
      iunfold rnMsgR
      iright
      iunfold rnSnapMsg
      iexists q.st
      iframe Hm Hrm Htl
      ipureintro; exact hsn
    imod msgOwn_persist_fupd q.loc _ q.st ⊤ $$ Hm with #Hm
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := fun _ m => rnMsgR (GF := GF) E γ.node m)).2
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
    iframe Hm Hrm Htl Hc1 Ht1

/-- The read states a `Ready` hands out, each answering the server's registrations (through
the bridge). -/
theorem rnReadStates_of_raft (E : RNEnv GF) (γ : RNNames) :
    ∀ (vs : List ReadState) (sts : List ReadStateM),
      ⊢ rnReadStateBridge E γ -∗
        ([∗list] v;st ∈ vs;sts, ⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx') -∗
        ([∗list] st ∈ sts, readStateOk γ.node.raft st) -∗
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
    icases (BigSepL.bigSepL_cons (Φ := fun _ st => readStateOk (GF := GF) γ.node.raft st)).1 $$ Hok
      with ⟨#Hok1, #Hok'⟩
    ihave #Hrest := rnReadStates_of_raft E γ vs sts' $$ Hbr H2' Hok'
    iapply (BigSepL.bigSepL_cons (Φ := fun _ v => srvReadStateOk (GF := GF) E.γr.raft E.RQ v)).2
    iframe Hrest
    iunfold rnReadStateBridge at Hbr
    iapply Hbr $$ %st %v Hok1 %Hi Hc

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

/-- **Receiving a `Ready`** (in the loop's `select`; 2026-10-16, stage R7b: raft's payload, the
server's data derived): the idle driver at `L` learns the payload's log is `L`, and is busy with
it; the messages persisted (`msgOwn_persist`), `E.C` of the committed log (`rnEnvOk`), the entries
fit (`rnLogFits`), the read states answered (`rnReadStateBridge`); each message with the read
credit raft hands out with it (2026-10-19, D21 stage M1; until then dropped); (D43 M3) and the
committed log handed out through the batch (`dlvLb`, persistent: raft's `ApplyConfChange` checks a
conf change against it). -/
theorem rn_ready_recv (E : RNEnv GF) (γ : RNNames) (L : List EntryModel) (p : HardStateM)
    (rd : Ready) :
    rnEnvOk E γ -∗ rnLogFits γ -∗ rnReadStateBridge E γ -∗ rnDrv γ L p -∗ rnReadyP E γ rd ={⊤}=∗
      ∃ ce es p', rnReadyData E γ rd L ce es p p' ∗ rnBusy γ L ce es p' ∗
        dlvLb γ.node (rnLogOf γ (L ++ ce)) := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro #Henv #Hfits #Hbr Hdrv HP
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, %Hmode, -, #HM, #HC, -, -⟩
  obtain ⟨Hraft, Hpre, Hai0⟩ := Hn
  obtain ⟨-, -, Hstor, Hns⟩ := Hmode
  iunfold rnReadyP at HP
  -- (D22 S-d4) no snapshot: raft's no-snapshot mode
  icases readyP_none γ.node rd (.inl Hns) $$ HP with ⟨%d, %ce, %es, %ms, %p0, %p', Hd, Hrof, Hdata, #Hlb⟩
  iunfold rnDrv at Hdrv
  icases Hdrv with ⟨Hdrv, Hcfg⟩
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨#Hnode, Hds, -, Hreq⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hd Hds
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  iunfold rnLogFits at Hfits
  icases Hfits with %Hrb
  iunfold readyData at Hdata
  icases Hdata with ⟨#Hce, #Hcom, #Hes, Happ, Hmsgs, Hmo, Hmc, Hmt, ⟨%sts, #Hrs, #Hrsok⟩,
    ⟨%h, #Hhs, %Hp'⟩, #Hhw, #Hss, %Hsnap, #Hri⟩
  -- (2026-10-18, D19b stage 5) the indices handed out, bounded by the receipt of the log's last
  iunfold readyIdx at Hri
  icases Hri with ⟨%Lx, #Hlr, %Hix⟩
  imod lastRec_receipt γ.node.raft Lx $$ Hlr with #Hrc
  ihave %Hlt := preceipt_lt (GF := GF) _ $$ Hrc
  have Hfit : rnFits (es.map EntryModel.ofM) ∧ ((rnLogOf γ L) ++ ce).length + 1 < 2 ^ 64 := by
    obtain ⟨_, Hes0, Hd⟩ := Hix
    refine ⟨fun e0 He0 => ?_, by omega⟩
    rw [List.head?_map] at He0
    cases Hh : es.head? with
    | none => rw [Hh] at He0; cases He0
    | some x =>
      rw [Hh] at He0; cases He0
      have := Hes0 x Hh
      simp only [List.length_map]
      show uint.Z x.Index' + (es.length : Int) ≤ 2 ^ 61
      omega
  icases entsPts_elim _ _ _ $$ Hce with ⟨%ceL, #HceL, #Hcero⟩
  icases entsPts_elim _ _ _ $$ Hes with ⟨%esL, #HesL, #Hesro⟩
  imod ownSlice_persist _ _ _ $$ Hmsgs with #Hmsgs
  imod rnMsgOk_of_raft E γ ms $$ HM Hmo Hmc Hmt with Hmok
  -- `E.C (L ++ ce)` from the committed log, the next index fitting
  ihave #HLb : srvRLogLb E.γr.raft (L ++ ce.map EntryModel.ofM) $$ []
  · iunfold srvRLogLb
    unfold srvLogOf
    rw [Hraft, Hpre, ← List.append_assoc, List.map_append, EntryModel.map_toM_ofM]
    rw [show List.map EntryModel.toM (γ.pre ++ L) = rnLogOf γ L from rfl]
    iexact Hcom
  imod HC $$ %(L ++ ce.map EntryModel.ofM) HLb [] with #HEC
  · ipureintro
    have h2 := Hfit.2
    simp only [List.length_append, List.length_map, rnLogOf] at h2 ⊢
    push_cast at h2 ⊢
    omega
  imodintro
  iexists ce.map EntryModel.ofM, es.map EntryModel.ofM, p'
  isplitl [Happ Hmok]
  · iunfold rnReadyData
    iexists ceL, esL, ms.map QMsg.loc, HardStateModel.ofM h
    iframe HceL HesL Hmsgs Hmok HEC
    isplitr
    · iapply entriesAt_of_entRO ceL ce $$ Hcero
    isplitr
    · iapply entriesAt_of_entRO esL es $$ Hesro
    isplitl [Happ]
    · iunfold rnAppendRight
      rw [EntryModel.map_toM_ofM, ← Hstor]
      iframe Happ
      ipureintro; exact Hfit.1
    isplitr
    · iunfold softStateAt; iexact Hss
    isplitr
    · iunfold hardStateAt
      rw [HardStateModel.toM_ofM]
      iexact Hhs
    isplitr
    · rw [HardStateModel.toM_ofM]; ipureintro; exact Hp'
    isplitr
    · rw [rnLogOf_append, EntryModel.map_toM_ofM]
      iexact Hhw
    isplitr
    · iunfold readStatesPts at Hrs
      icases Hrs with ⟨%vs, #Hvs, #Hrs2⟩
      iexists vs
      iframe Hvs
      iapply rnReadStates_of_raft E γ vs sts $$ Hbr Hrs2 Hrsok
    ipureintro; exact Hsnap
  isplitl [Hcfg Hd Hds Hrof Hreq]
  · iunfold rnBusy
    iframe Hcfg
    iunfold rnBusyN
    iunfold nodeDriverBusy
    iframe Hnode
    rw [EntryModel.map_toM_ofM, rnLogOf_append, EntryModel.map_toM_ofM]
    isplitr
    · iunfold dlvLb; iexact Hlb
    iexists rnLogOf γ L, ce, _
    iframe Hd Hds Hrof
    isplitr
    · ipureintro; rfl
    iexact Hreq
  · rw [rnLogOf_append, EntryModel.map_toM_ofM]
    iunfold dlvLb; iexact Hlb

/-! ## The other components -/

/-- **The `*raft.MemoryStorage` `ms`** (trust boundary: v3.7's raft is names-only): `Append`
of the `Ready`'s entries turns the right into the receipt. -/
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
raft may send, borrowing `E.S` (2026-10-24); `Stop` returns. -/
def isRNTransport (E : RNEnv GF) (tr : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tr = GoInterface.ok ti⌝ ∗
    □ (∀ (sl : GoSlice) (msL : List Loc),
      {{ sl ↦* msL ∗ ([∗list] m ∈ msL, rnMsgOk E m) ∗ E.S }}
        (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #sl))
      {{ RET #(); E.S }}) ∗
    □ ({{ True }} (App (Val #(methods ti.ty go!"Stop" ti.v)) (Val #())) {{ RET #(); True }}))

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

/-- `raftAdvancedC` (D19i part 1, 2026-10-18: the fork closes it after every `Advance`, and
`applyAll` waits for it before snapshotting or compacting): a broadcast channel, never sent on,
closed once (`make(chan struct{}, 1)`: a `stopChan`), its close carrying `P` (the storage's floor
past the batch, `rnApP`); a reader's view of it. -/
def rnAdvChan (c : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ γc : ChanNames, ownStopChan c γc P .Unknown)

instance rnAdvChan_persistent (c : Loc) (P : IProp GF) : Persistent (rnAdvChan (GF := GF) c P) := by
  unfold rnAdvChan; infer_instance


/-- (D22 S-b, item 2) The raft term a batch carries (`toApply.raftTerm`, the latest non-empty
`HardState` term the raft goroutine saw, D22a): `0`, or a term of which raft handed out the
witness `commitWit` (`readyData`'s `hsWit`) at a commit index `c` of at least `n`, the batch's
raft index (D22l: the witness is of raft's `prevHardSt` after each `Ready`, so it covers the
batches of `Ready`s with a `nil` `HardState` too; `notes/decisions.md`, "D22 D22l carried out"). -/
def rnRtOk (γ : RNNames) (t : w64) (n : Nat) : IProp GF :=
  iprop(⌜uint.Z t = 0⌝ ∨ ∃ c : w64, commitWit γ.node.raft t c ∗ ⌜(n : Int) ≤ uint.Z c⌝)

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

/-- (D22l) A batch's raft term from the witness of `prevHardSt` after its `Ready` (`rnReadyData`'s
`hsWit` of `p'`): the term recorded is `0` or `p'`'s, whose commit index bounds the batch. -/
theorem rnRtOk_of_hsWit (γ : RNNames) (t : w64) (p' : HardStateM) (n : Nat)
    (Ht : uint.Z t = 0 ∨ t = p'.Term') :
    hsWit (GF := GF) γ.node.raft p' n ⊢ rnRtOk γ t n := by
  iintro #H
  iunfold rnRtOk
  iunfold hsWit at H
  icases H with (%Hz | ⟨#Hcw, %Hn⟩)
  · ileft; ipureintro
    rcases Ht with h | h
    · exact h
    · rw [h, Hz]; rfl
  · by_cases h0 : uint.Z t = 0
    · ileft; ipureintro; exact h0
    · have h : t = p'.Term' := Ht.resolve_left h0
      subst h
      iright; iexists p'.Commit'
      iframe Hcw; ipureintro; exact Hn

/-- (D43 M3, 2026-10-25) A batch has a `ConfChange` entry (raft.go's `confChanged` scan). -/
def ccIn [FfiSyntax] (ce : List EntryModel) : Bool := ce.any (fun m => decide (m.typ = W32 1))

/-- (D43 M3) The driver's view goes to the apply thread with the batch `ce`: raft's dynamic mode
and a conf entry in it (the apply thread applies it; the second `notifyc` send brings the view
back). -/
def rnHands (γ : RNNames) (ce : List EntryModel) : Bool := γ.node.mode.isDyn && ccIn ce

/-- (D43 M3) What the apply thread's `notifyc` receive deposits: the view after the batch, if it
went along. -/
def rnApR (γ : RNNames) (F ce : List EntryModel) : IProp GF :=
  if rnHands γ ce then rnCfgAt γ (F ++ ce) else iprop(True)

/-- (D43 M3) What goes along with the batch: the view after `F` and the committed log handed out
through the batch (`dlvLb`), if `rnHands`. -/
def rnApGive (γ : RNNames) (F ce : List EntryModel) : IProp GF :=
  if rnHands γ ce then iprop(rnCfgAt γ F ∗ dlvLb γ.node (rnLogOf γ (F ++ ce))) else iprop(True)

/-- The `i`th payload on `applyc`: the log `F` forwarded before it (`cum[i]`) and the batch
`ce` it extends it with (`cum[i + 1] = F ++ ce`, committed), no snapshot, and its two channels;
and (2026-10-14, unit C2a) the committed index at least the batch's last index (`committedLast`:
`updateCommittedIndex` raised it before the send); and (D22 S-b) its raft term (`rnRtOk`). -/
def rnApP (E : RNEnv GF) (γ : RNNames) (i : Int) (ap : toApply) : IProp GF :=
  iprop(∃ (F ce : List EntryModel) (ceL : List Loc),
    monoListIdxOwn γ.cum i.toNat F ∗ monoListIdxOwn γ.cum (i.toNat + 1) (F ++ ce) ∗
    ap.entries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (F ++ ce) ∗ ⌜ap.snapshot' = null⌝ ∗
    -- (D43 M3, 2026-10-25) `notifyc`, with the receive's right: the receive deposits `rnApR`
    (∃ γnc : NotifyNames, isNotify γnc ap.notifyc' (rnApR γ F ce) ∗ notifyRcv γnc) ∗
    -- (D43 M3) a batch the driver's view goes with (`rnHands`): the view after `F`
    rnApGive γ F ce ∗
    -- (D19i part 1) closed once `Advance` returned: the storage's floor past the batch
    rnAdvChan ap.raftAdvancedC' (memFloorAtLeast γ.ms γ.γs (γ.pre ++ F ++ ce).length) ∗
    committedLast E.γr ce ∗
    -- (D22 S-b) the raft term it carries; (D22l) whose witness's commit index bounds the batch
    rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length)

/-- (D22 S-b) A batch's raft term, read off its payload (for `applyAll`'s merged snapshot); (D22l)
with the batch's log `F ++ ce` (`cum`'s element `i + 1`) within its witness's commit index. -/
theorem rnApP_rtOk (E : RNEnv GF) (γ : RNNames) (i : Int) (ap : toApply) :
    ⊢ rnApP E γ i ap -∗ rnApP E γ i ap ∗ ∃ (F ce : List EntryModel),
      monoListIdxOwn γ.cum (i.toNat + 1) (F ++ ce) ∗
      rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length := by
  iintro H
  iunfold rnApP at H
  icases H with ⟨%F, %ce, %ceL, #H1, #H2, #H3, #H4, #H5, %H6, H7, HG, #H8, #H9, #Hrt⟩
  isplitl [H7 HG]
  · iunfold rnApP
    iexists F, ce, ceL
    iframe H1 H2 H3 H4 H5 H7 HG H8 H9 Hrt
    ipureintro; exact H6
  iexists F, ce
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
half, and `cum`'s authority, one element per payload sent after the first, ending at `L`. -/
def rnLoopTokP (γ : RNNames) (L : List EntryModel) (p : HardStateM) : IProp GF :=
  iprop(∃ (sent : List toApply) (cums : List (List EntryModel)),
    rnDrv γ L p ∗ spscProducer γ.ap sent ∗ monoListAuthOwn γ.cum 1 cums ∗
    ⌜cums.length = sent.length + 1 ∧ cums.getLast? = some L⌝)

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
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Loc) (rnSnapMsg γ.node))

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
    "#Hstc" ∷ rnStoppedAddr r ↦□ stc ∗ "#Hstci" ∷ isUnitBag stc ∗
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
