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
  (persistent, in `isRaftNode`): `E.T` raft's tick credit, `E.M` of a message raft handed out,
  `E.C` from the committed log (and back: the log prefix and the indices), `E.RQ` raft's read
  registration (`srvRQ`), and the names tied (`E.γr.raft.raft = γ.node.raft`, ...).
- **The node** (`isRaftNodeIfc E γ n`, the `raft.Node` interface, shaped like node.go's verified
  specs): `Ready()` is a handshake channel whose payload is raft's `readyP γ.node` (`rnReadyP`);
  the driver (`rnDrv γ L`, raft's `nodeDriver` at `pre ++ L`) learns the payload's log is `L`
  and is busy (`rnBusy`, raft's `nodeDriverBusy`) until `Advance()`, which takes the append
  receipt of the `Ready`'s entries (the `MemoryStorage`'s, `rnAppendReceipt`). Receiving a
  `Ready` (`rn_ready_recv`) derives the server's view of its data (`rnReadyData`: the messages
  persisted, `E.C` from the committed log) under the run's premises `rnLogFits` (every `Ready`'s
  entries fit `Append`'s index bound, and the committed index fits) and the read states' bridge
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
public import Perennial.Ghost.MonoList
public import Perennial.Proof.context.Base

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
  countableOfLeftInverse (fun a : toApply => (a.entries', a.snapshot', a.snapshotPersistedC',
      a.raftStorageReadyC', a.waitForStorageBeforeApply', a.applyCompletedC', a.raftAdvancedC',
      a.onApplyCompleted'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩) (fun _ => rfl)

/-- (etcd-io/etcd#22223) the append worker's queue element. -/
instance asyncAppendWork_countable : Pos.Countable asyncAppendWork :=
  countableOfLeftInverse (fun a : asyncAppendWork => (a.message', a.barrierC'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

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
-- (etcd-io/etcd#22223) the asynchronous-storage-writes switch and the storage responses' cancel
abbrev rnAsyncAddr (r : Loc) : Loc :=
  structFieldRef raftNodeConfig go!"asyncStorageWrites" (rnCfgAddr r)
abbrev rnCancelSRAddr (r : Loc) : Loc := structFieldRef raftNode go!"cancelStorageResponses" r

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

/-- A message the node handed out, as the wrapper reads and forwards it (persistent). -/
def rnMsgOk (E : RNEnv GF) (m : Loc) : IProp GF :=
  iprop(∃ (to : w64) (ty : w32), msgAt m to ty ∗ □ E.M m)

instance rnMsgOk_persistent (E : RNEnv GF) (m : Loc) : Persistent (rnMsgOk E m) := by
  unfold rnMsgOk; infer_instance

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
def rnReadyData (E : RNEnv GF) (γ : RNNames) (rd : Ready) (d ce es : List EntryModel) :
    IProp GF :=
  iprop(∃ (ceL esL msL : List Loc) (hs : HardStateModel),
    rd.CommittedEntries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (d ++ ce) ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗ rnAppendRight γ es ∗
    rd.Messages' ↦*□ msL ∗ ([∗list] m ∈ msL, rnMsgOk E m) ∗
    softStateAt rd.SoftState' ∗ hardStateAt rd.HardState' hs ∗
    (∃ rsL : List ReadState, rd.ReadStates' ↦*□ rsL ∗ [∗list] rs ∈ rsL, srvReadStateOk E.γr.raft E.RQ rs) ∗
    ⌜rd.Snapshot' = null⌝)

/-- A `Ready` on the node's channel: raft's payload (`readyP`; `E` unused, kept for the
statements' shape). -/
def rnReadyP (_E : RNEnv GF) (γ : RNNames) (rd : Ready) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  readyP γ.node rd

/-- The driver, idle, handed the committed log `L` so far: raft's `nodeDriver` at `pre ++ L`,
with the driver's view of the configuration (`nodeCfg`, which `Advance` takes and returns). -/
def rnDrv (γ : RNNames) (L : List EntryModel) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  iprop(nodeDriver γ.node γ.id γ.nl (rnLogOf γ L) ∗ ∃ (ca : Nat) (cfg : CCState), nodeCfg γ.node ca cfg)

/-- The driver with a `Ready` in hand, handed the committed log `d ++ ce`, to append `es`
before `Advance`: raft's `nodeDriverBusy`. -/
def rnBusy (γ : RNNames) (d ce es : List EntryModel) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  iprop(nodeDriverBusy γ.node γ.id γ.nl (rnLogOf γ (d ++ ce)) (es.map EntryModel.toM) ∗
    ∃ (ca : Nat) (cfg : CCState), nodeCfg γ.node ca cfg)

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
read registration. -/
def rnEnvOk (E : RNEnv GF) (γ : RNNames) : IProp GF :=
  iprop(⌜E.T = tickCred γ.node.bud 1⌝ ∗
    ⌜E.γr.raft.raft = γ.node.raft ∧ E.γr.raft.pre = γ.pre ∧
      uint.Z E.γr.raft.ai0 = γ.pre.length⌝ ∗
    ⌜γ.node.mode = RNMode.static ∧ γ.node.stor = memStorIface γ.ms⌝ ∗
    □ (∀ (m : Loc) (st : MsgSt), msgOwn m DFrac.discard st ∗ isRaftMsg γ.node.raft st ∗
        termLB γ.node.bud st.msg.Term' -∗ E.M m) ∗
    □ (∀ L : List EntryModel, srvRLogLb E.γr.raft L -∗
        ⌜uint.Z E.γr.raft.ai0 + 1 + L.length < 2 ^ 64⌝ ={⊤}=∗ □ E.C L) ∗
    □ (∀ L : List EntryModel, E.C L -∗ srvRLogLb E.γr.raft L ∗ ⌜srvIdxOk E.γr.raft.ai0 L⌝) ∗
    ⌜E.RQ = srvRQ E.γr.raft⌝)

instance rnEnvOk_persistent (E : RNEnv GF) (γ : RNNames) : Persistent (rnEnvOk E γ) := by
  unfold rnEnvOk; infer_instance

/-- **The run's premise on raft's `Ready`s** (persistent; a trust-boundary premise, D10): every
`Ready`'s entries fit `MemoryStorage.Append`'s index bound (raft's node layer cannot establish it
for the unstable entries it hands out; the register checks it in Go, etcd does not), and the
committed index it hands out has a successor (the next index fits a `uint64`: what the server's
`srvIdxOk` carries for the delivered log). -/
def rnLogFits (γ : RNNames) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  iprop(□ ∀ (rd : Ready) (d ce es : List EntryM) (ms : List QMsg),
    readyData γ.node rd d ce es ms -∗
      ⌜rnFits (es.map EntryModel.ofM) ∧ (d ++ ce).length + 1 < 2 ^ 64⌝ ∗
      readyData γ.node rd d ce es ms)

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
  icases Henv with ⟨-, %Hn, -, -, -, -, %HRQ⟩
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
    □ ({{ True }} (App (Val #(methods ni.ty go!"Ready" ni.v)) (Val #()))
      {{ (ch : Loc), RET #ch; isHandshake (V := Ready) γ.node.readyc ch (rnReadyP E γ) iprop(True) }}) ∗
    □ (∀ (d ce es : List EntryModel),
      {{ rnBusy γ d ce es ∗ rnAppendReceipt γ es }}
        (App (Val #(methods ni.ty go!"Advance" ni.v)) (Val #()))
      {{ RET #(); rnDrv γ (d ++ ce) }}) ∗
    □ ({{ E.T }} (App (Val #(methods ni.ty go!"Tick" ni.v)) (Val #())) {{ RET #(); True }}) ∗
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

/-- The messages a `Ready` hands out, persisted, each one `E.M` admits. -/
theorem rnMsgOk_of_raft (E : RNEnv GF) (γ : RNNames) :
    ∀ ms : List QMsg,
      ⊢ □ (∀ (m : Loc) (st : MsgSt), msgOwn m DFrac.discard st ∗ isRaftMsg γ.node.raft st ∗
          termLB γ.node.bud st.msg.Term' -∗ E.M m) -∗
        ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ.node.raft q.st ∗
          termLB γ.node.bud q.st.msg.Term') ={⊤}=∗
        [∗list] m ∈ ms.map QMsg.loc, rnMsgOk E m
  | [] => by
    iintro #HM -
    imodintro
    simp only [List.map_nil]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | q :: ms => by
    iintro #HM H
    icases (BigSepL.bigSepL_cons (Φ := fun _ (q : QMsg) => iprop(msgOwn (GF := GF) q.loc (readyDq q.st) q.st ∗
      isRaftMsg γ.node.raft q.st ∗ termLB γ.node.bud q.st.msg.Term'))).1 $$ H with ⟨⟨Hm, #Hrm, #Htl⟩, Hrest⟩
    imod msgOwn_persist_fupd q.loc _ q.st ⊤ $$ Hm with #Hm
    imod rnMsgOk_of_raft E γ ms $$ HM Hrest with #Hrest
    imodintro
    simp only [List.map_cons]
    iapply (BigSepL.bigSepL_cons (Φ := fun _ m => rnMsgOk (GF := GF) E m)).2
    iframe Hrest
    iunfold rnMsgOk
    iexists q.st.msg.To', q.st.msg.Type'
    isplitr
    · iunfold msgAt
      iexists q.st
      iframe Hm
      ipureintro; exact ⟨rfl, rfl⟩
    iintro !>
    iapply HM $$ %q.loc %q.st
    iframe Hm Hrm Htl

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
fit (`rnLogFits`), the read states answered (`rnReadStateBridge`); the read credits raft hands
out with its messages are dropped. -/
theorem rn_ready_recv (E : RNEnv GF) (γ : RNNames) (L : List EntryModel) (rd : Ready) :
    rnEnvOk E γ -∗ rnLogFits γ -∗ rnReadStateBridge E γ -∗ rnDrv γ L -∗ rnReadyP E γ rd ={⊤}=∗
      ∃ ce es, rnReadyData E γ rd L ce es ∗ rnBusy γ L ce es := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro #Henv #Hfits #Hbr Hdrv HP
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, %Hmode, #HM, #HC, -, -⟩
  obtain ⟨Hraft, Hpre, Hai0⟩ := Hn
  obtain ⟨-, Hstor⟩ := Hmode
  iunfold rnReadyP at HP
  iunfold readyP at HP
  icases HP with ⟨%d, %ce, %es, %ms, Hd, Hrof, Hdata, #Hlb⟩
  iunfold rnDrv at Hdrv
  icases Hdrv with ⟨Hdrv, Hcfg⟩
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨#Hnode, Hds, -⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hd Hds
  subst Heq
  iunfold rnLogFits at Hfits
  ihave ⟨%Hfit, Hdata⟩ := Hfits $$ %rd %(rnLogOf γ L) %ce %es %ms Hdata
  iunfold readyData at Hdata
  icases Hdata with ⟨#Hce, #Hcom, #Hes, Happ, Hmsgs, Hmo, -, ⟨%sts, #Hrs, #Hrsok⟩, ⟨%h, #Hhs⟩,
    #Hss, %Hsnap⟩
  icases entsPts_elim _ _ _ $$ Hce with ⟨%ceL, #HceL, #Hcero⟩
  icases entsPts_elim _ _ _ $$ Hes with ⟨%esL, #HesL, #Hesro⟩
  imod ownSlice_persist _ _ _ $$ Hmsgs with #Hmsgs
  imod rnMsgOk_of_raft E γ ms $$ HM Hmo with #Hmok
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
  iexists ce.map EntryModel.ofM, es.map EntryModel.ofM
  isplitl [Happ]
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
    · iunfold readStatesPts at Hrs
      icases Hrs with ⟨%vs, #Hvs, #Hrs2⟩
      iexists vs
      iframe Hvs
      iapply rnReadStates_of_raft E γ vs sts $$ Hbr Hrs2 Hrsok
    ipureintro; exact Hsnap
  · iunfold rnBusy
    iframe Hcfg
    iunfold nodeDriverBusy
    iframe Hnode
    rw [EntryModel.map_toM_ofM, rnLogOf_append, EntryModel.map_toM_ofM]
    isplitr
    · iunfold dlvLb; iexact Hlb
    iexists rnLogOf γ L, ce
    iframe Hd Hds Hrof
    ipureintro; rfl

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
      {{ RET #(GoInterface.nil); True }}))

instance isRNWal_persistent (st : GoInterface) : Persistent (isRNWal (GF := GF) st) := by
  unfold isRNWal; infer_instance

/-- **The transport `tr`** (`rafthttp.Transporter`, trust boundary: names-only): `Send` takes
the slice of messages, each one raft may send; `Stop` returns. -/
def isRNTransport (E : RNEnv GF) (tr : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tr = GoInterface.ok ti⌝ ∗
    □ (∀ (sl : GoSlice) (msL : List Loc),
      {{ sl ↦* msL ∗ [∗list] m ∈ msL, rnMsgOk E m }}
        (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #sl))
      {{ RET #(); True }}) ∗
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
stage R7b: raft's tick credit comes with the tick; "fewer than `2^64 - 1` ticks in a run" is the
ticker's premise), or nil (`newRaftNode`'s `&time.Ticker{}` when `heartbeat == 0`); `Stop`
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

/-- A unit channel with no logical content (`raftAdvancedC`, `stopped`). -/
def isUnitBag (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Unit) (fun _ => iprop(True)))

instance isUnitBag_persistent (c : Loc) : Persistent (isUnitBag (GF := GF) c) := by
  unfold isUnitBag; infer_instance

/-- **A legacy (`Ready`/`Advance`) payload's synchronization points** (etcd-io/etcd#22223, which
replaced the single `notifyc` by explicit channels): the apply side does not wait for storage
before applying (`waitForStorageBeforeApply = false`) and has no completion callback
(`onApplyCompleted = nil`); `raftStorageReadyC`, which the loop closes once the batch is
persisted and appended, is a broadcast channel the apply side may receive from (`.Unknown`);
`applyCompletedC`, which the apply side closes once done, comes with the right to close it
(`.Pending`; the loop keeps an `.Unknown` view to wait on it); `raftAdvancedC` a unit bag. No
payload carries a proposition: the ordering the channels enforce (persist, then snapshot; apply,
then a follower's send) is not modeled (as `notifyc` carried none before the PR), and the proofs,
of partial correctness, say nothing about the waits terminating. -/
def rnApChans (ap : toApply) : IProp GF :=
  iprop(⌜ap.waitForStorageBeforeApply' = false ∧ ap.onApplyCompleted' = func.nil⌝ ∗
    (∃ γc : ChanNames, ownBroadcastChan ap.raftStorageReadyC' γc iprop(True) .Unknown) ∗
    (∃ γc : ChanNames, ownBroadcastChan ap.applyCompletedC' γc iprop(True) .Pending) ∗
    isUnitBag ap.raftAdvancedC')

/-- The `i`th payload on `applyc`: the log `F` forwarded before it (`cum[i]`) and the batch
`ce` it extends it with (`cum[i + 1] = F ++ ce`, committed), no snapshot, and its channels
(`rnApChans`; etcd-io/etcd#22223); and (2026-10-14, unit C2a) the committed index at least the
batch's last index (`committedLast`: `updateCommittedIndex` raised it before the send). -/
def rnApP (E : RNEnv GF) (γ : RNNames) (i : Int) (ap : toApply) : IProp GF :=
  iprop(∃ (F ce : List EntryModel) (ceL : List Loc),
    monoListIdxOwn γ.cum i.toNat F ∗ monoListIdxOwn γ.cum (i.toNat + 1) (F ++ ce) ∗
    ap.entries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (F ++ ce) ∗ ⌜ap.snapshot' = null⌝ ∗
    rnApChans ap ∗ committedLast E.γr ce)

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
def rnLoopTok (γ : RNNames) (L : List EntryModel) : IProp GF :=
  iprop(∃ (sent : List toApply) (cums : List (List EntryModel)),
    rnDrv γ L ∗ spscProducer γ.ap sent ∗ monoListAuthOwn γ.cum 1 cums ∗
    ⌜cums.length = sent.length + 1 ∧ cums.getLast? = some L⌝)

/-- The apply side's ghost state: `applyc`'s consumer half, and `cum` at the number of
payloads received, the log `A` forwarded so far. -/
def rnApplyTok (γ : RNNames) (A : List EntryModel) : IProp GF :=
  iprop(∃ rcv : List toApply, spscConsumer γ.ap rcv ∗ monoListIdxOwn γ.cum rcv.length A)

/-- `msgSnapC`: a channel of messages raft may send. -/
def isRNMsgSnapC (E : RNEnv GF) (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Loc) (rnMsgOk E))

instance isRNMsgSnapC_persistent (E : RNEnv GF) (c : Loc) : Persistent (isRNMsgSnapC E c) := by
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
      (hb : time.Duration) (msc apc rsc stc dnc : GoChan) (csr : GoFunc)
      (γcsr : context.ContextNames),
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
    "#Hmsci" ∷ isRNMsgSnapC E msc ∗
    "#Hapc" ∷ rnApplycAddr r ↦□ apc ∗ "#Hapci" ∷ isRNApplyc E γ apc ∗
    "#Hrsc" ∷ rnReadStateCAddr r ↦□ rsc ∗
    "#Hrsci" ∷ isRNReadStateC E rsc ∗
    "#Htk" ∷ rnTickerAddr r ↦□ tk ∗ "#Htki" ∷ isRNTicker E tk ∗
    "#Htd" ∷ rnTdAddr r ↦□ td ∗ "#Htdi" ∷ isRNTimeoutDetector td ∗
    "#Hstc" ∷ rnStoppedAddr r ↦□ stc ∗ "#Hstci" ∷ isUnitBag stc ∗
    "#Hdnc" ∷ rnDoneAddr r ↦□ dnc ∗ "#Hdnci" ∷ ownBroadcastChan dnc γ.done iprop(True) .Unknown ∗
    -- (etcd-io/etcd#22223) asynchronous storage writes off: the loop takes the `Ready`/`Advance`
    -- path (raft's proofs cover synchronous writes only, `NewRawNode.spec`'s
    -- `AsyncStorageWrites = false`); the storage responses' cancel function returns
    "#Hasync" ∷ rnAsyncAddr r ↦□ false ∗
    "#Hcsr" ∷ rnCancelSRAddr r ↦□ csr ∗ "#Hcsri" ∷ context.cancelSpec csr γcsr iprop(True))

instance isRaftNode_persistent (E : RNEnv GF) (γ : RNNames) (r : Loc) :
    Persistent (isRaftNode E γ r) where
  persistent := by
    unfold isRaftNode
    iintro H
    iNamed H
    imodintro
    iexists lg, mu, ms, td, tk, n, st, tr, idr, hb, msc, apc, rsc, stc, dnc, csr, γcsr
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
