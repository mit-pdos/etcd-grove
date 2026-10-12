/-
The server's raft wrapper (`server/v3/etcdserver/raft.go`): the shared vocabulary of
`Spec/raftNode__*.lean`. Lean-first (no Rocq counterpart); the plan is `decisions.md`, "The
server's raft wrapper".

- **The environment** `E : RNEnv` is what the node contract is stated over: `C L`, "`L` is a
  prefix of the cluster's committed log"; `M m`, "raft may send the message `m`"; `T`, a tick's
  resource (node.go's term-budget credit).
- **The node** (`isRaftNodeIfc E γ n`, the `raft.Node` interface, a trust boundary shaped like
  node.go's verified specs, `Proof/go_etcd_io/raft/v3/InvNode.lean`): `Ready()` is a handshake
  channel whose payload `rnReadyP` carries the node's half of the delivered log `dlv` at `d`,
  its record `rof` of the `Ready`, and the `Ready`'s data (`rnReadyData`); the driver
  (`rnDrv γ L`, the other half of `dlv`) learns `d = L`, and is busy (`rnBusy`) until
  `Advance()`, which takes the append receipt of the `Ready`'s entries.
- **`applyc`** is an SPSC channel (`isSpsc`) of `toApply`s; the `k`th payload carries the
  mono-list `cum`'s elements `k` and `k + 1` (the log forwarded before and after it), so the
  consumer, at `cum[|received|] = A` (`rnApplyTok γ A`), learns that the batch extends `A`. The
  loop (`rnLoopTok γ L`) owns the producer half and `cum`'s authority, whose last element is
  the node's delivered log `L`.
- **The other components** are persistent predicates of triples (the WAL, the
  `MemoryStorage`, the transport, the timeout detector, the ready handler's closures, the
  ticker), and the wrapper's fields are read-only after `start` but `latestTickTs`, under
  `tickMu` (`rnTickInv`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg
public import Perennial.Golang.Theory.Chan.Idioms.Idioms
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

instance entryModel_countable : Pos.Countable EntryModel :=
  .ofInjective (fun m => Pos.Countable.encode (((m.term, m.index), m.typ), m.data))
    (fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
      rfl)

section countable
variable [FfiSyntax]

instance ready_countable : Pos.Countable Ready :=
  countableOfLeftInverse
    (fun r : Ready => (r.SoftState', r.HardState', r.ReadStates', r.Entries', r.Snapshot',
      r.CommittedEntries', r.Messages', r.MustSync'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance toApply_countable : Pos.Countable toApply :=
  countableOfLeftInverse (fun a : toApply => (a.entries', a.snapshot', a.notifyc', a.raftAdvancedC'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

instance readState_countable : Pos.Countable ReadState :=
  countableOfLeftInverse (fun r : ReadState => (r.Index', r.RequestCtx'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

end countable

/-- The ghost names of a raft wrapper: the node's `Ready` channel, its delivered log `dlv`
(halves: the node's, the driver's), its record of the last `Ready` `rof`, the append right
and receipt `app`; `applyc`'s SPSC names and the mono-list `cum` of the log forwarded after
each payload. -/
structure RNNames where
  readyc : ChanNames
  dlv : GName
  rof : GName
  app : GName
  ap : SpscNames
  cum : GName

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

/-- A message the node handed out, as the wrapper reads and forwards it (persistent). -/
def rnMsgOk (E : RNEnv GF) (m : Loc) : IProp GF :=
  iprop(∃ (to : w64) (ty : w32), msgAt m to ty ∗ □ E.M m)

instance rnMsgOk_persistent (E : RNEnv GF) (m : Loc) : Persistent (rnMsgOk E m) := by
  unfold rnMsgOk; infer_instance

/-! ## The node's `Ready`/`Advance` exchange -/

/-- The right to append `es` to the `MemoryStorage` (from a `Ready`). -/
def appendRight (γ : RNNames) (es : List EntryModel) : IProp GF :=
  dghostVar γ.app (DFrac.own (1 : Qp).half) (es, false)

/-- The receipt of the append of `es` (for `Advance`). -/
def appendReceipt (γ : RNNames) (es : List EntryModel) : IProp GF :=
  dghostVar γ.app (DFrac.own (1 : Qp).half) (es, true)

/-- A `Ready`'s `SoftState`: nil, or a read-only struct. -/
def softStateAt (p : Loc) : IProp GF :=
  iprop(⌜p = null⌝ ∨ ∃ ss : SoftState, p ↦□ ss)

instance softStateAt_persistent (p : Loc) : Persistent (softStateAt (GF := GF) p) := by
  unfold softStateAt; infer_instance

/-- What a `Ready` gives the driver, after the committed log `d` handed out before it: the
committed entries `ce` to apply next (`C (d ++ ce)`), the entries `es` to append with the right
to, the messages, each one raft may send; a `SoftState`, a `HardState`; no snapshot and no read
states (as node.go's `readyData`). -/
def rnReadyData (E : RNEnv GF) (γ : RNNames) (rd : Ready) (d ce es : List EntryModel) :
    IProp GF :=
  iprop(∃ (ceL esL msL : List Loc) (hs : HardStateModel),
    rd.CommittedEntries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (d ++ ce) ∗
    rd.Entries' ↦*□ esL ∗ entriesAt esL es ∗ appendRight γ es ∗
    rd.Messages' ↦*□ msL ∗ ([∗list] m ∈ msL, rnMsgOk E m) ∗
    softStateAt rd.SoftState' ∗ hardStateAt rd.HardState' hs ∗
    ⌜rd.Snapshot' = null ∧ rd.ReadStates' = slice.nil⌝)

/-- A `Ready` on the node's channel: the node's half of `dlv` at `d`, its record's other half,
and the data. -/
def rnReadyP (E : RNEnv GF) (γ : RNNames) (rd : Ready) : IProp GF :=
  iprop(∃ (d ce es : List EntryModel),
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es) ∗ rnReadyData E γ rd d ce es)

/-- The driver, idle, handed the committed log `L` so far. -/
def rnDrv (γ : RNNames) (L : List EntryModel) : IProp GF :=
  dghostVar γ.dlv (DFrac.own (1 : Qp).half) L

/-- The driver with a `Ready` in hand, handed the committed log `d ++ ce`, to append `es`
before `Advance`. -/
def rnBusy (γ : RNNames) (d ce es : List EntryModel) : IProp GF :=
  iprop(dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es))

/-- **The `raft.Node` `n`** (trust boundary, see the file header): `Ready` returns the node's
handshake channel, `Advance` takes the busy driver and the append receipt, `Tick` a tick's
resource, `Stop` returns. -/
def isRaftNodeIfc (E : RNEnv GF) (γ : RNNames) (n : GoInterface) : IProp GF :=
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗
    □ ({{ True }} (App (Val #(methods ni.ty go!"Ready" ni.v)) (Val #()))
      {{ (ch : Loc), RET #ch; isHandshake (V := Ready) γ.readyc ch (rnReadyP E γ) iprop(True) }}) ∗
    □ (∀ (d ce es : List EntryModel),
      {{ rnBusy γ d ce es ∗ appendReceipt γ es }}
        (App (Val #(methods ni.ty go!"Advance" ni.v)) (Val #()))
      {{ RET #(); rnDrv γ (d ++ ce) }}) ∗
    □ ({{ E.T }} (App (Val #(methods ni.ty go!"Tick" ni.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ni.ty go!"Stop" ni.v)) (Val #())) {{ RET #(); True }}))

instance isRaftNodeIfc_persistent (E : RNEnv GF) (γ : RNNames) (n : GoInterface) :
    Persistent (isRaftNodeIfc E γ n) := by
  unfold isRaftNodeIfc; infer_instance

/-- Receiving a `Ready` (in the loop's `select`): the idle driver at `L` learns the payload's
`d` is `L`, and is busy with it. -/
theorem rn_ready_recv (E : RNEnv GF) (γ : RNNames) (L : List EntryModel) (rd : Ready) :
    rnDrv γ L -∗ rnReadyP E γ rd -∗
      ∃ ce es, rnReadyData E γ rd L ce es ∗ rnBusy γ L ce es := by
  iintro Hdrv HP
  unfold rnReadyP
  icases HP with ⟨%d, %ce, %es, Hd, Hrof, Hdata⟩
  unfold rnDrv
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hd Hdrv
  subst Heq
  iexists ce, es
  iframe Hdata
  unfold rnBusy
  iframe

/-! ## The other components -/

/-- **The `*raft.MemoryStorage` `ms`** (trust boundary: v3.7's raft is names-only): `Append`
of the `Ready`'s entries turns the right into the receipt. -/
def isRNMemStor (γ : RNNames) (ms : Loc) : IProp GF :=
  iprop(□ (∀ (sl : GoSlice) (esL : List Loc) (es : List EntryModel),
    {{ sl ↦*□ esL ∗ entriesAt esL es ∗ appendRight γ es }}
      (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #sl))
    {{ RET #(GoInterface.nil); appendReceipt γ es }}))

instance isRNMemStor_persistent (γ : RNNames) (ms : Loc) :
    Persistent (isRNMemStor (GF := GF) γ ms) := by
  unfold isRNMemStor; infer_instance

/-- **The WAL `st`** (`serverstorage.Storage`, trust boundary: names-only): `Save` of a hard
state and entries, and `Close`, return some error. -/
def isRNWal (st : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
        (es : List EntryModel),
      {{ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; True }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; True }}))

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

/-- **The ready handler `rh`** (the server's four closures, `run`): each returns. -/
def isReadyHandler (rh : Loc) : IProp GF :=
  iprop(∃ (gl ul uls uci : GoFunc),
    structFieldRef raftReadyHandler go!"getLead" rh ↦□ gl ∗
    structFieldRef raftReadyHandler go!"updateLead" rh ↦□ ul ∗
    structFieldRef raftReadyHandler go!"updateLeadership" rh ↦□ uls ∗
    structFieldRef raftReadyHandler go!"updateCommittedIndex" rh ↦□ uci ∗
    □ ({{ True }} (App (Val #gl) (Val #())) {{ (v : w64), RET #v; True }}) ∗
    □ (∀ v : w64, {{ True }} (App (Val #ul) (Val #v)) {{ RET #(); True }}) ∗
    □ (∀ b : Bool, {{ True }} (App (Val #uls) (Val #b)) {{ RET #(); True }}) ∗
    □ (∀ v : w64, {{ True }} (App (Val #uci) (Val #v)) {{ RET #(); True }}))

instance isReadyHandler_persistent (rh : Loc) : Persistent (isReadyHandler (GF := GF) rh) := by
  unfold isReadyHandler; infer_instance

/-- **The ticker `tk`** (Perennial models no `time.Ticker`): its `C` is a channel on which a
receive may yield some time, or nil (`newRaftNode`'s `&time.Ticker{}` when `heartbeat == 0`). -/
def isRNTicker (tk : Loc) : IProp GF :=
  iprop(∃ c : Loc, structFieldRef time.Ticker go!"C" tk ↦□ c ∗
    (⌜c = chan.nil⌝ ∨ ∃ γc : ChanNames, isChanBag γc c (V := time.Time) (fun _ => iprop(True))))

instance isRNTicker_persistent (tk : Loc) : Persistent (isRNTicker (GF := GF) tk) := by
  unfold isRNTicker; infer_instance

/-- `tickMu`'s resource: `latestTickTs`, a `q`-fraction. -/
def rnTickInv (r : Loc) (q : Qp) : IProp GF :=
  iprop(∃ t : time.Time, rnLatestTickTsAddr r ↦{DFrac.own q} t)

/-! ## `applyc` -/

/-- A unit channel with no logical content (`notifyc`, `raftAdvancedC`, `stopped`). -/
def isUnitBag (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := Unit) (fun _ => iprop(True)))

instance isUnitBag_persistent (c : Loc) : Persistent (isUnitBag (GF := GF) c) := by
  unfold isUnitBag; infer_instance

/-- The `i`th payload on `applyc`: the log `F` forwarded before it (`cum[i]`) and the batch
`ce` it extends it with (`cum[i + 1] = F ++ ce`, committed), no snapshot, and its two channels. -/
def rnApP (E : RNEnv GF) (γ : RNNames) (i : Int) (ap : toApply) : IProp GF :=
  iprop(∃ (F ce : List EntryModel) (ceL : List Loc),
    monoListIdxOwn γ.cum i.toNat F ∗ monoListIdxOwn γ.cum (i.toNat + 1) (F ++ ce) ∗
    ap.entries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (F ++ ce) ∗ ⌜ap.snapshot' = null⌝ ∗
    isUnitBag ap.notifyc' ∗ isUnitBag ap.raftAdvancedC')

/-- `applyc` (persistent): an SPSC channel of `rnApP` payloads, never closed. -/
def isRNApplyc (E : RNEnv GF) (γ : RNNames) (c : Loc) : IProp GF :=
  isSpsc γ.ap c (V := toApply) (rnApP E γ) (fun _ => iprop(True))

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

/-- `readStateC`: a channel of read states with no logical content. -/
def isRNReadStateC (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := ReadState) (fun _ => iprop(True)))

instance isRNReadStateC_persistent (c : Loc) : Persistent (isRNReadStateC (GF := GF) c) := by
  unfold isRNReadStateC; infer_instance

/-! ## The wrapper -/

/-- **The raft wrapper `r`** (persistent): its fields, read-only once started (`start`'s
comment), with their components; `latestTickTs` under `tickMu`. -/
def isRaftNode (E : RNEnv GF) (γ : RNNames) (r : Loc) : IProp GF :=
  iprop(∃ (lg mu ms td tk : Loc) (n st tr : GoInterface) (idr : GoFunc)
      (hb : time.Duration) (msc apc rsc stc dnc : GoChan),
    "#Hlg" ∷ rnLgAddr r ↦□ lg ∗ "%Hlgnn" ∷ ⌜lg ≠ null⌝ ∗
    "#Hmu" ∷ rnTickMuAddr r ↦□ mu ∗ "#Hmug" ∷ sync.isRWMutexGuard mu (rnTickInv r) ∗
    "#Hn" ∷ rnNodeAddr r ↦□ n ∗ "#Hni" ∷ isRaftNodeIfc E γ n ∗
    "#Hidr" ∷ rnIsIDRemovedAddr r ↦□ idr ∗ "#Hidri" ∷ isRNIDRemoved idr ∗
    "#Hms" ∷ rnRaftStorageAddr r ↦□ ms ∗ "#Hmsi" ∷ isRNMemStor γ ms ∗
    "#Hst" ∷ rnStorageAddr r ↦□ st ∗ "#Hsti" ∷ isRNWal st ∗
    "#Hhb" ∷ rnHeartbeatAddr r ↦□ hb ∗
    "#Htr" ∷ rnTransportAddr r ↦□ tr ∗ "#Htri" ∷ isRNTransport E tr ∗
    "#Hmsc" ∷ rnMsgSnapCAddr r ↦□ msc ∗
    "#Hmsci" ∷ isRNMsgSnapC E msc ∗
    "#Hapc" ∷ rnApplycAddr r ↦□ apc ∗ "#Hapci" ∷ isRNApplyc E γ apc ∗
    "#Hrsc" ∷ rnReadStateCAddr r ↦□ rsc ∗
    "#Hrsci" ∷ isRNReadStateC rsc ∗
    "#Htk" ∷ rnTickerAddr r ↦□ tk ∗ "#Htki" ∷ isRNTicker tk ∗
    "#Htd" ∷ rnTdAddr r ↦□ td ∗ "#Htdi" ∷ isRNTimeoutDetector td ∗
    "#Hstc" ∷ rnStoppedAddr r ↦□ stc ∗ "#Hstci" ∷ isUnitBag stc ∗
    "#Hdnc" ∷ rnDoneAddr r ↦□ dnc)



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
    ipureintro; exact Hlgnn

end defs

end EtcdGrove
end Perennial
