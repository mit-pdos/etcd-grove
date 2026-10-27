/-
etcd's linearizable read loop (`server/v3/etcdserver/read`, `read.go`, `util.go`): the shared
definitions of its specs. Lean-first (no Rocq counterpart); the request path's unit 4a
(2026-10-13); design: `notes/decisions.md`, "The read loop's notifier: deposited lower bounds".

**The protocol.** A client of `LinearizableReadNotify(ctx)` knows a lower bound `c` of the
cluster's committed index (`committedAtLeast γr c`) and must learn that the applied index has
passed it (`readIndexOk γr c`). It reads the current notifier `nc` (under `r.mux`'s read lock,
`readMuP`), signals the loop (`waitC`), and waits on `nc.c`. The loop swaps the notifier out (under
the write lock), then asks raft for the read index (`ReadIndex`, `ReadState`: an index at least the
cluster's committed index when raft served the request) and waits until the applied index reaches
it, then closes `nc.c`. A client's bound and the loop's request do not compare by themselves: the
client *deposits* `c` in the notifier's **need** (`γn`, a mono nat: the largest bound a client of
`nc` required) when it reads `nc`, with the read invariant (`readInv`) open; the read invariant
holds the current notifier's need's authority with a lower bound of the committed index at least
the need (the join of the clients' `committedAtLeast`); the loop, swapping `nc` out, takes them out
and freezes the need (`needFrozen`: the authority in an invariant of its own, since no client can
take `nc` any more), sends `ReadIndex` with that committed bound `n`, so the read state's index is
at least `n`, hence at least every deposited `c`. The close transfers `notified`: the error, and if
`nil` the frozen need and an applied index at least it.

**The contracts** (persistent; discharged for `*EtcdServer` and its `raftNode` in the request
path's unit 4b: `ReadServer.lean`, `ReadRaft.lean`, the server's `read_server`, `read_raft`):
`isReadServer srv γr LR NR` (the `server` interface: the stop, done, leader-change and
first-commit channels (`bcastChan`, closed and never sent on), the logger with the caller's
resource `LR` (the server's `lgMu` reader slot), the applied index's lower bound, `ApplyWait`'s
channel closed once the applied index reached the deadline, a request id for a resource `NR` (the
id budget, the server's premise) with its context's fresh token and a read credit (2026-10-16,
stage R7b: the server mints both from the id, `srvRdFreshInv`), the request timeout) and
`isReadRaft rf γr RQ` (the `raftInterface`: `ReadIndex`, with the fresh token and the credit,
registers a request id at a committed bound, `RQ id n`, and every read state on `ReadState()`'s
channel answers each registration of its id: `srvReadStateOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.read
public import Perennial.Golang.Theory.Chan.Idioms.Idioms
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopChan
public import Perennial.Proof.time
public import Perennial.Proof.encoding.binary
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A notifier's channel (`nc.c`). -/
abbrev ncCAddr (nc : Loc) : Loc := structFieldRef notifier go!"c" nc
/-- A notifier's error (`nc.err`). -/
abbrev ncErrAddr (nc : Loc) : Loc := structFieldRef notifier go!"err" nc
/-- The read loop's server (`r.server`). -/
abbrev readServerAddr (r : Loc) : Loc := structFieldRef go_etcd_io.etcd.server.v3.etcdserver.read.Read go!"server" r
/-- The read loop's raft (`r.raft`). -/
abbrev readRaftAddr (r : Loc) : Loc := structFieldRef go_etcd_io.etcd.server.v3.etcdserver.read.Read go!"raft" r
/-- The read loop's wake-up channel (`r.waitC`). -/
abbrev readWaitCAddr (r : Loc) : Loc := structFieldRef go_etcd_io.etcd.server.v3.etcdserver.read.Read go!"waitC" r

end addrs

/-! ## Request ids as bytes: `beBytes` (`InvRequest.lean`, since 2026-10-16, stage R7b: the read
contexts' mint, `srvRdFreshInv`, is stated over it) -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The notifiers -/

/-- The namespace of a swapped-out notifier's frozen need. -/
def readFrozenN : Namespace := nroot .@ "read_frozen"
/-- The namespace of the read invariant. -/
def readInvN : Namespace := nroot .@ "read_notifier"

/-- **The need `γn` is frozen at `n`** (persistent): its authority, in an invariant (no update can
happen any more: the notifier was swapped out, no client deposits in it). -/
def needFrozen (γn : NeedNames) (n : w64) : IProp GF :=
  inv readFrozenN (monoNatAuthOwn γn.need 1 (uint.nat n))

/-- **The clients' list of `γn` is frozen at `gs`** (persistent; 2026-10-14, unit T1): its
authority, in an invariant (the notifier was swapped out). -/
def listFrozen (γn : NeedNames) (gs : List GName) : IProp GF :=
  inv readFrozenN (monoListAuthOwn γn.list 1 gs)

/-- **The loop's answer to the clients of a notifier with names `γn`** (persistent): its need was
frozen at `n`, its clients' list at `gs`, the applied index has reached the read index `ci ≥ n`,
and (2026-10-14, unit T1) raft's witness of the round's read update at `ci` (`srvReadWit`: the
clients' results at every committed log through an index at least `ci`). -/
def frozenOk (γn : NeedNames) (γr : ReadNames) : IProp GF :=
  iprop(∃ (n ci ai : w64) (gs : List GName), needFrozen γn n ∗ listFrozen γn gs ∗
    appliedAtLeast γr ai ∗ ⌜uint.Z n ≤ uint.Z ci ∧ uint.Z ci ≤ uint.Z ai⌝ ∗
    srvReadWit γr.raft (readQs gs) ci)

/-- **What the close of a notifier `nc` tells every waiter** (persistent): its error, stored
before the close for good (`nc.err ↦□`), one the gRPC layer can take (`applyErrIs`), and, if
`nil`, the loop's answer (`frozenOk`). -/
def notified (nc : Loc) (γn : NeedNames) (γr : ReadNames) : IProp GF :=
  iprop(∃ err : GoInterface, ncErrAddr nc ↦□ err ∗ applyErrIs err ∗
    (⌜err ≠ GoInterface.nil⌝ ∨ frozenOk γn γr))

/-- **A channel closed (never sent on) whose close tells `Q`** (persistent; Perennial's broadcast
idiom, any receiver's view). -/
def bcastChan (ch : Loc) (Q : IProp GF) : IProp GF :=
  iprop(∃ γ : ChanNames, ownBroadcastChan ch γ Q .Unknown)

/-- **A channel closed (never sent on) whose close tells `Q`, or closed already** (persistent;
D19r (D), 2026-10-18): `bcastChan`, or a channel an invariant keeps closed with `□ Q` known
(`ApplyWait`'s answer when the deadline was already triggered: `pkg/wait`'s `closec`). -/
def bcastOrClosed (ch : Loc) (Q : IProp GF) : IProp GF :=
  iprop(bcastChan ch Q ∨
    (∃ γ : ChanNames, isChan ch γ Unit ∗
      inv _root_.Perennial.context.closedchanN (ownChan γ Unit (.Closed [])) ∗ □ Q))

instance bcastOrClosed_persistent (ch : Loc) (Q : IProp GF) :
    Persistent (bcastOrClosed (GF := GF) ch Q) := by
  unfold bcastOrClosed bcastChan; infer_instance

/-- **A receive from `bcastOrClosed`** returns, with `□ Q`. -/
theorem bcastOrClosed_receive (ch : Loc) (Q : IProp GF) :
    bcastOrClosed ch Q ⊢ ∃ γ : ChanNames, isChan ch γ Unit ∗
      □ (∀ Φ : Unit → Bool → IProp GF, (□ Q -∗ Φ () false) -∗ recvAu γ Unit Φ) := by
  iintro #H
  iunfold bcastOrClosed at H
  icases H with (#Hb | ⟨%γ, #Hc, #Hi, #HQ⟩)
  · iunfold bcastChan at Hb
    icases Hb with ⟨%γ, #Hb⟩
    iexists γ
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hb
    iintro !> %Φ HΦ
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hb
    iintro ⟨#HQ', -⟩
    iapply HΦ $$ HQ'
  · iexists γ
    iframe Hc
    iintro !> %Φ HΦ
    ihave HΦ' := HΦ $$ HQ
    unfold recvAu
    iinv Hi with Hst Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists .Closed []
    iframe Hst
    dsimp only
    iintro Hch
    imod Hmask with -
    imod Hclose $$ Hch with -
    imodintro
    iexact HΦ'

/-- **The notifier `nc` with need `γn`** (persistent; a waiter's view): its channel, closed with
`notified`. -/
def notifierIs (nc : Loc) (γn : NeedNames) (γr : ReadNames) : IProp GF :=
  iprop(∃ ch : Loc, ncCAddr nc ↦□ ch ∗ bcastChan ch (notified nc γn γr))

/-- **The right to notify `nc`** (the loop's, once it swapped `nc` out): the channel not closed
yet, and `nc.err` (written once, before the close). -/
def notifierOwn (nc : Loc) (γn : NeedNames) (γr : ReadNames) : IProp GF :=
  iprop(∃ (ch : Loc) (γ : ChanNames) (e : GoInterface), ncCAddr nc ↦□ ch ∗
    ownBroadcastChan ch γ (notified nc γn γr) .Pending ∗ ncErrAddr nc ↦ e)

/-- **The read invariant** (`γr.notifier`'s half; the lock's resource `readMuP` holds the other):
the current notifier `nc` and its need `γn` (its waiter's view and the right to notify it), the
need's authority `n`, and a lower bound of the committed index at least the need. The deposits at
the state function `F` (the auth plan's E3r, 2026-10-27; by default the auth mode `off`'s). -/
def readInv (γr : ReadNames) (F : List EntryModel → KVState := kvStOff γr.kv) : IProp GF :=
  inv readInvN iprop(∃ (nc : Loc) (γn : NeedNames) (n : w64) (gs : List GName),
    ghostVar γr.notifier (1 : Qp).half (nc, γn) ∗ notifierIs nc γn γr ∗ notifierOwn nc γn γr ∗
    monoNatAuthOwn γn.need 1 (uint.nat n) ∗ committedAtLeast γr n ∗
    monoListAuthOwn γn.list 1 gs ∗ [∗list] g ∈ gs, regOk γr.kv g F)

instance needFrozen_persistent (γn : NeedNames) (n : w64) : Persistent (needFrozen (GF := GF) γn n) := by
  unfold needFrozen; infer_instance
instance listFrozen_persistent (γn : NeedNames) (gs : List GName) :
    Persistent (listFrozen (GF := GF) γn gs) := by
  unfold listFrozen; infer_instance
instance frozenOk_persistent (γn : NeedNames) (γr : ReadNames) : Persistent (frozenOk (GF := GF) γn γr) := by
  unfold frozenOk; infer_instance
instance notified_persistent (nc : Loc) (γn : NeedNames) (γr : ReadNames) :
    Persistent (notified (GF := GF) nc γn γr) := by
  unfold notified; infer_instance
instance bcastChan_persistent (ch : Loc) (Q : IProp GF) : Persistent (bcastChan ch Q) := by
  unfold bcastChan; infer_instance
instance notifierIs_persistent (nc : Loc) (γn : NeedNames) (γr : ReadNames) :
    Persistent (notifierIs (GF := GF) nc γn γr) := by
  unfold notifierIs; infer_instance
instance readIndexOk_persistent_read (γr : ReadNames) (c : w64) :
    Persistent (readIndexOk (GF := GF) γr c) := by
  unfold readIndexOk; infer_instance
instance readInv_persistent (γr : ReadNames) (F : List EntryModel → KVState) :
    Persistent (readInv (GF := GF) γr F) := by
  unfold readInv; infer_instance

/-! ## The server, as the read loop sees it (`server`) -/

/-- The method `m` of the server value `si` returns a channel that is closed, never sent on, with
no content (the stop, done, leader-change and first-commit channels). -/
def srvChanOk (si : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ {{ True }} (App (Val #(methods si.ty m si.v)) (Val #()))
    {{ (ch : Loc), RET #ch; bcastChan ch iprop(True) }})

/-- The method `m` of the server value `si`, with the caller's resource `LR` (given back), returns
a channel that is closed, never sent on, with no content (the leader-change and first-commit
channels: `notify.Notifier.Receive` read-locks the notifier, so the caller holds a reader slot;
2026-10-13, the request path's unit 4b). -/
def srvChanOkR (si : GoInterfaceOk) (m : GoString) (LR : IProp GF) : IProp GF :=
  iprop(□ {{ LR }} (App (Val #(methods si.ty m si.v)) (Val #()))
    {{ (ch : Loc), RET #ch; bcastChan ch iprop(True) ∗ LR }})

/-- The method `m` of the server value `si` returns a buffered channel closed once, never sent on,
with no content (`stopChan`: the `stopping` channel, `make(chan struct{}, 1)`; 2026-10-13, the
request path's unit 4c: a broadcast channel, `bcastChan`, until then, which Perennial allocates only
unbuffered). -/
def srvStopOk (si : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ {{ True }} (App (Val #(methods si.ty m si.v)) (Val #()))
    {{ (ch : Loc), RET #ch; stopChan ch }})

/-- **The server's `Done()`** (persistent; what `LinearizableReadNotify` needs of the server). -/
def srvDoneOk (srv : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜srv = GoInterface.ok si⌝ ∗ srvChanOk si go!"Done")

/-- **The `server` interface value `srv`** (persistent; unit 4b discharges it for `*EtcdServer`):
* `Done()`, `Stopping()`, `LeaderChanged()`, `FirstCommitInTermNotify()`: channels closed, never
  sent on, with no content (`bcastChan`; `Stopping()`'s buffered, `stopChan`: 2026-10-13, unit 4c);
  the last two with the caller's resource `LR` (given back: they read-lock a notifier; 2026-10-13,
  unit 4b);
* `Logger()`: a non-nil `*zap.Logger`, for the caller's resource `LR` (the server's `lgMu` reader
  slot: `EtcdServer.Logger` read-locks it; and the two notifiers' reader slots), given back;
* `AppliedIndex()`: an index the applied index has reached (`appliedAtLeast`);
* `ApplyWait(d)`: a channel closed once the applied index has reached `d`: its close tells some `Q`
  from which `appliedAtLeast γr d` follows (2026-10-13, unit 4b: `WaitTime.Wait` returns the
  package's `closec`, closed with nothing, when `d` was already triggered);
* `NextRequestID()`: an id, for a resource `NR` (the id generator's credit: the id budget, the
  server's premise; the loop asks for one per `ReadIndex` request, unboundedly), with (2026-10-16,
  stage R7b) the fresh token of the id's context (raft's `rdFresh`, `srvRdFresh`) and one of
  raft's read credits (`srvRdCred`): the server mints both from the id (`srvRdFresh_mint`), so
  raft's read budget is paid by the id budget, one `ReadIndex` per id;
* `RequestTimeout()`: some duration. -/
def isReadServer (srv : GoInterface) (γr : ReadNames) (LR NR : IProp GF) : IProp GF :=
  iprop(srvDoneOk srv ∗ ∃ si : GoInterfaceOk, ⌜srv = GoInterface.ok si⌝ ∗
    srvStopOk si go!"Stopping" ∗ srvChanOkR si go!"LeaderChanged" LR ∗
    srvChanOkR si go!"FirstCommitInTermNotify" LR ∗
    □ ({{ LR }} (App (Val #(methods si.ty go!"Logger" si.v)) (Val #()))
      {{ (l : Loc), RET #l; ⌜l ≠ null⌝ ∗ LR }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"AppliedIndex" si.v)) (Val #()))
      {{ (i : w64), RET #i; appliedAtLeast γr i }}) ∗
    □ (∀ d : w64, {{ True }} (App (Val #(methods si.ty go!"ApplyWait" si.v)) (Val #d))
      {{ (ch : Loc), RET #ch; ∃ Q : IProp GF, bcastOrClosed ch Q ∗ □ (Q -∗ appliedAtLeast γr d) }}) ∗
    □ ({{ NR }} (App (Val #(methods si.ty go!"NextRequestID" si.v)) (Val #()))
      {{ (id : w64), RET #id; srvRdFresh γr.raft (beBytes id) ∗ srvRdCred γr.raft }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"RequestTimeout" si.v)) (Val #()))
      {{ (d : _root_.Perennial.time.Duration), RET #d; True }}))

instance srvChanOk_persistent (si : GoInterfaceOk) (m : GoString) :
    Persistent (srvChanOk (GF := GF) si m) := by
  unfold srvChanOk; infer_instance
instance srvChanOkR_persistent (si : GoInterfaceOk) (m : GoString) (LR : IProp GF) :
    Persistent (srvChanOkR (GF := GF) si m LR) := by
  unfold srvChanOkR; infer_instance
instance srvStopOk_persistent (si : GoInterfaceOk) (m : GoString) :
    Persistent (srvStopOk (GF := GF) si m) := by
  unfold srvStopOk; infer_instance
instance srvDoneOk_persistent (srv : GoInterface) : Persistent (srvDoneOk (GF := GF) srv) := by
  unfold srvDoneOk; infer_instance
instance isReadServer_persistent (srv : GoInterface) (γr : ReadNames) (LR NR : IProp GF) :
    Persistent (isReadServer srv γr LR NR) := by
  unfold isReadServer; infer_instance

/-! ## Raft, as the read loop sees it (`raftInterface`) -/

/-- **A read state `rs` on raft's `ReadState()` channel** (persistent): its request context,
read-only, a context deposited with raft (`srvCtxDeposited`; 2026-10-16, stage R7b: until then
`⌜bs.length = 8⌝`, which raft's read states do not carry; the loop derives it, `readCtxMinted`:
every deposited context is a minted `beBytes id`), and its index answers every registration of
the id they encode: a request `ReadIndex` registered at a committed bound `n` with the read update
of result `Qr` (`RQ id n Qr`) has `n ≤ rs.Index`, and (2026-10-14, unit T1) raft's witness of the
update at the read index (`srvReadWit γ Qr rs.Index`). -/
def srvReadStateOk (γ : ServerRaftNames) (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF)
    (rs : go_etcd_io.raft.v3.ReadState) : IProp GF :=
  iprop(∃ bs : List w8, rs.RequestCtx' ↦*□ bs ∗ srvCtxDeposited γ bs ∗
    □ (∀ (id n : w64) (Qr : List EntryModel → IProp GF), ⌜bs = beBytes id⌝ -∗ RQ id n Qr -∗
      ⌜uint.Z n ≤ uint.Z rs.Index'⌝ ∗ srvReadWit γ Qr rs.Index'))

/-- **`ReadState()`'s channel** (persistent): a bag channel of read states, each `srvReadStateOk`
(the raft wrapper's `readStateC`, `isRNReadStateC` with content). -/
def isReadStateC (c : Loc) (γ : ServerRaftNames)
    (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ γc : ChanNames, isChanBag γc c (V := go_etcd_io.raft.v3.ReadState) (srvReadStateOk γ RQ))

/-- **The `raftInterface` value `rf`** (persistent; unit 4b discharges it for the server's
`raftNode`, as `raftPropose`): `ReadState()` returns a channel of answered read states
(`isReadStateC`); `ReadIndex(ctx, rctx)`, with the big-endian bytes of an id read-only and a
lower bound `n` of the committed index, returns an error the gRPC layer can take, and if `nil` the
registration `RQ id n` (persistent). Sound of raft, given the request path's premise that request
ids do not repeat within the process (the `2^48` budget): a read state's index is the leader's
commit index when it served the request, at least every index committed cluster-wide by then; a
repeated id would let an old read state answer a new request's bound. -/
def isReadRaft (rf : GoInterface) (γr : ReadNames)
    (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rf = GoInterface.ok ri⌝ ∗
    □ ({{ True }} (App (Val #(methods ri.ty go!"ReadState" ri.v)) (Val #()))
      {{ (c : Loc), RET #c; isReadStateC c γr.raft RQ }}) ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice)
        (id n : w64) (Qr : List EntryModel → IProp GF),
      {{ context.isContext ctx cd ∗ sl ↦*□ beBytes id ∗ committedAtLeast γr n ∗
          srvReadAu γr.raft Qr ∗
          -- (2026-10-16, stage R7b) raft's read credit and the context's fresh token
          srvRdCred γr.raft ∗ srvRdFresh γr.raft (beBytes id) }}
        (App (App (Val #(methods ri.ty go!"ReadIndex" ri.v)) (Val #(GoInterface.ok ctx)))
          (Val #sl))
      {{ (err : GoInterface), RET #err; applyErrIs err ∗
          (⌜err = GoInterface.nil⌝ -∗ □ RQ id n Qr) }}))

instance srvReadStateOk_persistent (γ : ServerRaftNames)
    (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF)
    (rs : go_etcd_io.raft.v3.ReadState) : Persistent (srvReadStateOk (GF := GF) γ RQ rs) := by
  unfold srvReadStateOk; infer_instance
instance isReadStateC_persistent (c : Loc) (γ : ServerRaftNames)
    (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF) :
    Persistent (isReadStateC (GF := GF) c γ RQ) := by
  unfold isReadStateC; infer_instance
instance isReadRaft_persistent (rf : GoInterface) (γr : ReadNames)
    (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF) :
    Persistent (isReadRaft rf γr RQ) := by
  unfold isReadRaft; infer_instance

/-- **One read update for a list of clients** (persistent; 2026-10-14, unit T1; the server's
`kv_read_compose`, from its KV invariant): the round's update, of the clients' results. -/
def readCompose (γr : ReadNames) (F : List EntryModel → KVState := kvStOff γr.kv) : IProp GF :=
  iprop(□ ∀ gs : List GName, ([∗list] g ∈ gs, regOk γr.kv g F) -∗ srvReadAu γr.raft (readQs gs))

instance readCompose_persistent (γr : ReadNames) (F : List EntryModel → KVState) :
    Persistent (readCompose (GF := GF) γr F) := by
  unfold readCompose; infer_instance

/-- **Every context raft registered is a minted one** (persistent; 2026-10-16, stage R7b; the
read loop's view of the read contexts' mint, `srvRdFreshInv`, which the server's composition
proves from it, `readCtxMinted_of_mint`): a deposited context (`srvCtxDeposited`, what a read
state carries) is the big-endian bytes of a request id, so eight bytes long: `read.go`'s
`len(rs.RequestCtx) == 8` guard never fails. -/
def readCtxMinted (γr : ReadNames) : IProp GF :=
  iprop(□ ∀ c : List w8, srvCtxDeposited γr.raft c ={⊤}=∗ ⌜∃ id : w64, c = beBytes id⌝)

instance readCtxMinted_persistent (γr : ReadNames) : Persistent (readCtxMinted (GF := GF) γr) := by
  unfold readCtxMinted; infer_instance

/-- `readCtxMinted` from the mint (`srvCtxDeposited_minted`). (2026-10-27: the read contexts'
mint keeps the committed contexts itself; until then also raft's commit invariant.) -/
theorem readCtxMinted_of_mint (γr : ReadNames) (γi : IdNames) :
    srvRdFreshInv (GF := GF) γr.raft γi ∗ srvRaftLogInv γr.raft ⊢ readCtxMinted γr := by
  iintro ⟨#Hm, -⟩
  iunfold readCtxMinted
  iintro !> %c #Hd
  iapply srvCtxDeposited_minted γr.raft γi c $$ Hm Hd

/-! ## The `*Read` -/

/-- **What `LinearizableReadNotify` needs of `r`** (persistent): the server's `Done()`, the
wake-up channel (a bag of `struct{}`), the read invariant. -/
def isReadPre (r : Loc) (γr : ReadNames) (F : List EntryModel → KVState := kvStOff γr.kv) :
    IProp GF :=
  iprop(∃ (srv : GoInterface) (wc : Loc) (γw : ChanNames),
    readServerAddr r ↦□ srv ∗ srvDoneOk srv ∗
    readWaitCAddr r ↦□ wc ∗ isChanBag γw wc (V := Unit) (fun _ => iprop(True)) ∗
    readInv γr F)

/-- **What `LinearizableReadLoop` needs of `r`** (persistent; `NewRead`'s result, with `isReadNotify`):
the two contracts (`isReadServer` with the logger's resource `LR` and the id resource `NR`;
`isReadRaft` with the registrations `RQ`), the wake-up channel, the read invariant, the write
side of `r.mux` (`sync.isRWMutexGuard`), `context`'s ghost fact (`closedchan` closed: what
`sendReadIndex`'s `context.WithTimeout` of `Background()` needs), the clients' read update
(`readCompose`) and (2026-10-16, stage R7b) the minted contexts (`readCtxMinted`). -/
def isReadLoopPre (r : Loc) (γr : ReadNames)
    (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF) (LR NR : IProp GF)
    (F : List EntryModel → KVState := kvStOff γr.kv) : IProp GF :=
  iprop(∃ (srv rf : GoInterface) (wc : Loc) (γw : ChanNames),
    readServerAddr r ↦□ srv ∗ isReadServer srv γr LR NR ∗
    readRaftAddr r ↦□ rf ∗ isReadRaft rf γr RQ ∗
    readWaitCAddr r ↦□ wc ∗ isChanBag γw wc (V := Unit) (fun _ => iprop(True)) ∗
    readInv γr F ∗ sync.isRWMutexGuard (readMuAddr r) (readMuP r γr) ∗ context.isClosedchanInit ∗
    readCompose γr F ∗ readCtxMinted γr)

instance isReadPre_persistent (r : Loc) (γr : ReadNames) (F : List EntryModel → KVState) :
    Persistent (isReadPre (GF := GF) r γr F) := by
  unfold isReadPre; infer_instance
instance isReadLoopPre_persistent (r : Loc) (γr : ReadNames)
    (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF)
    (LR NR : IProp GF) (F : List EntryModel → KVState) :
    Persistent (isReadLoopPre r γr RQ LR NR F) := by
  unfold isReadLoopPre; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The lock's resource is fractional (for `sync.init_RWMutex`): the points-to and the ghost
variable split, two parts agree on the notifier and its need. -/
instance readMuP_fractional (r : Loc) (γr : ReadNames) : Fractional (readMuP (GF := GF) r γr) where
  fractional q1 q2 := by
    have hpt : ∀ v : Loc, (readNotifierAddr r ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
        readNotifierAddr r ↦{DFrac.own q1} v ∗ readNotifierAddr r ↦{DFrac.own q2} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1)
        (DFrac.own q2)
    have hgv := fun (x : Loc × NeedNames) =>
      (ghostVar_fractional (GF := GF) γr.notifier x).fractional q1.half q2.half
    unfold readMuP
    rw [Qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro ⟨%nc, %γn, Hp, Hg⟩
      icases (hpt nc).1 $$ Hp with ⟨Hp1, Hp2⟩
      icases (hgv (nc, γn)).1 $$ Hg with ⟨Hg1, Hg2⟩
      isplitl [Hp1 Hg1]
      · iexists nc, γn; iframe Hp1 Hg1
      · iexists nc, γn; iframe Hp2 Hg2
    · iintro ⟨⟨%nc, %γn, Hp1, Hg1⟩, ⟨%nc2, %γn2, Hp2, Hg2⟩⟩
      ihave %Hag := ghostVar_agree γr.notifier _ _ _ _ $$ Hg1 Hg2
      cases Hag
      iexists nc, γn
      isplitl [Hp1 Hp2]
      · iapply (hpt nc).2; iframe Hp1 Hp2
      · iapply (hgv (nc, γn)).2; iframe Hg1 Hg2

/-! ## The ghost steps -/

/-- **A client's deposit** (`LinearizableReadNotify`, holding the read lock's ghost fraction of the
current notifier `nc` with names `γn`): the client's bound `c` raises the need (the read invariant
keeps a committed lower bound at least the need: the larger of the two bounds), and (2026-10-14,
unit T1) the client's result predicate `Q` (a saved predicate at `g`) and deposit are appended to
the notifier's clients' list; the client gets a lower bound of the need, its position `k` in the
list and the notifier's waiters' view. -/
theorem read_need_deposit (γr : ReadNames) (q : Qp) (nc : Loc) (γn : NeedNames) (c : w64) (g : GName)
    (Q : List EntryModel → IProp GF) (F : List EntryModel → KVState) :
    ⊢ readInv (GF := GF) γr F -∗ £ 1 -∗ ghostVar γr.notifier q (nc, γn) -∗ committedAtLeast γr c -∗
      savedPredOwn g DFrac.discard Q -∗ kvDep γr.kv Q F
      ={⊤}=∗ ghostVar γr.notifier q (nc, γn) ∗ notifierIs nc γn γr ∗
        monoNatLbOwn γn.need (uint.nat c) ∗ ∃ k : Nat, monoListIdxOwn γn.list k g := by
  iintro #Hinv Hlc Hg #Hc #HQ #HD
  iunfold readInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑readInvN) $$ Hlc Hi with Hi
  icases Hi with ⟨%nc', %γn', %n, %gs, Hg', #His, Hown, Hauth, #Hn, Hlist, #Hregs⟩
  ihave %Hag := ghostVar_agree γr.notifier _ _ _ _ $$ Hg Hg'
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  imod monoListAuthOwn_update_app [g] $$ Hlist with ⟨Hlist, #Hllb⟩
  ihave #Hidx : iprop(monoListIdxOwn γn.list gs.length g) $$ []
  · iapply monoListIdxOwn_get gs.length g (by simp) $$ Hllb
  ihave #Hregs' : iprop([∗list] g' ∈ gs ++ [g], regOk γr.kv g' F) $$ []
  · iapply BigSepL.bigSepL_snoc.2
    iframe Hregs
    iunfold regOk
    iexists Q
    iframe HQ HD
  by_cases hle : uint.Z c ≤ uint.Z n
  · ihave #Hlb := monoNatLbOwn_get γn.need 1 _ $$ Hauth
    imod Hclose $$ [Hg' Hown Hauth Hlist] with -
    · inext; iexists nc, γn, n, gs ++ [g]; iframe Hg' His Hown Hauth Hn Hlist Hregs'
    imodintro
    iframe Hg His
    isplitl []
    · iapply monoNatLbOwn_le (uint.nat c) (by word) $$ Hlb
    iexists gs.length; iexact Hidx
  · imod mono_nat_own_update (uint.nat c) (by word) $$ Hauth with ⟨Hauth, #Hlb⟩
    imod Hclose $$ [Hg' Hown Hauth Hlist] with -
    · inext; iexists nc, γn, c, gs ++ [g]; iframe Hg' His Hown Hauth Hc Hlist Hregs'
    imodintro
    iframe Hg His Hlb
    iexists gs.length; iexact Hidx

/-- A frozen need bounds every lower bound of it. -/
theorem needFrozen_le (γn : NeedNames) (n : w64) (m : Nat) :
    ⊢ needFrozen (GF := GF) γn n -∗ monoNatLbOwn γn.need m ={⊤}=∗ ⌜m ≤ uint.nat n⌝ := by
  iintro #Hf #Hlb
  iunfold needFrozen at Hf
  iinv Hf with Ha Hclose
  icases Ha with >Ha
  ihave %h := monoNatLbOwn_valid γn.need 1 _ _ $$ Ha Hlb
  imod Hclose $$ [Ha] with -
  · inext; iexact Ha
  imodintro
  ipureintro
  exact h.2

/-- **The loop's answer, for a client of the notifier** whose bound `c` is in the need: the
applied index reached an index at least `c`. -/
theorem read_frozenOk_readIndexOk (γn : NeedNames) (γr : ReadNames) (c : w64) :
    ⊢ frozenOk (GF := GF) γn γr -∗ monoNatLbOwn γn.need (uint.nat c) ={⊤}=∗ readIndexOk γr c := by
  iintro #Hfz #Hlb
  iunfold frozenOk at Hfz
  icases Hfz with ⟨%n, %ci, %i, %gs, #Hf, -, #Hi, %Hni, -⟩
  imod needFrozen_le γn n (uint.nat c) $$ Hf Hlb with %hcn
  imodintro
  iunfold readIndexOk
  iexists i
  iframe Hi
  ipureintro
  have := Hni.1; have := Hni.2
  word

/-- **The loop's answer, for a client registered at position `k`** (2026-10-14, unit T1): the
read served (`readServed`): the client is in the frozen list of the round, whose read index is at
least the client's bound. -/
theorem read_frozenOk_served (γn : NeedNames) (γr : ReadNames) (c : w64) (k : Nat) (g : GName) :
    ⊢ frozenOk (GF := GF) γn γr -∗ monoNatLbOwn γn.need (uint.nat c) -∗
      monoListIdxOwn γn.list k g ={⊤}=∗ readServed γr c g := by
  iintro #Hfz #Hlb #Hidx
  iunfold frozenOk at Hfz
  icases Hfz with ⟨%n, %ci, %ai, %gs, #Hf, #Hlf, #Hi, %Hni, #Hw⟩
  imod needFrozen_le γn n (uint.nat c) $$ Hf Hlb with %hcn
  iunfold listFrozen at Hlf
  iinv Hlf with >Ha Hclose
  ihave %Hk := mono_list_auth_idx_lookup γn.list 1 gs k g $$ Ha Hidx
  imod Hclose $$ [Ha] with -
  · inext; iexact Ha
  imodintro
  iunfold readServed
  iexists ci, ai, gs, k
  iframe Hi Hw
  ipureintro
  have := Hni.1
  exact ⟨by word, Hni.2, Hk⟩

/-- **The loop's swap** (`LinearizableReadLoop`, holding the write lock's ghost half of the current
notifier `nc` with names `γn`, swapping in the new notifier `nc'` with names `γn'`, its need at `0`
and its list empty): the read invariant takes `nc'`; the loop gets the right to notify `nc`, its
need frozen at `n` (no client can deposit in it any more), a lower bound `n` of the committed
index, and (2026-10-14, unit T1) its clients' list frozen at `gs` with their deposits. -/
theorem read_swap (γr : ReadNames) (nc : Loc) (γn : NeedNames) (nc' : Loc) (γn' : NeedNames)
    (F : List EntryModel → KVState) :
    ⊢ readInv (GF := GF) γr F -∗ £ 1 -∗ ghostVar γr.notifier (1 : Qp).half (nc, γn) -∗
      notifierIs nc' γn' γr -∗ notifierOwn nc' γn' γr -∗ monoNatAuthOwn γn'.need 1 0 -∗
      monoListAuthOwn γn'.list 1 ([] : List GName) ={⊤}=∗
      ghostVar γr.notifier (1 : Qp).half (nc', γn') ∗ notifierOwn nc γn γr ∗
      ∃ (n : w64) (gs : List GName), needFrozen γn n ∗ committedAtLeast γr n ∗
        listFrozen γn gs ∗ [∗list] g ∈ gs, regOk γr.kv g F := by
  iintro #Hinv Hlc Hg #Hnis' Hown' Hauth' Hlist'
  iunfold readInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑readInvN) $$ Hlc Hi with Hi
  icases Hi with ⟨%nc0, %γn0, %n, %gs, Hg', #His, Hown, Hauth, #Hn, Hlist, #Hregs⟩
  ihave %Hag := ghostVar_agree γr.notifier _ _ _ _ $$ Hg Hg'
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  imod ghostVar_update_halves (nc', γn') γr.notifier _ _ $$ Hg Hg' with ⟨Hg, Hg'⟩
  imod monoNatLbOwn_0 γr.committed with #H0
  imod Hclose $$ [Hg' Hown' Hauth' Hlist'] with -
  · inext
    iexists nc', γn', (W64 0), []
    iframe Hg' Hnis' Hown'
    rw [show uint.nat (W64 0) = 0 by word]
    iframe Hauth' Hlist'
    isplitl []
    · iunfold committedAtLeast
      rw [show uint.nat (W64 0) = 0 by word]
      iexact H0
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  imod inv_alloc readFrozenN ⊤ (monoNatAuthOwn γn.need 1 (uint.nat n)) $$ [Hauth] with #Hfz
  · inext; iexact Hauth
  imod inv_alloc readFrozenN ⊤ (monoListAuthOwn γn.list 1 gs) $$ [Hlist] with #Hlf
  · inext; iexact Hlist
  imodintro
  iframe Hg Hown
  iexists n, gs
  iframe Hn Hregs
  iunfold needFrozen
  iunfold listFrozen
  iframe Hfz Hlf

end lemmas

end EtcdGrove
end Perennial
