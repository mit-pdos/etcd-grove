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

**The contracts** (persistent; unit 4b discharges them for `*EtcdServer` and its `raftNode`):
`isReadServer srv γr LR NR` (the `server` interface: the stop, done, leader-change and
first-commit channels (`bcastChan`, closed and never sent on), the logger with the caller's
resource `LR` (the server's `lgMu` reader slot), the applied index's lower bound, `ApplyWait`'s
channel closed once the applied index reached the deadline, a request id for a resource `NR` (the
id budget, the server's premise), the request timeout) and `isReadRaft rf γr RQ` (the
`raftInterface`: `ReadIndex` registers a request id at a committed bound, `RQ id n`, and every read
state on `ReadState()`'s channel answers each registration of its id: `readStateOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.read
public import Perennial.Golang.Theory.Chan.Idioms.Idioms
public import Perennial.Proof.time
public import Perennial.Proof.encoding.binary

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

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

/-! ## Request ids as bytes -/

/-- The big-endian bytes of `id` (`binary.BigEndian.PutUint64`, `uint64ToBigEndianBytes`). -/
def beBytes (id : w64) : List w8 := (u64Le id).reverse

theorem beBytes_length (id : w64) : (beBytes id).length = 8 := by
  simp [beBytes, u64Le_length]

/-- Eight bytes are the big-endian bytes of what `binary.BigEndian.Uint64` reads from them. -/
theorem beBytes_of_length (bs : List w8) (h : bs.length = 8) : bs = beBytes (leToU64 bs.reverse) := by
  unfold beBytes
  rw [leToU64_le _ (by simp [h]), List.reverse_reverse]

/-- `binary.BigEndian.Uint64` reads `id` back from its big-endian bytes. -/
theorem leToU64_beBytes (id : w64) : leToU64 (beBytes id).reverse = id := by
  unfold beBytes
  rw [List.reverse_reverse, u64Le_to_word]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
def needFrozen (γn : GName) (n : w64) : IProp GF :=
  inv readFrozenN (monoNatAuthOwn γn 1 (uint.nat n))

/-- **The loop's answer to the clients of a notifier with need `γn`** (persistent): its need was
frozen at `n`, and the applied index has reached `i ≥ n`. -/
def frozenOk (γn : GName) (γr : ReadNames) : IProp GF :=
  iprop(∃ (n i : w64), needFrozen γn n ∗ appliedAtLeast γr i ∗ ⌜uint.Z n ≤ uint.Z i⌝)

/-- **What the close of a notifier `nc` tells every waiter** (persistent): its error, stored
before the close for good (`nc.err ↦□`), one the gRPC layer can take (`applyErrIs`), and, if
`nil`, the loop's answer (`frozenOk`). -/
def notified (nc : Loc) (γn : GName) (γr : ReadNames) : IProp GF :=
  iprop(∃ err : GoInterface, ncErrAddr nc ↦□ err ∗ applyErrIs err ∗
    (⌜err ≠ GoInterface.nil⌝ ∨ frozenOk γn γr))

/-- **A channel closed (never sent on) whose close tells `Q`** (persistent; Perennial's broadcast
idiom, any receiver's view). -/
def bcastChan (ch : Loc) (Q : IProp GF) : IProp GF :=
  iprop(∃ γ : ChanNames, ownBroadcastChan ch γ Q .Unknown)

/-- **The notifier `nc` with need `γn`** (persistent; a waiter's view): its channel, closed with
`notified`. -/
def notifierIs (nc : Loc) (γn : GName) (γr : ReadNames) : IProp GF :=
  iprop(∃ ch : Loc, ncCAddr nc ↦□ ch ∗ bcastChan ch (notified nc γn γr))

/-- **The right to notify `nc`** (the loop's, once it swapped `nc` out): the channel not closed
yet, and `nc.err` (written once, before the close). -/
def notifierOwn (nc : Loc) (γn : GName) (γr : ReadNames) : IProp GF :=
  iprop(∃ (ch : Loc) (γ : ChanNames) (e : GoInterface), ncCAddr nc ↦□ ch ∗
    ownBroadcastChan ch γ (notified nc γn γr) .Pending ∗ ncErrAddr nc ↦ e)

/-- **The read invariant** (`γr.notifier`'s half; the lock's resource `readMuP` holds the other):
the current notifier `nc` and its need `γn` (its waiter's view and the right to notify it), the
need's authority `n`, and a lower bound of the committed index at least the need. -/
def readInv (γr : ReadNames) : IProp GF :=
  inv readInvN iprop(∃ (nc : Loc) (γn : GName) (n : w64),
    ghostVar γr.notifier (1 : Qp).half (nc, γn) ∗ notifierIs nc γn γr ∗ notifierOwn nc γn γr ∗
    monoNatAuthOwn γn 1 (uint.nat n) ∗ committedAtLeast γr n)

instance needFrozen_persistent (γn : GName) (n : w64) : Persistent (needFrozen (GF := GF) γn n) := by
  unfold needFrozen; infer_instance
instance frozenOk_persistent (γn : GName) (γr : ReadNames) : Persistent (frozenOk (GF := GF) γn γr) := by
  unfold frozenOk; infer_instance
instance notified_persistent (nc : Loc) (γn : GName) (γr : ReadNames) :
    Persistent (notified (GF := GF) nc γn γr) := by
  unfold notified; infer_instance
instance bcastChan_persistent (ch : Loc) (Q : IProp GF) : Persistent (bcastChan ch Q) := by
  unfold bcastChan; infer_instance
instance notifierIs_persistent (nc : Loc) (γn : GName) (γr : ReadNames) :
    Persistent (notifierIs (GF := GF) nc γn γr) := by
  unfold notifierIs; infer_instance
instance readIndexOk_persistent_read (γr : ReadNames) (c : w64) :
    Persistent (readIndexOk (GF := GF) γr c) := by
  unfold readIndexOk; infer_instance
instance readInv_persistent (γr : ReadNames) : Persistent (readInv (GF := GF) γr) := by
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

/-- **The server's `Done()`** (persistent; what `LinearizableReadNotify` needs of the server). -/
def srvDoneOk (srv : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜srv = GoInterface.ok si⌝ ∗ srvChanOk si go!"Done")

/-- **The `server` interface value `srv`** (persistent; unit 4b discharges it for `*EtcdServer`):
* `Done()`, `Stopping()`, `LeaderChanged()`, `FirstCommitInTermNotify()`: channels closed, never
  sent on, with no content (`bcastChan`); the last two with the caller's resource `LR` (given
  back: they read-lock a notifier; 2026-10-13, unit 4b);
* `Logger()`: a non-nil `*zap.Logger`, for the caller's resource `LR` (the server's `lgMu` reader
  slot: `EtcdServer.Logger` read-locks it; and the two notifiers' reader slots), given back;
* `AppliedIndex()`: an index the applied index has reached (`appliedAtLeast`);
* `ApplyWait(d)`: a channel closed once the applied index has reached `d`: its close tells some `Q`
  from which `appliedAtLeast γr d` follows (2026-10-13, unit 4b: `WaitTime.Wait` returns the
  package's `closec`, closed with nothing, when `d` was already triggered);
* `NextRequestID()`: some id, for a resource `NR` (the id generator's credit: the id budget, the
  server's premise; the loop asks for one per `ReadIndex` request, unboundedly);
* `RequestTimeout()`: some duration. -/
def isReadServer (srv : GoInterface) (γr : ReadNames) (LR NR : IProp GF) : IProp GF :=
  iprop(srvDoneOk srv ∗ ∃ si : GoInterfaceOk, ⌜srv = GoInterface.ok si⌝ ∗
    srvChanOk si go!"Stopping" ∗ srvChanOkR si go!"LeaderChanged" LR ∗
    srvChanOkR si go!"FirstCommitInTermNotify" LR ∗
    □ ({{ LR }} (App (Val #(methods si.ty go!"Logger" si.v)) (Val #()))
      {{ (l : Loc), RET #l; ⌜l ≠ null⌝ ∗ LR }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"AppliedIndex" si.v)) (Val #()))
      {{ (i : w64), RET #i; appliedAtLeast γr i }}) ∗
    □ (∀ d : w64, {{ True }} (App (Val #(methods si.ty go!"ApplyWait" si.v)) (Val #d))
      {{ (ch : Loc), RET #ch; ∃ Q : IProp GF, bcastChan ch Q ∗ □ (Q -∗ appliedAtLeast γr d) }}) ∗
    □ ({{ NR }} (App (Val #(methods si.ty go!"NextRequestID" si.v)) (Val #()))
      {{ (id : w64), RET #id; True }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"RequestTimeout" si.v)) (Val #()))
      {{ (d : _root_.Perennial.time.Duration), RET #d; True }}))

instance srvChanOk_persistent (si : GoInterfaceOk) (m : GoString) :
    Persistent (srvChanOk (GF := GF) si m) := by
  unfold srvChanOk; infer_instance
instance srvChanOkR_persistent (si : GoInterfaceOk) (m : GoString) (LR : IProp GF) :
    Persistent (srvChanOkR (GF := GF) si m LR) := by
  unfold srvChanOkR; infer_instance
instance srvDoneOk_persistent (srv : GoInterface) : Persistent (srvDoneOk (GF := GF) srv) := by
  unfold srvDoneOk; infer_instance
instance isReadServer_persistent (srv : GoInterface) (γr : ReadNames) (LR NR : IProp GF) :
    Persistent (isReadServer srv γr LR NR) := by
  unfold isReadServer; infer_instance

/-! ## Raft, as the read loop sees it (`raftInterface`) -/

/-- **A read state `rs` on raft's `ReadState()` channel** (persistent): its request context, eight
bytes, read-only, and its index answers every registration of the id they encode: a request
`ReadIndex` registered at a committed bound `n` (`RQ id n`) has `n ≤ rs.Index`. -/
def readStateOk (RQ : w64 → w64 → IProp GF)
    (rs : go_etcd_io.raft.v3.ReadState) : IProp GF :=
  iprop(∃ bs : List w8, rs.RequestCtx' ↦*□ bs ∗ ⌜bs.length = 8⌝ ∗
    □ (∀ (id n : w64), ⌜bs = beBytes id⌝ -∗ RQ id n -∗ ⌜uint.Z n ≤ uint.Z rs.Index'⌝))

/-- **`ReadState()`'s channel** (persistent): a bag channel of read states, each `readStateOk`
(the raft wrapper's `readStateC`, `isRNReadStateC` with content). -/
def isReadStateC (c : Loc) (RQ : w64 → w64 → IProp GF) : IProp GF :=
  iprop(∃ γ : ChanNames, isChanBag γ c (V := go_etcd_io.raft.v3.ReadState) (readStateOk RQ))

/-- **The `raftInterface` value `rf`** (persistent; unit 4b discharges it for the server's
`raftNode`, as `raftPropose`): `ReadState()` returns a channel of answered read states
(`isReadStateC`); `ReadIndex(ctx, rctx)`, with the big-endian bytes of an id read-only and a
lower bound `n` of the committed index, returns an error the gRPC layer can take, and if `nil` the
registration `RQ id n` (persistent). Sound of raft, given the request path's premise that request
ids do not repeat within the process (the `2^48` budget): a read state's index is the leader's
commit index when it served the request, at least every index committed cluster-wide by then; a
repeated id would let an old read state answer a new request's bound. -/
def isReadRaft (rf : GoInterface) (γr : ReadNames) (RQ : w64 → w64 → IProp GF) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rf = GoInterface.ok ri⌝ ∗
    □ ({{ True }} (App (Val #(methods ri.ty go!"ReadState" ri.v)) (Val #()))
      {{ (c : Loc), RET #c; isReadStateC c RQ }}) ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (dq : DFrac)
        (id n : w64),
      {{ context.isContext ctx cd ∗ sl ↦*{dq} beBytes id ∗ committedAtLeast γr n }}
        (App (App (Val #(methods ri.ty go!"ReadIndex" ri.v)) (Val #(GoInterface.ok ctx)))
          (Val #sl))
      {{ (err : GoInterface), RET #err; sl ↦*{dq} beBytes id ∗ applyErrIs err ∗
          (⌜err = GoInterface.nil⌝ -∗ □ RQ id n) }}))

instance readStateOk_persistent (RQ : w64 → w64 → IProp GF)
    (rs : go_etcd_io.raft.v3.ReadState) : Persistent (readStateOk (GF := GF) RQ rs) := by
  unfold readStateOk; infer_instance
instance isReadStateC_persistent (c : Loc) (RQ : w64 → w64 → IProp GF) :
    Persistent (isReadStateC (GF := GF) c RQ) := by
  unfold isReadStateC; infer_instance
instance isReadRaft_persistent (rf : GoInterface) (γr : ReadNames) (RQ : w64 → w64 → IProp GF) :
    Persistent (isReadRaft rf γr RQ) := by
  unfold isReadRaft; infer_instance

/-! ## The `*Read` -/

/-- **What `LinearizableReadNotify` needs of `r`** (persistent): the server's `Done()`, the
wake-up channel (a bag of `struct{}`), the read invariant. -/
def isReadPre (r : Loc) (γr : ReadNames) : IProp GF :=
  iprop(∃ (srv : GoInterface) (wc : Loc) (γw : ChanNames),
    readServerAddr r ↦□ srv ∗ srvDoneOk srv ∗
    readWaitCAddr r ↦□ wc ∗ isChanBag γw wc (V := Unit) (fun _ => iprop(True)) ∗
    readInv γr)

/-- **What `LinearizableReadLoop` needs of `r`** (persistent; `NewRead`'s result, with `isRead`):
the two contracts (`isReadServer` with the logger's resource `LR` and the id resource `NR`;
`isReadRaft` with the registrations `RQ`), the wake-up channel, the read invariant, the write
side of `r.mux` (`sync.isRWMutexGuard`), and `context`'s ghost fact (`closedchan` closed: what
`sendReadIndex`'s `context.WithTimeout` of `Background()` needs). -/
def isReadLoopPre (r : Loc) (γr : ReadNames) (RQ : w64 → w64 → IProp GF) (LR NR : IProp GF) :
    IProp GF :=
  iprop(∃ (srv rf : GoInterface) (wc : Loc) (γw : ChanNames),
    readServerAddr r ↦□ srv ∗ isReadServer srv γr LR NR ∗
    readRaftAddr r ↦□ rf ∗ isReadRaft rf γr RQ ∗
    readWaitCAddr r ↦□ wc ∗ isChanBag γw wc (V := Unit) (fun _ => iprop(True)) ∗
    readInv γr ∗ sync.isRWMutexGuard (readMuAddr r) (readMuP r γr) ∗ context.isClosedchanInit)

instance isReadPre_persistent (r : Loc) (γr : ReadNames) : Persistent (isReadPre (GF := GF) r γr) := by
  unfold isReadPre; infer_instance
instance isReadLoopPre_persistent (r : Loc) (γr : ReadNames) (RQ : w64 → w64 → IProp GF)
    (LR NR : IProp GF) : Persistent (isReadLoopPre r γr RQ LR NR) := by
  unfold isReadLoopPre; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The loop's view gives the clients'. -/
theorem isReadLoopPre_pre (r : Loc) (γr : ReadNames) (RQ : w64 → w64 → IProp GF) (LR NR : IProp GF) :
    isReadLoopPre r γr RQ LR NR ⊢ isReadPre r γr := by
  iunfold isReadLoopPre
  iintro ⟨%srv, %rf, %wc, %γw, #Hs, #Hsrv, -, -, #Hw, #Hb, #Hi, -, -⟩
  iunfold isReadServer at Hsrv
  icases Hsrv with ⟨#Hd, -⟩
  iunfold isReadPre
  iexists srv, wc, γw
  iframe #

/-- An unclosed broadcast channel's owner view gives a waiter's view too. -/
theorem bcast_pending_unknown (ch : Loc) (γ : ChanNames) (Q : IProp GF) :
    ownBroadcastChan ch γ Q .Pending ⊢ ownBroadcastChan ch γ Q .Pending ∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro H
  icases ownBroadcastChan_open _ _ _ _ $$ H with ⟨%γch, #Hint, Hd⟩
  isplitl [Hd]
  · iapply ownBroadcastChan_close _ _ _ _ γch; iframe Hint Hd
  · iapply ownBroadcastChan_close _ _ _ .Unknown γch; iframe Hint

/-- A guard of a lock from its reader slots (there is at least one; as mvcc's `guard_of_slots`). -/
theorem read_guard_of_slots [sync.Assumptions] (rw : Loc) (P : Qp → IProp GF) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), sync.ownRWMutex rw P) ⊢
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), sync.ownRWMutex rw P) ∗
        sync.isRWMutexGuard rw P := by
  have hpos : 0 < Int.toNat sync.rwmutex.actualMaxReaders :=
    Int.lt_toNat.2 (by simpa using sync.actualMaxReaders_pos)
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨Htok, Htoks⟩
  icases sync.ownRWMutex_guard _ _ $$ Htok with ⟨Htok, #Hguard⟩
  iframe Hguard
  iapply BigSepL.bigSepL_cons.2
  iframe Htok Htoks

/-- A ghost variable as two halves. -/
theorem read_ghostVar_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghostVar (GF := GF) γ 1 a ⊣⊢ ghostVar γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  have h := (ghostVar_fractional (GF := GF) γ a).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

/-- Halving distributes over a sum of fractions. -/
theorem read_qp_half_add (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half := by
  apply Subtype.ext
  show (q1.val + q2.val) / 2 = q1.val / 2 + q2.val / 2
  grind

/-- The lock's resource is fractional (for `sync.init_RWMutex`): the points-to and the ghost
variable split, two parts agree on the notifier and its need. -/
instance readMuP_fractional (r : Loc) (γr : ReadNames) : Fractional (readMuP (GF := GF) r γr) where
  fractional q1 q2 := by
    have hpt : ∀ v : Loc, (readNotifierAddr r ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
        readNotifierAddr r ↦{DFrac.own q1} v ∗ readNotifierAddr r ↦{DFrac.own q2} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1)
        (DFrac.own q2)
    have hgv := fun (x : Loc × GName) =>
      (ghostVar_fractional (GF := GF) γr.notifier x).fractional q1.half q2.half
    unfold readMuP
    rw [read_qp_half_add]
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
current notifier `nc` with need `γn`): the client's bound `c` raises the need (the read invariant
keeps a committed lower bound at least the need: the larger of the two bounds), and the client
gets a lower bound of the need and the notifier's waiters' view. -/
theorem read_deposit (γr : ReadNames) (q : Qp) (nc : Loc) (γn : GName) (c : w64) :
    ⊢ readInv (GF := GF) γr -∗ £ 1 -∗ ghostVar γr.notifier q (nc, γn) -∗ committedAtLeast γr c
      ={⊤}=∗ ghostVar γr.notifier q (nc, γn) ∗ notifierIs nc γn γr ∗ monoNatLbOwn γn (uint.nat c) := by
  iintro #Hinv Hlc Hg #Hc
  iunfold readInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑readInvN) $$ Hlc Hi with Hi
  icases Hi with ⟨%nc', %γn', %n, Hg', #His, Hown, Hauth, #Hn⟩
  ihave %Hag := ghostVar_agree γr.notifier _ _ _ _ $$ Hg Hg'
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  by_cases hle : uint.Z c ≤ uint.Z n
  · ihave #Hlb := monoNatLbOwn_get γn 1 _ $$ Hauth
    imod Hclose $$ [Hg' Hown Hauth] with -
    · inext; iexists nc, γn, n; iframe Hg' His Hown Hauth Hn
    imodintro
    iframe Hg His
    iapply monoNatLbOwn_le (uint.nat c) (by word) $$ Hlb
  · imod mono_nat_own_update (uint.nat c) (by word) $$ Hauth with ⟨Hauth, #Hlb⟩
    imod Hclose $$ [Hg' Hown Hauth] with -
    · inext; iexists nc, γn, c; iframe Hg' His Hown Hauth Hc
    imodintro
    iframe Hg His Hlb

/-- A frozen need bounds every lower bound of it. -/
theorem needFrozen_le (γn : GName) (n : w64) (m : Nat) :
    ⊢ needFrozen (GF := GF) γn n -∗ monoNatLbOwn γn m ={⊤}=∗ ⌜m ≤ uint.nat n⌝ := by
  iintro #Hf #Hlb
  iunfold needFrozen at Hf
  iinv Hf with Ha Hclose
  icases Ha with >Ha
  ihave %h := monoNatLbOwn_valid γn 1 _ _ $$ Ha Hlb
  imod Hclose $$ [Ha] with -
  · inext; iexact Ha
  imodintro
  ipureintro
  exact h.2

/-- **The loop's answer, for a client of the notifier** whose bound `c` is in the need: the
applied index reached an index at least `c`. -/
theorem read_frozenOk_readIndexOk (γn : GName) (γr : ReadNames) (c : w64) :
    ⊢ frozenOk (GF := GF) γn γr -∗ monoNatLbOwn γn (uint.nat c) ={⊤}=∗ readIndexOk γr c := by
  iintro #Hfz #Hlb
  iunfold frozenOk at Hfz
  icases Hfz with ⟨%n, %i, #Hf, #Hi, %Hni⟩
  imod needFrozen_le γn n (uint.nat c) $$ Hf Hlb with %hcn
  imodintro
  iunfold readIndexOk
  iexists i
  iframe Hi
  ipureintro
  word

/-- **The loop's swap** (`LinearizableReadLoop`, holding the write lock's ghost half of the current
notifier `nc` with need `γn`, swapping in the new notifier `nc'` with need `γn'` at `0`): the read
invariant takes `nc'`; the loop gets the right to notify `nc`, its need frozen at `n` (no client
can deposit in it any more) and a lower bound `n` of the committed index. -/
theorem read_swap (γr : ReadNames) (nc : Loc) (γn : GName) (nc' : Loc) (γn' : GName) :
    ⊢ readInv (GF := GF) γr -∗ £ 1 -∗ ghostVar γr.notifier (1 : Qp).half (nc, γn) -∗
      notifierIs nc' γn' γr -∗ notifierOwn nc' γn' γr -∗ monoNatAuthOwn γn' 1 0 ={⊤}=∗
      ghostVar γr.notifier (1 : Qp).half (nc', γn') ∗ notifierOwn nc γn γr ∗
      ∃ n : w64, needFrozen γn n ∗ committedAtLeast γr n := by
  iintro #Hinv Hlc Hg #Hnis' Hown' Hauth'
  iunfold readInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑readInvN) $$ Hlc Hi with Hi
  icases Hi with ⟨%nc0, %γn0, %n, Hg', #His, Hown, Hauth, #Hn⟩
  ihave %Hag := ghostVar_agree γr.notifier _ _ _ _ $$ Hg Hg'
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  imod ghostVar_update_halves (nc', γn') γr.notifier _ _ $$ Hg Hg' with ⟨Hg, Hg'⟩
  imod monoNatLbOwn_0 γr.committed with #H0
  imod Hclose $$ [Hg' Hown' Hauth'] with -
  · inext
    iexists nc', γn', (W64 0)
    iframe Hg' Hnis' Hown'
    rw [show uint.nat (W64 0) = 0 by word]
    iframe Hauth'
    iunfold committedAtLeast
    rw [show uint.nat (W64 0) = 0 by word]
    iexact H0
  imod inv_alloc readFrozenN ⊤ (monoNatAuthOwn γn 1 (uint.nat n)) $$ [Hauth] with #Hfz
  · inext; iexact Hauth
  imodintro
  iframe Hg Hown
  iexists n
  iframe Hn
  iunfold needFrozen
  iexact Hfz

end lemmas

end EtcdGrove
end Perennial
