/-
**The watch service's message models** (pure; split out of `InvWatchStream.lean` in the mvcc API
migration, 2026-11-05, so that the send loop's pure models are checked without the server): a
request's model `WatchReqM` (the oneof: a create request's fields `CreateReqM`, a cancel's watch id,
a progress request, or `other`), a response's model `WatchRespM` (the wire's fields and, as ghost
data, the mvcc response it carries: its index in the send loop's received list and the API's
`WResp`), the restrictions (`watchReqOk`), what a control response answers (`ctrlAnswers`), the
range a create registers (`createRangeOk`), and the send loop's bookkeeping of the mvcc responses it
forwards (`mvccResp`, `idLive`, `sentEvsOf`, `fwdEvs`, `fwdIdx`; the draft
`notes/mvcc-api-clients/WatchSpecs.lean` §2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchApi
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxnOwn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## The models (pure) -/

/-- **A `*pb.WatchCreateRequest`** as the server reads it. -/
structure CreateReqM where
  key : GoString
  rangeEnd : GoString
  startRev : w64
  progressNotify : Bool
  filters : List w32
  prevKv : Bool
  watchId : w64
  fragment : Bool
  /-- (ghost, not on the wire) the client promises the watch's completeness (`cplCond`, the
  client's): the server no longer reads it (W2 of `notes/watch-cut-plan.md`: a progress
  notification is above every watcher's first revision, by `progressIfSync`'s guard). -/
  sr : Bool := false
  /-- (ghost, not on the wire; G2, 2026-10-30) the client's bound on the auth store's published
  index when it sent the create (`watchUp`: `authPubLbM` of it comes with the request), at which
  the server's check is fresh (`watchAuthed`). A plain create's is `0`. -/
  bound : Nat := 0

/-- **A `*pb.WatchRequest`** as the server reads it: its oneof. `other` is a request the server
ignores (an empty oneof, or a wrapper whose request is `nil`). -/
inductive WatchReqM where
  | create (c : CreateReqM)
  | cancel (id : w64)
  | progress
  | other

/-- **A `*pb.WatchResponse`** as the wire carries it, with the mvcc response it carries as ghost
data (`src`, `none` for a control response; for one of the mvcc stream's, its index `n` in the send
loop's received list and the API's response; not on the wire). -/
structure WatchRespM where
  hdr : HdrM
  watchId : w64
  created : Bool
  canceled : Bool
  compactRev : w64
  cancelReason : GoString
  fragment : Bool
  evs : List mvcc.EvM
  src : Option (Nat × mvcc.api.WResp)

instance CreateReqM.countable : Pos.Countable CreateReqM :=
  .ofInjective (fun c => Pos.Countable.encode (c.key, c.rangeEnd, c.startRev, c.progressNotify,
      c.filters, c.prevKv, c.watchId, c.fragment, c.sr, c.bound))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- The oneof as a sum (for its countability). -/
def WatchReqM.enc : WatchReqM → CreateReqM ⊕ (w64 ⊕ Bool)
  | .create c => .inl c
  | .cancel id => .inr (.inl id)
  | .progress => .inr (.inr true)
  | .other => .inr (.inr false)

instance WatchReqM.countable : Pos.Countable WatchReqM :=
  .ofInjective (fun m => Pos.Countable.encode m.enc)
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [WatchReqM.enc])

instance WatchRespM.countable : Pos.Countable WatchRespM :=
  .ofInjective (fun m => Pos.Countable.encode ((m.hdr.clusterId, m.hdr.memberId, m.hdr.revision,
      m.hdr.raftTerm, m.hdr.leaderId), m.watchId, m.created, m.canceled, m.compactRev,
      m.cancelReason, m.fragment, m.evs, m.src))
    (fun a b h => by
      have := Pos.encode_inj h
      rcases a with ⟨⟨_, _, _, _, _⟩, _, _, _, _, _, _, _, _⟩
      rcases b with ⟨⟨_, _, _, _, _⟩, _, _, _, _, _, _, _, _⟩
      simp_all)

/-- **The restrictions of the watch server's proof** (`upRestricted`): a create request asks
neither for previous key-values (`prev_kv`: the send loop's `PrevKv` write and the store read
behind it are not modeled; not a bug: `newWatcherBatch` copies each event per watcher), nor for
fragments, nor filters; and no request is `other` (an empty oneof or a `nil` inner request: the translation
of `recvLoop`'s `default:` branch reads the type switch's variable `uv`, which Goose leaves
unbound there, a translator bug, `notes/STATUS.md`; etcd's client never sends one). And (the
watch slice's unit W-C) a create request asks for no watch id of its own (`WatchId = 0`,
`AutoWatchID`): this excludes clients choosing their own watch ids, which etcd's client never
does (`watch.go`'s `toPB` leaves it `0`); it is what makes the server's ids unique per stream,
the premise `srvEventIdsAssigned` of the client's watch true of the server
(`client/v3/InvWatch.lean`). -/
def watchReqOk : WatchReqM → Prop
  | .create c => c.prevKv = false ∧ c.fragment = false ∧ c.filters = [] ∧ c.watchId = W64 0
  | .other => False
  | _ => True

/-- **What a control response answers** (pure): a create request's `Created` response (no events,
no compaction, not fragmented, no ghost source): canceled with the watch id `-1` (a negative
start revision, the compacted response; the permission check failed; or mvcc's `Watch` refused:
an empty range, a duplicate id), or registered, not canceled, with the requested id if it was
not `0` (`AutoWatchID`), at a start revision at least `0`; a cancel request's `Canceled` response
with its id. -/
def ctrlAnswers (req : WatchReqM) (m : WatchRespM) : Prop :=
  m.src = none ∧ m.evs = [] ∧ m.compactRev = W64 0 ∧ m.fragment = false ∧
  match req with
  | .create c => m.created = true ∧
      ((m.canceled = true ∧ m.watchId = W64 (-1)) ∨
       (m.canceled = false ∧ 0 ≤ sint.Z c.startRev ∧
         (c.watchId ≠ W64 0 → m.watchId = c.watchId)))
  | .cancel id => m.created = false ∧ m.canceled = true ∧ m.watchId = id
  | _ => False

/-- **The range `r` a create request `c` registers** with the watch id `id` (`recvLoop`'s
normalization): an empty key is `"\x00"` (the smallest key); an empty range end is a single key
(`RangeEnd = nil`); the range end `"\x00"` is "from the key on" (`RangeEnd = []byte{}`, not
`nil`: the end `some []`); any other range end is kept. -/
def createRangeOk (c : CreateReqM) (id : w64) (r : mvcc.WatchRange) : Prop :=
  r.key = (if c.key = [] then [W8 0] else c.key) ∧ r.startRev = c.startRev ∧ r.id = id ∧
  (if c.rangeEnd = [] then r.end? = none
   else if c.rangeEnd = [W8 0] then r.end? = some []
   else r.end? = some c.rangeEnd)

/-- **The response the send loop makes of the `n`-th received response `x`** with the header `h`
(its revision `x.rev`): `x`'s watch id, events and compaction revision, canceled if that is set (a
watch behind the compaction revision: `chooseAll`'s response; watches across a compaction, D6,
2026-11-01), not created, no reason, not fragmented, `(n, x)` as its ghost source. -/
def mvccResp (n : Nat) (x : mvcc.api.WResp) (h : HdrM) : WatchRespM :=
  { hdr := h, watchId := x.id, created := false, canceled := decide (x.compactRev ≠ W64 0),
    compactRev := x.compactRev, cancelReason := [], fragment := false, evs := x.evs,
    src := some (n, x) }

/-- **The watch id `X` is live after the responses `L`** (pure; the watch slice's unit W-C): the
last control response for `X` among `L` is a created, not canceled, one. The send loop sends an
mvcc response of an id other than `-1` only while it is (`ids`), and a client that saw `X`
canceled is sent nothing more for it. -/
def idLive (L : List WatchRespM) (X : w64) : Prop :=
  ((L.filter (fun m => decide (m.src = none ∧ m.watchId = X))).getLast?.map
    (fun m => m.created && !m.canceled)) = some true

/-- The mvcc responses with events of the id `X` among the responses `L` sent down (by id: ids are
never reused on a stream, `StreamState.cancel` keeps the entry). -/
def sentEvsOf (L : List WatchRespM) (X : w64) : List mvcc.api.WResp :=
  ((L.filterMap WatchRespM.src).map Prod.snd).filter fun x => decide (x.id = X ∧ x.evs ≠ [])

/-- **What was forwarded of the id `X` before the response `x` received after `pre`** (pure;
K2e-7d, by id): for `X` live after the responses `L` sent before `x`, `x`'s own or any for `x` of
id `-1`: its responses with events sent are those received before `x`, in order (the send loop
sends a live id's responses at once, and flushes an id's buffered ones right after its created
response). -/
def fwdEvs (L : List WatchRespM) (pre : List mvcc.api.WResp) (x : mvcc.api.WResp) (X : w64) :
    Prop :=
  X ≠ W64 (-1) → idLive L X → (x.id = X ∨ x.id = W64 (-1)) →
    sentEvsOf L X = (pre.filter (fun y => decide (y.id = X))).filter (fun y => decide (y.evs ≠ []))

/-- **The responses sent before the `n`-th received one were received before it** (pure;
K2e-7d): those sent while `x`'s id was live (any, for `x` of id `-1`, which is sent at once). -/
def fwdIdx (L : List WatchRespM) (n : Nat) (x : mvcc.api.WResp) : Prop :=
  ∀ (i : Nat) (m' : WatchRespM) (n' : Nat) (y : mvcc.api.WResp), L[i]? = some m' →
    m'.src = some (n', y) → (x.id = W64 (-1) ∨ idLive (L.take i) x.id) → n' < n




end v3rpc
end EtcdGrove
end Perennial
