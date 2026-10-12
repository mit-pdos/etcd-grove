/-
etcd's cache `watcher` (`cache/watcher.go`): the shared vocabulary of `Spec/newWatcher.lean`
and `Spec/watcher__*.lean`, and the two operations of the watcher's consumer that are not Go
functions (`wp_watcher_receive`, `wp_watcher_cancelResp`). Lean-first (no Rocq counterpart).

A watcher is a buffered channel `respCh` of `WatchResponse`s with one producer (the demux,
which calls `enqueueResponse` under its lock, and `Stop`/`Compact`) and one consumer (the
goroutine of `Cache.Watch`, which does `resp, ok := <-w.respCh` and, on `!ok`, reads
`w.cancelResp`); a key filter `keyPred`; and a `sync.Once` guarding the `close`.

**The four predicates** (ghost names `γ`, `WatcherNames`):
- `isWatcher w γ pred` (persistent): the channel, the `keyPred` closure (nil iff
  `pred = none`, else its triple `keyPredSpec`), the `Once`, and the invariant `watcherInv`.
- `watcherOpen γ sent` (exclusive, the producer's): the channel is open and `sent` is the
  log of every response sent so far.
- `watcherClosed γ sent c` (persistent): the channel was closed after `sent`, with
  `cancelResp` nil (`c = none`, `Stop`) or the compaction response of revision `rev`
  (`c = some rev`, `Compact`).
- `watcherConsumer γ received` (exclusive, the consumer's): the consumer has received
  `received`, a prefix of `sent`.
The producer's and the consumer's views are separate (two halves of two ghost variables, the
other halves in the invariant) because they run concurrently: the producer cannot know how
much has been received, the consumer how much has been sent. The invariant ties them to the
channel: `recv <+: sent`, and the values in flight (in the buffer, or the one an unbuffered
send has committed) are the responses `sent.drop recv.length`, each `respSent` (`respAt` of
its model, with a non-nil `Header`).

**Closing.** `Stop` and `Compact` close the channel through `stopOnce.Do`. The `Once`'s
one-shot resource is `cancelResp ↦ nil`, its persistent result "closed after some log"; the
caller lends its `watcherOpen` to the closure (`Once.wp_Do_frame`, `OnceFrame.lean`), which
closes the channel, records `watcherClosed γ sent c` and leaves `cancelResp` read-only for
good. A caller that already holds `watcherClosed` gets it back unchanged.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore
public import Proof.go_etcd_io.etcd.cache.v3.OnceFrame
public import Perennial.Golang.Theory.Chan
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Pure models -/

instance EvModel.countable : Pos.Countable EvModel :=
  .ofInjective (fun e => Pos.Countable.encode (e.typ, e.key, e.kv, e.rev))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

instance RespModel.countable : Pos.Countable RespModel :=
  .ofInjective (fun r => Pos.Countable.encode (r.events, r.compactRev, r.canceled, r.created, r.hdrRev))
    (by rintro ⟨a, b, c, d, e⟩ ⟨a', b', c', d', e'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- What `enqueueResponse(resp)` sends for a response modelled by `r`, for a key filter `pred`
(`none` for a nil `keyPred`): with a filter, a response that is not a progress notification
keeps only the events whose key `pred` accepts, and is dropped (`none`) if none is left. (A
nil `Header` is replaced by an empty one, which has the same model: `hdrRev = 0`.) -/
def filterResp (pred : Option (GoString → Bool)) (r : RespModel) : Option RespModel :=
  match pred with
  | none => some r
  | some p =>
    if r.isProgressNotify then some r
    else if (r.events.filter (fun e => p e.key)).isEmpty then none
    else some { r with events := r.events.filter (fun e => p e.key) }

/-- The (event pointer, event model) pairs of `ls`/`evs` whose key `p` accepts. -/
def filterPairs (p : GoString → Bool) (ls : List Loc) (evs : List EvModel) : List (Loc × EvModel) :=
  (ls.zip evs).filter (fun x => p x.2.key)

theorem filterPairs_snd (p : GoString → Bool) :
    ∀ (ls : List Loc) (evs : List EvModel), ls.length = evs.length →
      (filterPairs p ls evs).map Prod.snd = evs.filter (fun e => p e.key)
  | [], [], _ => rfl
  | l :: ls, e :: evs, h => by
    have ih := filterPairs_snd p ls evs (by simpa using h)
    unfold filterPairs at ih ⊢
    simp only [List.zip_cons_cons, List.filter_cons]
    split <;> simp_all
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem filterPairs_take_succ (p : GoString → Bool) (ls : List Loc) (evs : List EvModel)
    (i : Nat) (l : Loc) (e : EvModel) (hl : ls[i]? = some l) (he : evs[i]? = some e) :
    filterPairs p (ls.take (i + 1)) (evs.take (i + 1)) =
      filterPairs p (ls.take i) (evs.take i) ++ (if p e.key then [(l, e)] else []) := by
  unfold filterPairs
  rw [List.take_add_one, List.take_add_one, hl, he]
  simp only [Option.toList_some]
  rw [List.zip_append (by
    have h1 : i < ls.length := (List.getElem?_eq_some_iff.mp hl).1
    have h2 : i < evs.length := (List.getElem?_eq_some_iff.mp he).1
    simp [List.length_take]; omega)]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.filter_append, List.filter_cons,
    List.filter_nil]
  try (split <;> simp_all)

theorem filterPairs_get (p : GoString → Bool) (ls : List Loc) (evs : List EvModel) (j : Nat)
    (l : Loc) (e : EvModel)
    (h1 : ((filterPairs p ls evs).map Prod.fst)[j]? = some l)
    (h2 : ((filterPairs p ls evs).map Prod.snd)[j]? = some e) :
    ∃ k : Nat, ls[k]? = some l ∧ evs[k]? = some e := by
  rw [List.getElem?_map] at h1 h2
  cases hj : (filterPairs p ls evs)[j]? with
  | none => simp [hj] at h1
  | some x =>
    simp only [hj, Option.map_some, Option.some.injEq] at h1 h2
    have hm : x ∈ ls.zip evs := by
      have := List.mem_of_getElem? hj
      unfold filterPairs at this
      exact (List.mem_filter.mp this).1
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    refine ⟨k, ?_, ?_⟩
    · rw [List.getElem?_zip_eq_some] at hk; rw [← h1]; exact hk.1
    · rw [List.getElem?_zip_eq_some] at hk; rw [← h2]; exact hk.2

/-- The response `Compact(rev)` leaves in `cancelResp`: canceled, with compaction revision
`rev`, no events, and an empty (`Revision = 0`) header. -/
def cancelModel (rev : w64) : RespModel :=
  { events := [], compactRev := rev, canceled := true, created := false, hdrRev := W64 0 }

/-- The values a channel in state `s` holds in flight: its buffer (also when closed), or the
value an unbuffered send has committed to; `none` for the states of a blocking send, which
the watcher's producer never does. -/
def chanInflight {V : Type} : ChanState V → Option (List V)
  | .Buffered b => some b
  | .Closed b => some b
  | .Idle => some []
  | .RcvPending => some []
  | .SndCommit v => some [v]
  | .SndPending _ => none
  | .RcvCommit => none

/-- The channel state `s` is closed. -/
def chanIsClosed {V : Type} : ChanState V → Bool
  | .Closed _ => true
  | _ => false

/-- The ghost names of a watcher. -/
structure WatcherNames where
  /-- the channel's -/
  ch : ChanNames
  /-- `ghostVar (List RespModel)`: the log of sent responses -/
  sent : GName
  /-- `ghostVar (List RespModel)`: the log of received responses -/
  recv : GName
  /-- `dghostVar (Option (List RespModel × Option w64))`: `some (sent, c)` once closed -/
  closed : GName
  /-- `token`: the `Once`'s one-shot right to close, in the invariant once closed -/
  tok : GName

/-- The encoding of a `WatchResponse` (for `Pos.Countable`, which the channel's ghost state
needs). -/
def watchResponseEnc [FfiSyntax] (r : go_etcd_io.etcd.client.v3.WatchResponse) :
    Loc × GoSlice × w64 × Bool × Bool × GoInterface × GoString :=
  (r.Header', r.Events', r.CompactRevision', r.Canceled', r.Created', r.closeErr', r.CancelReason')

instance watchResponse_countable [FfiSyntax] :
    Pos.Countable go_etcd_io.etcd.client.v3.WatchResponse :=
  .ofInjective (fun r => Pos.Countable.encode (watchResponseEnc r))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b
      simp only [watchResponseEnc, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h'
      rfl)

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `w.respCh`. -/
abbrev watcherRespChAddr (w : Loc) : Loc := structFieldRef watcher go!"respCh" w

/-- The address of `w.cancelResp`. -/
abbrev watcherCancelRespAddr (w : Loc) : Loc := structFieldRef watcher go!"cancelResp" w

/-- The address of `w.keyPred`. -/
abbrev watcherKeyPredAddr (w : Loc) : Loc := structFieldRef watcher go!"keyPred" w

/-- The address of `w.stopOnce`. -/
abbrev watcherStopOnceAddr (w : Loc) : Loc := structFieldRef watcher go!"stopOnce" w

end addrs

/-- The watcher's invariant's namespace. -/
def watcherN : Namespace := nroot.@"watcher"

/-- What a watcher publishes about its producer's logs, for its consumer (`isWatcher`'s
parameter, chosen by `newWatcher`'s caller): `pub none L` holds for every log `L` the producer
has had (every prefix of what was sent; the producer establishes it for each new log at the send),
`pub (some c) L` once the channel was closed after `L` with cancel `c` (established at the
close). The consumer learns `pub none` of each prefix it receives, and `pub (some c)` when it
sees the close. Timeless, so that the watcher's invariant is (the demux's facts are pure and
points-to facts). -/
structure WatcherPub (GF : BundledGFunctors) where
  pub : Option (Option w64) → List RespModel → IProp GF
  timeless : ∀ oc L, Timeless (pub oc L)

instance WatcherPub.pub_timeless {GF : BundledGFunctors} (Pb : WatcherPub GF)
    (oc : Option (Option w64)) (L : List RespModel) : Timeless (Pb.pub oc L) := Pb.timeless oc L

/-- Nothing published. -/
def WatcherPub.trivial (GF : BundledGFunctors) : WatcherPub GF :=
  ⟨fun _ _ => iprop(True), fun _ _ => inferInstance⟩

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- A response value as the watcher sends it: modelled by `r` (`respAt`), with a non-nil
header (`enqueueResponse` fills in a nil one). -/
def respSent (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop(respAt v r ∗ ⌜v.Header' ≠ null⌝)

instance respSent_persistent (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (respSent (GF := GF) v r) := by
  unfold respSent; infer_instance

/-- The values `vs` are the responses `rs`, pointwise (`respSent`). -/
def respsSent (vs : List go_etcd_io.etcd.client.v3.WatchResponse) (rs : List RespModel) :
    IProp GF :=
  iprop(⌜vs.length = rs.length⌝ ∗
    □ (∀ (i : Nat) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
      ⌜vs[i]? = some v⌝ -∗ ⌜rs[i]? = some r⌝ -∗ respSent v r))

instance respsSent_persistent (vs : List go_etcd_io.etcd.client.v3.WatchResponse)
    (rs : List RespModel) : Persistent (respsSent (GF := GF) vs rs) := by
  unfold respsSent; infer_instance

theorem respsSent_nil : ⊢ respsSent (GF := GF) [] [] := by
  unfold respsSent
  iintro
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %v %r %Hv
  simp at Hv

theorem respsSent_length (vs : List go_etcd_io.etcd.client.v3.WatchResponse)
    (rs : List RespModel) : respsSent (GF := GF) vs rs ⊢ ⌜vs.length = rs.length⌝ := by
  unfold respsSent
  iintro ⟨%H, -⟩
  ipureintro; exact H

/-- Appending a sent response. -/
theorem respsSent_snoc (vs : List go_etcd_io.etcd.client.v3.WatchResponse) (rs : List RespModel)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    respsSent (GF := GF) vs rs ∗ respSent v r ⊢ respsSent (vs ++ [v]) (rs ++ [r]) := by
  unfold respsSent
  iintro ⟨⟨%Hlen, #H⟩, #Hv⟩
  isplitr
  · ipureintro; simp [Hlen]
  imodintro
  iintro %i %v' %r' %Hv' %Hr'
  by_cases hi : i < vs.length
  · rw [List.getElem?_append_left hi] at Hv'
    rw [List.getElem?_append_left (Hlen ▸ hi)] at Hr'
    iapply H $$ %i %v' %r' %Hv' %Hr'
  · have hge : vs.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hge] at Hv'
    rw [List.getElem?_append_right (Hlen ▸ hge)] at Hr'
    rw [Hlen] at Hv'
    obtain ⟨hi1, rfl⟩ := List.getElem?_eq_some_iff.mp Hv'
    obtain ⟨hi2, rfl⟩ := List.getElem?_eq_some_iff.mp Hr'
    simp only [List.length_singleton, Nat.lt_one_iff] at hi1
    simp only [hi1, List.getElem_singleton]
    iexact Hv

/-- Taking the first in-flight response. -/
theorem respsSent_cons (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (vs : List go_etcd_io.etcd.client.v3.WatchResponse) (rs : List RespModel) :
    respsSent (GF := GF) (v :: vs) rs ⊢
      ∃ r rs', ⌜rs = r :: rs'⌝ ∗ respSent v r ∗ respsSent vs rs' := by
  unfold respsSent
  iintro ⟨%Hlen, #H⟩
  cases rs with
  | nil => simp at Hlen
  | cons r rs' =>
    iexists r, rs'
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply H $$ %0 %v %r %rfl %rfl
    isplitr
    · ipureintro; simpa using Hlen
    imodintro
    iintro %i %v' %r' %Hv' %Hr'
    iapply H $$ %(i + 1) %v' %r' %Hv' %Hr'

/-- `p` is the value of `cancelResp` after a close with cancel `c`: nil for `none`, a
read-only `WatchResponse` modelled by `cancelModel rev` for `some rev`. -/
def cancelAt (p : Loc) (c : Option w64) : IProp GF :=
  match c with
  | none => iprop(⌜p = null⌝)
  | some rev => iprop(∃ v : go_etcd_io.etcd.client.v3.WatchResponse,
      p ↦□ v ∗ respSent v (cancelModel rev))

instance cancelAt_persistent (p : Loc) (c : Option w64) : Persistent (cancelAt (GF := GF) p c) := by
  cases c <;> unfold cancelAt <;> infer_instance

/-- The `keyPred` closure `f` implements the key filter `p`: on a read-only byte slice holding
`key`, it returns `p key`. -/
def keyPredSpec (f : GoFunc) (p : GoString → Bool) : IProp GF :=
  iprop(∀ (sl : GoSlice) (key : GoString),
    {{ sl ↦*□ key }} (App (Val #f) (Val #sl)) {{ RET #(p key); True }})

instance keyPredSpec_persistent (f : GoFunc) (p : GoString → Bool) :
    Persistent (keyPredSpec (GF := GF) f p) := by
  unfold keyPredSpec; infer_instance

/-- `keyPred` is `f`, nil for no filter. -/
def keyPredOk (f : GoFunc) (pred : Option (GoString → Bool)) : IProp GF :=
  match pred with
  | none => iprop(⌜f = func.nil⌝)
  | some p => iprop(⌜f ≠ func.nil⌝ ∗ keyPredSpec f p)

instance keyPredOk_persistent (f : GoFunc) (pred : Option (GoString → Bool)) :
    Persistent (keyPredOk (GF := GF) f pred) := by
  cases pred <;> unfold keyPredOk <;> infer_instance

/-- The producer's view: the channel is open and `sent` was sent. -/
def watcherOpen (γ : WatcherNames) (sent : List RespModel) : IProp GF :=
  iprop(ghostVar γ.sent (1 : Qp).half sent ∗
    dghostVar γ.closed (.own (1 : Qp).half) (none : Option (List RespModel × Option w64)))

/-- The channel was closed after `sent`, with cancel `c` (persistent). -/
def watcherClosed (γ : WatcherNames) (sent : List RespModel) (c : Option w64) : IProp GF :=
  dghostVar γ.closed .discard (some (sent, c))

instance watcherClosed_persistent (γ : WatcherNames) (sent : List RespModel) (c : Option w64) :
    Persistent (watcherClosed (GF := GF) γ sent c) := by
  unfold watcherClosed; infer_instance

/-- The consumer's view: it has received `received`. -/
def watcherConsumer (γ : WatcherNames) (received : List RespModel) : IProp GF :=
  ghostVar γ.recv (1 : Qp).half received

/-- The closed state of the invariant: closed after `sent` with cancel `c`, `cancelResp`
read-only for good. -/
def watcherInvClosed (w : Loc) (γ : WatcherNames) (Pb : WatcherPub GF) (sent : List RespModel)
    (cl : Option (List RespModel × Option w64)) : IProp GF :=
  match cl with
  | none => dghostVar γ.closed (.own (1 : Qp).half) (none : Option (List RespModel × Option w64))
  | some (sc, c) => iprop(watcherClosed γ sc c ∗ ghostVar γ.sent (1 : Qp).half sent ∗ ⌜sc = sent⌝ ∗
      token γ.tok ∗ (∃ p, watcherCancelRespAddr w ↦□ p ∗ cancelAt p c) ∗ □ Pb.pub (some c) sc)

/-- The watcher's invariant (see the module docstring). -/
def watcherInv (w : Loc) (γ : WatcherNames) (Pb : WatcherPub GF) : IProp GF :=
  iprop(∃ (s : ChanState go_etcd_io.etcd.client.v3.WatchResponse) (sent recv : List RespModel)
      (vs : List go_etcd_io.etcd.client.v3.WatchResponse)
      (cl : Option (List RespModel × Option w64)),
    "Hch" ∷ ownChan γ.ch go_etcd_io.etcd.client.v3.WatchResponse s ∗
    "Hsent" ∷ ghostVar γ.sent (1 : Qp).half sent ∗
    "Hrecv" ∷ ghostVar γ.recv (1 : Qp).half recv ∗
    "%Hpre" ∷ ⌜recv <+: sent⌝ ∗
    "%Hinfl" ∷ ⌜chanInflight s = some vs⌝ ∗
    "%Hclosed" ∷ ⌜chanIsClosed s = cl.isSome⌝ ∗
    "#Hvs" ∷ respsSent vs (sent.drop recv.length) ∗
    "#Hpub" ∷ □ (∀ L, ⌜L <+: sent⌝ -∗ Pb.pub none L) ∗
    "Hcl" ∷ watcherInvClosed w γ Pb sent cl)

/-- The `stopOnce`'s one-shot resource: `cancelResp` (still nil) and the right to close. -/
def watcherOnceP (w : Loc) (γ : WatcherNames) : IProp GF :=
  iprop(watcherCancelRespAddr w ↦ (null : Loc) ∗ token γ.tok)

instance respSent_timeless (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Timeless (respSent (GF := GF) v r) := by
  unfold respSent respAt eventsAt eventAt hdrAt; infer_instance

instance respsSent_timeless (vs : List go_etcd_io.etcd.client.v3.WatchResponse)
    (rs : List RespModel) : Timeless (respsSent (GF := GF) vs rs) := by
  unfold respsSent; infer_instance

instance cancelAt_timeless (p : Loc) (c : Option w64) : Timeless (cancelAt (GF := GF) p c) := by
  cases c <;> unfold cancelAt <;> infer_instance

instance watcherInvClosed_timeless (w : Loc) (γ : WatcherNames) (Pb : WatcherPub GF)
    (sent : List RespModel) (cl : Option (List RespModel × Option w64)) :
    Timeless (watcherInvClosed (GF := GF) w γ Pb sent cl) := by
  rcases cl with _ | ⟨sc, c⟩ <;> unfold watcherInvClosed watcherClosed <;> infer_instance

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
instance watcherInv_timeless (w : Loc) (γ : WatcherNames) (Pb : WatcherPub GF) :
    Timeless (watcherInv (GF := GF) w γ Pb) := by
  unfold watcherInv; infer_instance

/-- `w` is a watcher with ghost names `γ`, key filter `pred` and publication `Pb` (persistent). -/
def isWatcher (w : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool)) (Pb : WatcherPub GF) :
    IProp GF :=
  iprop(∃ (ch : Loc) (f : GoFunc),
    "#HrespCh" ∷ watcherRespChAddr w ↦□ ch ∗
    "#HisCh" ∷ isChan ch γ.ch go_etcd_io.etcd.client.v3.WatchResponse ∗
    "#HkeyPred" ∷ watcherKeyPredAddr w ↦□ f ∗
    "#Hpred" ∷ keyPredOk f pred ∗
    "#Honce" ∷ sync.isOnce (watcherStopOnceAddr w) (watcherOnceP w γ)
      iprop(∃ sc c, watcherClosed γ sc c) ∗
    "#Hinv" ∷ inv watcherN (watcherInv w γ Pb))

instance isWatcher_persistent (w : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) : Persistent (isWatcher (GF := GF) w γ pred Pb) := by
  unfold isWatcher; infer_instance

/-- Where `Stop`/`Compact` start from: open after `sent`, or already closed after `sent`. -/
inductive WatcherPhase where
  | opened
  | closed (c : Option w64)

/-- The cancel of the watcher after a `Stop` (`c = none`) or `Compact(rev)` (`c = some rev`)
from phase `ph`: `c` if it was open (this call closed it), the old one otherwise. -/
def WatcherPhase.cancelAfter : WatcherPhase → Option w64 → Option w64
  | .opened, c => c
  | .closed c0, _ => c0

/-- What `Stop`/`Compact` must publish to close a watcher in phase `ph` with cancel `c`: the
closed log's `pub (some c)` if this call closes it (it is open), nothing otherwise. -/
def watcherClosePub (Pb : WatcherPub GF) (sent : List RespModel) (c : Option w64) :
    WatcherPhase → IProp GF
  | .opened => iprop(□ Pb.pub (some c) sent)
  | .closed _ => iprop(True)

instance watcherClosePub_persistent (Pb : WatcherPub GF) (sent : List RespModel) (c : Option w64)
    (ph : WatcherPhase) : Persistent (watcherClosePub Pb sent c ph) := by
  cases ph <;> unfold watcherClosePub <;> infer_instance

/-- The producer's view in phase `ph`. -/
def watcherAt (γ : WatcherNames) (sent : List RespModel) : WatcherPhase → IProp GF
  | .opened => watcherOpen γ sent
  | .closed c => watcherClosed γ sent c

end defs

/-! ## Lemmas -/

theorem prefix_drop_cons {α : Type} {sent recv rs : List α} {r : α} (hp : recv <+: sent)
    (hd : sent.drop recv.length = r :: rs) :
    recv ++ [r] <+: sent ∧ sent.drop (recv ++ [r]).length = rs := by
  obtain ⟨t, rfl⟩ := hp
  simp only [List.drop_left] at hd
  subst hd
  refine ⟨⟨rs, by simp⟩, ?_⟩
  simp

theorem prefix_drop_nil {α : Type} {sent recv : List α} (hp : recv <+: sent)
    (hd : sent.drop recv.length = []) : recv = sent := by
  obtain ⟨t, rfl⟩ := hp
  simp only [List.drop_left] at hd
  simp [hd]

theorem prefix_snoc_cases {α : Type} {L sent : List α} {r : α} (h : L <+: sent ++ [r]) :
    L <+: sent ∨ L = sent ++ [r] := by
  obtain ⟨t, ht⟩ := h
  rcases List.eq_nil_or_concat t with rfl | ⟨t', x, rfl⟩
  · right; simpa using ht
  · left
    have h1 : (L ++ t') ++ [x] = sent ++ [r] := by simpa using ht
    have h2 := List.append_inj_left' h1 rfl
    exact ⟨t', h2⟩

theorem prefix_snoc_drop {α : Type} {sent recv : List α} (r : α) (hp : recv <+: sent) :
    recv <+: sent ++ [r] ∧ (sent ++ [r]).drop recv.length = sent.drop recv.length ++ [r] := by
  refine ⟨hp.trans (List.prefix_append _ _), ?_⟩
  exact List.drop_append_of_le_length hp.length_le

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem watcherOpen_closed_false (γ : WatcherNames) (sent sent' : List RespModel) (c : Option w64) :
    watcherOpen (GF := GF) γ sent ∗ watcherClosed γ sent' c ⊢ False := by
  unfold watcherOpen watcherClosed
  iintro ⟨⟨-, H1⟩, H2⟩
  ihave %H := dghostVar_agree _ _ _ _ _ $$ H1 H2
  cases H

theorem watcherClosed_agree (γ : WatcherNames) (s1 s2 : List RespModel) (c1 c2 : Option w64) :
    watcherClosed (GF := GF) γ s1 c1 ∗ watcherClosed γ s2 c2 ⊢ ⌜s1 = s2 ∧ c1 = c2⌝ := by
  unfold watcherClosed
  iintro ⟨H1, H2⟩
  ihave %H := dghostVar_agree _ _ _ _ _ $$ H1 H2
  ipureintro
  simpa using H

/-- Once closed, the right to close is gone (in the invariant). -/
theorem watcher_tok_closed_false (w : Loc) (γ : WatcherNames) (Pb : WatcherPub GF)
    (sent : List RespModel) (c : Option w64) :
    inv watcherN (watcherInv (hG := hG) w γ Pb) ∗ watcherClosed γ sent c ∗ token γ.tok ∗ £ 1 ⊢
      |={⊤}=> False := by
  iintro ⟨#Hinv, #Hcl0, Htok, Hlc⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑watcherN) $$ Hlc Hi with Hi
  unfold watcherInv
  iNamed Hi
  rcases cl with _ | ⟨sc, c'⟩
  · unfold watcherInvClosed watcherClosed
    ihave %H := dghostVar_agree _ _ _ _ _ $$ Hcl Hcl0
    cases H
  · unfold watcherInvClosed
    icases Hcl with ⟨-, -, -, Htok', -⟩
    iexfalso
    iapply token_exclusive $$ Htok Htok'

/-- Closing the watcher's channel (the closure of `Stop`/`Compact`, with `cancelResp`
already set to `p` for good): the producer's open view and the right to close become
`watcherClosed γ sent c`. -/
theorem watcher_close_au (w : Loc) (γ : WatcherNames) (Pb : WatcherPub GF)
    (sent : List RespModel) (c : Option w64) (p : Loc) (Φ : IProp GF) :
    ⊢ inv watcherN (watcherInv (hG := hG) w γ Pb) -∗ watcherOpen γ sent -∗ token γ.tok -∗
      watcherCancelRespAddr w ↦□ p -∗ cancelAt p c -∗ □ Pb.pub (some c) sent -∗
      (watcherClosed γ sent c -∗ Φ) -∗
      closeAu γ.ch go_etcd_io.etcd.client.v3.WatchResponse Φ := by
  iintro #Hinv Hopen Htok #Hp #Hc #HPc HΦ
  unfold closeAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold watcherInv
  iNamed Hi
  unfold watcherOpen
  icases Hopen with ⟨Hs, Hcl0⟩
  rcases cl with _ | ⟨sc, c'⟩
  case some =>
    unfold watcherInvClosed watcherClosed
    icases Hcl with ⟨Hcl, -⟩
    ihave %H := dghostVar_agree _ _ _ _ _ $$ Hcl0 Hcl
    cases H
  unfold watcherInvClosed
  icombine Hs Hsent gives % ⟨_, Heq⟩
  subst Heq
  iexists s
  iframe Hch
  rcases s with (_ | ⟨b0, bs⟩) | _ | _ | _ | _ | _ | (_ | ⟨b0, bs⟩)
  all_goals dsimp only
  case Closed.nil => exfalso; simp [chanIsClosed] at Hclosed
  case Closed.cons => exfalso; simp [chanIsClosed] at Hclosed
  case SndPending => itrivial
  case RcvPending => itrivial
  case SndCommit => itrivial
  case RcvCommit => itrivial
  all_goals
    iintro Hch
    imod dghostVar_update_halves (some (sent, c)) γ.closed _ _ $$ Hcl0 Hcl with ⟨Hc1, Hc2⟩
    imod dghostVar_persist _ _ _ $$ Hc1 with #Hc1
    imod Hmask with -
    imod Hclose $$ [Hch Hs Hsent Hrecv Htok] with -
    · inext
      iexists _, sent, recv, vs, some (sent, c)
      simp only [named]
      iframe Hch
      iframe
      unfold watcherClosed
      iframe #
      ipureintro
      simp_all [chanInflight, chanIsClosed]
    imodintro
    iapply HΦ
    unfold watcherClosed
    iexact Hc1

/-- The ghost step of a receive: the next in-flight value `v` is the response `r` after
`received`, which becomes `received ++ [r]`. -/
theorem watcher_take (γ : WatcherNames) (received sent : List RespModel)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (rest : List go_etcd_io.etcd.client.v3.WatchResponse)
    (hpre : received <+: sent) :
    ghostVar (GF := GF) γ.recv (1 : Qp).half received ∗ ghostVar γ.recv (1 : Qp).half received ∗
      respsSent (v :: rest) (sent.drop received.length) ⊢
    |==> ∃ r, ghostVar γ.recv (1 : Qp).half (received ++ [r]) ∗
      ghostVar γ.recv (1 : Qp).half (received ++ [r]) ∗ respSent v r ∗
      respsSent rest (sent.drop (received ++ [r]).length) ∗ ⌜received ++ [r] <+: sent⌝ := by
  iintro ⟨H1, H2, #Hvs⟩
  icases respsSent_cons _ _ _ $$ Hvs with ⟨%r, %rs', %Hd, #Hr, #Hrest⟩
  obtain ⟨Hp', Hd'⟩ := prefix_drop_cons hpre Hd
  imod ghostVar_update_halves (received ++ [r]) γ.recv _ _ $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iexists r
  iframe
  rw [Hd']
  iframe #
  ipureintro; exact Hp'

/-- The producer's non-blocking send `select { case w.respCh <- v: handler; default: dflt }`
(`enqueueResponse`): `handler` runs after `v` (the response `r`) was sent, `dflt` with nothing
sent. The channel is open (`watcherOpen`), so the send cannot panic. -/
theorem wp_watcher_send (w ch : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) (sent : List RespModel) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r : RespModel) (dflt handler : Expr) (Ψ : val → IProp GF) :
    ⊢ isWatcher w γ pred Pb -∗ watcherRespChAddr w ↦□ ch -∗ watcherOpen γ sent -∗ respSent v r -∗
      □ Pb.pub none (sent ++ [r]) -∗
      ((watcherOpen γ (sent ++ [r]) -∗ WP handler {{ Ψ }}) ∧ (watcherOpen γ sent -∗ WP dflt {{ Ψ }})) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV (some dflt)
        [.CommClause (.SendCase go_etcd_io.etcd.client.v3.WatchResponse.ty (Val #ch) (Val #v)) handler])))
        {{ Ψ }} := by
  iintro #Hw #Hch' Hopen #Hv #HPr HΨ
  unfold isWatcher
  iNamed Hw
  icombine HrespCh Hch' gives %Heq
  subst Heq
  iapply chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
        inferInstance, ch, γ.ch, v
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · iexact HisCh
      unfold nonblockingSendAu
      isplit
      · unfold nonblockingSendAuInner
        iinv Hinv with Hi Hclose
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        inext
        unfold watcherInv
        iNamed Hi
        unfold watcherOpen
        icases Hopen with ⟨Hs, Hc0⟩
        rcases cl with _ | ⟨sc, c'⟩
        case some =>
          unfold watcherInvClosed watcherClosed
          icases Hcl with ⟨Hcl, -⟩
          ihave %H := dghostVar_agree _ _ _ _ _ $$ Hc0 Hcl
          cases H
        icombine Hs Hsent gives % ⟨_, Heq⟩
        subst Heq
        iexists s
        iframe Hch
        obtain ⟨Hpre', Hd⟩ := prefix_snoc_drop r Hpre
        rcases s with (_ | ⟨b0, bs⟩) | _ | _ | _ | _ | _ | (_ | ⟨b0, bs⟩)
        all_goals dsimp only
        case Closed.nil => exfalso; simp [chanIsClosed] at Hclosed
        case Closed.cons => exfalso; simp [chanIsClosed] at Hclosed
        all_goals first | itrivial | skip
        all_goals
          iintro Hch
          imod ghostVar_update_halves (sent ++ [r]) γ.sent _ _ $$ Hs Hsent with ⟨Hs, Hsent⟩
          ihave #Hvs' := respsSent_snoc _ _ v r $$ [$Hvs $Hv]
          ihave #Hpub' : iprop(□ (∀ L, ⌜L <+: sent ++ [r]⌝ -∗ Pb.pub none L)) $$ []
          · imodintro
            iintro %L %HL
            rcases prefix_snoc_cases HL with HL | rfl
            · iapply Hpub $$ %L %HL
            · iexact HPr
          imod Hmask with -
          imod Hclose $$ [Hch Hsent Hrecv Hcl] with -
          · inext
            iexists _, sent ++ [r], recv, vs ++ [v], none
            simp only [named]
            unfold watcherInvClosed
            iframe Hch
            rw [Hd]
            iframe
            iframe #
            ipureintro
            simp_all [chanInflight, chanIsClosed]
          imodintro
          icases HΨ with ⟨HΨ, -⟩
          iapply HΨ
          iframe
      · itrivial
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  · icases HΨ with ⟨-, HΨ⟩
    iapply HΨ $$ Hopen

/-- What the consumer gets from `<-w.respCh` with `received` received so far. -/
def watcherRecvResult (γ : WatcherNames) (Pb : WatcherPub GF) (received : List RespModel)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool) : IProp GF :=
  if ok then iprop(∃ r, respSent resp r ∗ watcherConsumer γ (received ++ [r]) ∗
    □ Pb.pub none (received ++ [r]))
  else iprop(∃ c, watcherConsumer γ received ∗ watcherClosed γ received c ∗
    □ Pb.pub (some c) received)

/-- The watcher's channel (for a `select` case on it). -/
theorem isWatcher_isChan (w ch : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) :
    isWatcher (GF := GF) w γ pred Pb ∗ watcherRespChAddr w ↦□ ch ⊢
      isChan ch γ.ch go_etcd_io.etcd.client.v3.WatchResponse := by
  iintro ⟨#Hw, #Hch'⟩
  unfold isWatcher
  iNamed Hw
  icombine HrespCh Hch' gives %Heq
  subst Heq
  iexact HisCh

/-- The consumer's receive on `w.respCh`, as the atomic update of Perennial's channel specs
(`recvAu`, for `chan.wp_receive` or a blocking `select` case, as in `Cache.Watch`): the next
response sent after `received` (`ok`; `received ++ [r]` is still a prefix of what was sent),
or, once the channel is closed and drained, `!ok` with everything sent received
(`watcherClosed γ received c`). -/
theorem watcher_recv_au (w ch : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) (received : List RespModel)
    (Φ : go_etcd_io.etcd.client.v3.WatchResponse → Bool → IProp GF) :
    ⊢ isWatcher w γ pred Pb -∗ watcherRespChAddr w ↦□ ch -∗ watcherConsumer γ received -∗
      (∀ (resp : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool),
        watcherRecvResult γ Pb received resp ok -∗ Φ resp ok) -∗
      recvAu γ.ch go_etcd_io.etcd.client.v3.WatchResponse Φ := by
  iintro #Hw #Hch' Hcons HΦ
  unfold isWatcher
  iNamed Hw
  icombine HrespCh Hch' gives %Heq
  subst Heq
  unfold recvAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold watcherInv
  iNamed Hi
  unfold watcherConsumer
  icombine Hcons Hrecv gives % ⟨_, Heq⟩
  subst Heq
  iexists s
  iframe Hch
  rcases s with (_ | ⟨v, rest⟩) | _ | _ | _ | _ | _ | (_ | ⟨v, rest⟩)
  all_goals dsimp only
  case Buffered.nil => itrivial
  case SndPending => simp [chanInflight] at Hinfl
  case RcvPending => itrivial
  case SndCommit => itrivial
  case RcvCommit => itrivial
  case Buffered.cons =>
    iintro Hch
    simp only [chanInflight, Option.some.injEq] at Hinfl
    subst Hinfl
    imod watcher_take γ received sent _ _ Hpre $$ [$Hcons $Hrecv $Hvs]
      with ⟨%r, Hcons, Hrecv, #Hr, #Hrest, %Hpre'⟩
    ihave #HPr : iprop(□ Pb.pub none (received ++ [r])) $$ []
    · imodintro; iapply Hpub $$ %_ %Hpre'
    imod Hmask with -
    imod Hclose $$ [Hch Hsent Hrecv Hcl] with -
    · inext
      iexists _, sent, received ++ [r], rest, cl
      simp only [named]
      iframe Hch
      iframe
      iframe #
      ipureintro
      simp_all [chanInflight, chanIsClosed]
    imodintro
    iapply HΦ
    unfold watcherRecvResult
    simp only [↓reduceIte]
    iexists r
    unfold watcherConsumer
    iframe
    iframe #
  case Closed.cons =>
    iintro Hch
    simp only [chanInflight, Option.some.injEq] at Hinfl
    subst Hinfl
    imod watcher_take γ received sent _ _ Hpre $$ [$Hcons $Hrecv $Hvs]
      with ⟨%r, Hcons, Hrecv, #Hr, #Hrest, %Hpre'⟩
    ihave #HPr : iprop(□ Pb.pub none (received ++ [r])) $$ []
    · imodintro; iapply Hpub $$ %_ %Hpre'
    imod Hmask with -
    imod Hclose $$ [Hch Hsent Hrecv Hcl] with -
    · inext
      iexists _, sent, received ++ [r], rest, cl
      simp only [named]
      iframe Hch
      iframe
      iframe #
      ipureintro
      simp_all [chanInflight, chanIsClosed]
    imodintro
    iapply HΦ
    unfold watcherRecvResult
    simp only [↓reduceIte]
    iexists r
    unfold watcherConsumer
    iframe
    iframe #
  case Closed.nil =>
    -- closed and drained: everything sent was received
    iintro Hch
    simp only [chanInflight, Option.some.injEq] at Hinfl
    subst Hinfl
    ihave %Hlen := respsSent_length _ _ $$ Hvs
    have Hd : sent.drop received.length = [] := by
      rw [← List.length_eq_zero_iff]; simpa using Hlen.symm
    have Heq := prefix_drop_nil Hpre Hd
    subst sent
    rcases cl with _ | ⟨sc, c⟩
    · simp [chanIsClosed] at Hclosed
    unfold watcherInvClosed
    icases Hcl with ⟨#Hcl0, Hsent', %Hsc, Htok, Hcl, #HPc⟩
    subst sc
    imod Hmask with -
    imod Hclose $$ [Hch Hsent Hrecv Hsent' Htok Hcl] with -
    · inext
      iexists ChanState.Closed [], received, received, [], some (received, c)
      simp only [named]
      iframe
      ihave #Hnil := respsSent_nil (GF := GF)
      simp only [List.drop_length]
      iframe #
      ipureintro
      exact ⟨List.prefix_refl _, rfl, rfl⟩
    imodintro
    iapply HΦ
    unfold watcherRecvResult
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexists c
    unfold watcherConsumer
    iframe
    iframe #
  case Idle =>
    -- wait for an unbuffered send
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch Hsent Hrecv Hcl] with -
    · inext
      iexists ChanState.RcvPending, sent, received, vs, cl
      simp only [named]
      iframe
      iframe #
      ipureintro; simp_all [chanInflight, chanIsClosed]
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    all_goals first | (solve_ndisj; done) | skip
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iNamed Hi
    iexists s
    iframe Hch
    rcases s with (_ | ⟨v', rest'⟩) | _ | _ | _ | ⟨v'⟩ | _ | (_ | ⟨v', rest'⟩)
    all_goals dsimp only
    all_goals first | itrivial | skip
    case SndCommit =>
      iintro Hch
      icombine Hcons Hrecv gives % ⟨_, Heq⟩
      subst recv
      simp only [chanInflight, Option.some.injEq] at Hinfl
      subst Hinfl
      imod watcher_take γ received sent _ _ Hpre $$ [$Hcons $Hrecv $Hvs]
        with ⟨%r, Hcons, Hrecv, #Hr, #Hrest, %Hpre'⟩
      ihave #HPr : iprop(□ Pb.pub none (received ++ [r])) $$ []
      · imodintro; iapply Hpub $$ %_ %Hpre'
      imod Hmask with -
      imod Hclose $$ [Hch Hsent Hrecv Hcl] with -
      · inext
        iexists ChanState.Idle, sent, received ++ [r], [], cl
        simp only [named]
        iframe Hch
        iframe
        iframe #
        ipureintro
        simp_all [chanInflight, chanIsClosed]
      imodintro
      iapply HΦ
      unfold watcherRecvResult
      simp only [↓reduceIte]
      iexists r
      unfold watcherConsumer
      iframe
      iframe #
    case Closed.nil =>
      -- closed and drained: everything sent was received
      iintro Hch
      icombine Hcons Hrecv gives % ⟨_, Heq⟩
      subst recv
      simp only [chanInflight, Option.some.injEq] at Hinfl
      subst Hinfl
      ihave %Hlen := respsSent_length _ _ $$ Hvs
      have Hd : sent.drop received.length = [] := by
        rw [← List.length_eq_zero_iff]; simpa using Hlen.symm
      have Heq := prefix_drop_nil Hpre Hd
      subst sent
      rcases cl with _ | ⟨sc, c⟩
      · simp [chanIsClosed] at Hclosed
      unfold watcherInvClosed
      icases Hcl with ⟨#Hcl0, Hsent', %Hsc, Htok, Hcl, #HPc⟩
      subst sc
      imod Hmask with -
      imod Hclose $$ [Hch Hsent Hrecv Hsent' Htok Hcl] with -
      · inext
        iexists ChanState.Closed [], received, received, [], some (received, c)
        simp only [named]
        iframe
        ihave #Hnil := respsSent_nil (GF := GF)
        simp only [List.drop_length]
        iframe #
        ipureintro
        exact ⟨List.prefix_refl _, rfl, rfl⟩
      imodintro
      iapply HΦ
      unfold watcherRecvResult
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists c
      unfold watcherConsumer
      iframe
      iframe #

/-- The consumer's `resp, ok := <-w.respCh` as a plain receive (see `watcher_recv_au`). -/
theorem wp_watcher_receive (w ch : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) (received : List RespModel) :
    ⊢ ∀ Φ : val → IProp GF,
      isWatcher w γ pred Pb -∗ watcherRespChAddr w ↦□ ch -∗ watcherConsumer γ received -∗
      (∀ (resp : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool),
        watcherRecvResult γ Pb received resp ok -∗ Φ (PairV #resp #ok)) -∗
      WP (App (Val (chan.receive go_etcd_io.etcd.client.v3.WatchResponse.ty)) (Val #ch)) {{ Φ }} := by
  iintro %Φ #Hw #Hch' Hcons HΦ
  ihave #Hc := isWatcher_isChan w ch γ pred Pb $$ [$Hw $Hch']
  iapply chan.wp_receive ch γ.ch $$ Hc
  iintro -
  iapply watcher_recv_au w ch γ pred Pb received (fun v ok => Φ (PairV #v #ok)) $$ Hw Hch' Hcons HΦ

/-- After the channel is closed (the consumer saw `!ok`), `w.cancelResp` holds the cancel
response of the close: nil (`Stop`) or the compaction response of `Compact(rev)`. -/
theorem wp_watcher_cancelResp (w : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) (sent : List RespModel) (c : Option w64) :
    ⊢ ∀ Φ : val → IProp GF,
      isWatcher w γ pred Pb -∗ watcherClosed γ sent c -∗ (∀ p : Loc, cancelAt p c -∗ Φ #p) -∗
      WP (App (Val (GoInstruction (GoLoad (go.GoType.PointerType go_etcd_io.etcd.client.v3.WatchResponse.ty))))
        (Val #(watcherCancelRespAddr w))) {{ Φ }} := by
  iintro %Φ #Hw #Hcl0 HΦ
  unfold isWatcher
  iNamed Hw
  ihave Hp : |={⊤}=> ∃ p, watcherCancelRespAddr w ↦□ p ∗ cancelAt p c $$ []
  · iinv Hinv with >Hi Hclose
    iNamed Hi
    rcases cl with _ | ⟨sc, c'⟩
    · unfold watcherInvClosed watcherClosed
      ihave %H := dghostVar_agree _ _ _ _ _ $$ Hcl Hcl0
      cases H
    unfold watcherInvClosed
    icases Hcl with ⟨#Hcl1, Hs', %Hsc, Htok, ⟨%p, #Hp, #Hc⟩, #HPc⟩
    unfold watcherClosed
    ihave %Hag := dghostVar_agree _ _ _ _ _ $$ Hcl0 Hcl1
    simp only [Option.some.injEq, Prod.mk.injEq] at Hag
    obtain ⟨-, rfl⟩ := Hag
    imod Hclose $$ [Hch Hsent Hrecv Hs' Htok] with -
    · inext
      unfold watcherInv
      iexists s, sent, recv, vs, some (sc, c)
      simp only [named]
      iframe
      unfold watcherInvClosed watcherClosed
      dsimp only
      iframe
      iframe #
      ipureintro; exact ⟨Hpre, Hinfl, Hclosed, Hsc⟩
    imodintro
    iexists p
    iframe #
  imod Hp with ⟨%p, #Hp, #Hc⟩
  wp_load
  iapply HΦ $$ Hc

/-- What the consumer has received is a prefix of what the producer has sent. -/
theorem watcher_received_prefix (w : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) (sent0 received0 : List RespModel) :
    isWatcher (GF := GF) w γ pred Pb ∗ watcherOpen γ sent0 ∗ watcherConsumer γ received0 ⊢
      |={⊤}=> watcherOpen γ sent0 ∗ watcherConsumer γ received0 ∗ ⌜received0 <+: sent0⌝ := by
  iintro ⟨#Hw, Hopen, Hcons⟩
  unfold isWatcher
  iNamed Hw
  iinv Hinv with >Hi Hclose
  iNamed Hi
  unfold watcherOpen watcherConsumer
  icases Hopen with ⟨Hs, Hc⟩
  icombine Hs Hsent gives % ⟨_, Heq1⟩
  icombine Hcons Hrecv gives % ⟨_, Heq2⟩
  subst sent recv
  imod Hclose $$ [Hch Hsent Hrecv Hcl] with -
  · inext
    unfold watcherInv
    iexists s, sent0, received0, vs, cl
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hpre, Hinfl, Hclosed⟩
  imodintro
  iframe
  ipureintro; exact Hpre

/-- Once closed after `sent0`, what the consumer has received is a prefix of `sent0`. -/
theorem watcher_received_prefix_closed (w : Loc) (γ : WatcherNames)
    (pred : Option (GoString → Bool)) (Pb : WatcherPub GF) (sent0 received0 : List RespModel)
    (c0 : Option w64) :
    isWatcher (GF := GF) w γ pred Pb ∗ watcherClosed γ sent0 c0 ∗ watcherConsumer γ received0 ⊢
      |={⊤}=> watcherConsumer γ received0 ∗ ⌜received0 <+: sent0⌝ := by
  iintro ⟨#Hw, #Hcl0, Hcons⟩
  unfold isWatcher
  iNamed Hw
  iinv Hinv with >Hi Hclose
  iNamed Hi
  unfold watcherConsumer
  icombine Hcons Hrecv gives % ⟨_, Heq2⟩
  subst recv
  rcases cl with _ | ⟨sc, c'⟩
  · unfold watcherInvClosed watcherClosed
    ihave %H := dghostVar_agree _ _ _ _ _ $$ Hcl Hcl0
    cases H
  unfold watcherInvClosed watcherClosed
  icases Hcl with ⟨#Hcl1, Hs', %Hsc, Htok, Hrest⟩
  ihave %Hag := dghostVar_agree _ _ _ _ _ $$ Hcl0 Hcl1
  simp only [Option.some.injEq, Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  subst Hsc
  imod Hclose $$ [Hch Hsent Hrecv Hs' Htok Hrest] with -
  · inext
    unfold watcherInv
    iexists s, sent0, received0, vs, some (sent0, c0)
    simp only [named]
    iframe
    unfold watcherInvClosed watcherClosed
    dsimp only
    iframe
    iframe #
    ipureintro; exact ⟨Hpre, Hinfl, Hclosed, rfl⟩
  imodintro
  iframe
  ipureintro; exact Hpre

/-- The producer's view is exclusive (the invariant holds the other half of the log): two
`watcherOpen γ` cannot both exist. (For the demux's `Register`: a watcher registered twice.) -/
theorem watcherOpen_excl (w : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) (sent1 sent2 : List RespModel) :
    isWatcher (GF := GF) w γ pred Pb ∗ watcherOpen γ sent1 ∗ watcherOpen γ sent2 ⊢ |={⊤}=> False := by
  iintro ⟨#Hw, Ho1, Ho2⟩
  unfold isWatcher
  iNamed Hw
  iinv Hinv with >Hi Hclose
  iNamed Hi
  unfold watcherOpen
  icases Ho1 with ⟨Hs1, -⟩
  icases Ho2 with ⟨Hs2, -⟩
  icombine Hs1 Hs2 as Hs12
  ihave %Hv := ghostVar_valid_2 _ _ _ _ _ $$ Hs12 Hsent
  exfalso
  obtain ⟨Hq, -⟩ := Hv
  have h' : ((1 : Qp) + (1 : Qp).half).val ≤ (1 : Qp).val := Hq
  simp at h'
  grind

/-! ## Freshness of a new watcher -/

/-- `w` is a watcher that `newWatcher` has just made (exclusive): half of `w.keyPred`'s points-to,
whose other half `isWatcher` keeps read-only. Two of them for one `w` contradict
(`watcherUnique_excl`), so whoever holds it knows `w` is not one of the watchers it holds
otherwise (the demux's `Register`: not registered yet; each registration keeps its own). -/
def watcherUnique (w : Loc) : IProp GF :=
  iprop(∃ f : GoFunc, watcherKeyPredAddr w ↦{DFrac.own (1 : Qp).half} f)

theorem dfrac_half_half_discard_invalid :
    ¬ ✓ ((DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half) • DFrac.discard) := by
  rw [DFrac.op_own, Qp.half_add_half]
  intro h
  have := DFrac.valid_own_op h
  have : (1 : Qp).val = 1 := rfl
  grind

theorem keyPred_halves_false (l : Loc) (f0 f1 f2 : GoFunc) :
    typedPointsto (GF := GF) l f1 (DFrac.own (1 : Qp).half) ∗
      typedPointsto l f2 (DFrac.own (1 : Qp).half) ∗ typedPointsto l f0 DFrac.discard ⊢ False := by
  iintro ⟨H1, H2, H0⟩
  icombine H1 H0 gives %He1
  icombine H2 H0 gives %He2
  subst He1 He2
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  icases H0 with ⟨H0, -⟩
  simp only [typedPointstoDef_heap]
  ihave H12 := ((heapPointsto_dfractional l #f2).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)).2 $$ [$H1 $H2]
  ihave H := ((heapPointsto_dfractional l #f2).dfractional
    (DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half) DFrac.discard).2 $$ [$H12 $H0]
  ihave %Hv := heapPointsto_valid _ _ _ $$ H
  exact absurd Hv dfrac_half_half_discard_invalid

/-- Two `watcherUnique w` contradict, for a watcher `w`. -/
theorem watcherUnique_excl (w : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool))
    (Pb : WatcherPub GF) :
    isWatcher (GF := GF) w γ pred Pb ∗ watcherUnique w ∗ watcherUnique w ⊢ False := by
  unfold watcherUnique
  iintro ⟨#Hw, ⟨%f1, H1⟩, ⟨%f2, H2⟩⟩
  unfold isWatcher
  iNamed Hw
  iapply keyPred_halves_false (watcherKeyPredAddr w) f f1 f2 $$ [$H1 $H2 $HkeyPred]

end lemmas

end EtcdGrove
end Perennial
