/-
# The watch path over mvcc's API (round 14): v3rpc's and client/v3's changed statements (draft)

Scratch (outside the repository, never committed); typechecks with `lake env lean FILE` from the
worktree `mvcc-api`. Names are under `v3rpc.W14` (and `client.W14`) to sit beside today's;
adopted, they drop the prefix and replace today's of the same name (`WatchRespM2` -> `WatchRespM`,
`mvccOk2` -> `mvccOk`, ...). The design and the gaps: `~/mvcc-api-candidates/clients-watch.md`.

Contents:
* §1 what the server must give the watch path (`SrvW`, `srvWOk`): parameters the server's draft
  defines, and their laws;
* §2 the pure models restated (a response's source is its index in the consumer's received list
  and its `WResp`; the registry's entry `RegInfo`);
* §3 one run's names and v3rpc's shared invariant `wsInv` (holding `wsState`);
* §4 the per-message stream spec (`mvccOk2`, `ctrlWatcher2`, `createdAfter2`, `watchDn2`);
* §5 what the client's content of a request gives (`upOk2`: no watch token, no `watchNoDup`);
* §6 the run's persistent facts (`swsIs2`) and the four specs that change;
* §7 the proof obligations the API introduces in v3rpc (statements only: the updates passed to
  `Watch`/`Cancel`/`Close`, the snapshot after a receive, the drain);
* §8 client/v3's changed bridge statements.
-/
import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__sendLoop
import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__close
import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__recvLoop
import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer__Watch
import Proof.go_etcd_io.etcd.client.v3.InvWatch

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc
namespace W14

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc (watchServer serverWatchStream)

/-! ## §2 The pure models -/

instance WResp.countable : Pos.Countable mvcc.api.WResp :=
  .ofInjective (fun r => Pos.Countable.encode (r.id, r.evs, r.rev, r.compactRev))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- **A watch response as the wire carries it, with its mvcc source** (ghost, not on the wire):
`none` for a control response; for one of the mvcc stream's, its index `n` in the send loop's
received list and the response (today's `src : Option mvcc.RespM`, whose ghost `w`, `cov`, `regs`,
`idx` the API has no counterpart of). The fields on the wire are `WatchRespM`'s. -/
structure WatchRespM2 where
  hdr : HdrM
  watchId : w64
  created : Bool
  canceled : Bool
  compactRev : w64
  cancelReason : GoString
  fragment : Bool
  evs : List mvcc.EvM
  src : Option (Nat × mvcc.api.WResp)

/-- The wire fields (today's model with no ghost source): what `watchRespMsg` holds. -/
def WatchRespM2.wire (m : WatchRespM2) : WatchRespM :=
  { hdr := m.hdr, watchId := m.watchId, created := m.created, canceled := m.canceled,
    compactRev := m.compactRev, cancelReason := m.cancelReason, fragment := m.fragment,
    evs := m.evs, src := none }

instance WatchRespM2.countable : Pos.Countable WatchRespM2 :=
  .ofInjective (fun m => Pos.Countable.encode ((m.hdr.clusterId, m.hdr.memberId, m.hdr.revision,
      m.hdr.raftTerm, m.hdr.leaderId), m.watchId, m.created, m.canceled, m.compactRev,
      m.cancelReason, m.fragment, m.evs, m.src))
    (fun a b h => by
      have := Pos.encode_inj h
      rcases a with ⟨⟨_, _, _, _, _⟩, _, _, _, _, _, _, _, _⟩
      rcases b with ⟨⟨_, _, _, _, _⟩, _, _, _, _, _, _, _, _⟩
      simp_all)

/-- The response the send loop makes of the `n`-th received response `x` with the header `h`
(today's `mvccResp`). -/
def mvccResp2 (n : Nat) (x : mvcc.api.WResp) (h : HdrM) : WatchRespM2 :=
  { hdr := h, watchId := x.id, created := false, canceled := decide (x.compactRev ≠ W64 0),
    compactRev := x.compactRev, cancelReason := [], fragment := false, evs := x.evs,
    src := some (n, x) }

/-- What a control response answers: today's, on the wire fields, with no source. -/
def ctrlAnswers2 (req : WatchReqM) (m : WatchRespM2) : Prop :=
  m.src = none ∧ ctrlAnswers req m.wire

/-- The watch id `X` is live after `L` (today's `idLive`). -/
def idLive2 (L : List WatchRespM2) (X : w64) : Prop :=
  ((L.filter (fun m => decide (m.src = none ∧ m.watchId = X))).getLast?.map
    (fun m => m.created && !m.canceled)) = some true

/-- The mvcc responses with events of the id `X` among `L` (today's `sentEvsOf`, by id: ids are
never reused on a stream, `StreamState.cancel` keeps the entry). -/
def sentEvsOf2 (L : List WatchRespM2) (X : w64) : List mvcc.api.WResp :=
  ((L.filterMap WatchRespM2.src).map Prod.snd).filter fun x => decide (x.id = X ∧ x.evs ≠ [])

/-- What was forwarded of the id `X` before the response `x` received after `pre` (today's
`fwdEvs`, by id). -/
def fwdEvs2 (L : List WatchRespM2) (pre : List mvcc.api.WResp) (x : mvcc.api.WResp) (X : w64) :
    Prop :=
  X ≠ W64 (-1) → idLive2 L X → (x.id = X ∨ x.id = W64 (-1)) →
    sentEvsOf2 L X = (pre.filter (fun y => decide (y.id = X))).filter (fun y => decide (y.evs ≠ []))

/-- The responses sent before the `n`-th received one, while its id was live (any, for `-1`), were
received before it (today's `fwdIdx`). -/
def fwdIdx2 (L : List WatchRespM2) (n : Nat) (x : mvcc.api.WResp) : Prop :=
  ∀ (i : Nat) (m' : WatchRespM2) (n' : Nat) (y : mvcc.api.WResp), L[i]? = some m' →
    m'.src = some (n', y) → (x.id = W64 (-1) ∨ idLive2 (L.take i) x.id) → n' < n

/-- **A registry entry**: what v3rpc records of a watcher at `Watch`'s commit (the `WInfo` but its
filters, `[]` for every watcher of the server, and its liveness, which only `wsState` has). -/
structure RegInfo where
  rg : mvcc.WatchRange
  lo : Nat
  k : Nat

instance RegInfo.countable : Pos.Countable RegInfo :=
  .ofInjective (fun r => Pos.Countable.encode (r.rg, r.lo, r.k))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

def regInfoOf (w : mvcc.api.WInfo) : RegInfo := ⟨w.rg, w.lo, w.k⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## §1 What the server must give the watch path

The server's draft defines these (its names may differ; the laws are what the watch path uses). -/

/-- **The server's side of the watch path**: the store's name, the namespace of the server's
invariant holding `mvccState`, the notified log's certified lower bound `histLb` (replacing
`mvcc.evLog`: `idxSealed ∗ certOk`), and the compaction revision's permit `crevOk` (replacing
`mvcc.crevPermAt` as the watch path reads it). -/
structure SrvW (GF : BundledGFunctors) where
  /-- the store's handle the server's invariant holds (the server draft's `E.kv`) -/
  kv : GoInterface
  γm : mvcc.api.MvccName
  N : Namespace
  histLb : mvcc.Log → IProp GF
  crevOk : Int → IProp GF

/-- **The server's peek** (persistent): at any mask containing its namespace, the store's state
`σ` (left unchanged), with the certified lower bound of its notified log and its compaction
revision's permit. What `Watch`'s and `Rev`'s updates and the send loop's snapshot open; all three
give `mvccState γ σ` back unchanged. -/
def srvPeek (W : SrvW GF) : IProp GF :=
  iprop(□ ∀ (E : CoPset), ⌜↑W.N ⊆ E⌝ -∗ |={E, E \ ↑W.N}=> ∃ σ : mvcc.api.MvccState,
    mvcc.api.mvccState W.γm σ ∗ W.histLb σ.notifiedLog ∗ W.crevOk σ.crev ∗
    (mvcc.api.mvccState W.γm σ ={E \ ↑W.N, E}=∗ True))

/-- **What the server gives the watch path** (persistent): the store's handle, which is the
watchable store at `wsl` (`E.kv = wsIface wsl`, xreview §6c: `shapes.law`'s per-type conjunct then
gives `NewWatchStream`'s contract, which `isMvcc` alone does not), the peek, its namespace outside `mvccN` (so it opens
inside `Watch`'s update, at `⊤ \ ↑mvccN`) and outside v3rpc's (`wsN`), and the laws of `histLb`
(agreement, prefix closure; and, round 16, a certified log's model facts: well formed and of fewer
than `2 ^ 63` revisions, from `mvccState_reachable` at the state it was taken of, small from the
receipt `⧖ (logCh σ.notifiedLog)` the server keeps with it (the API's notify steps give it) and
`receiptBound GF ≤ 2 ^ 62`, its keys short from the server's request checks: today's
`idxSealed_pure`, `sealed_logOk`, `srvLogsSmall`, `srvKVCoreM_keys`) and of `crevOk`
(no permit, or a positive revision's, downward closed; `kvCmpPermit_le`'s use). The client's
model laws over `histLb` (today's `watchLaws_srv` over `evLog`) are in §8. -/
def srvWOk (W : SrvW GF) (wsl : Loc) (wsN : Namespace) : IProp GF :=
  iprop(⌜W.kv = wsIface wsl⌝ ∗ mvcc.api.isMvcc W.kv W.γm ∗ srvPeek W ∗
    ⌜(↑W.N : CoPset) ⊆ ⊤ \ ↑mvcc.api.mvccN ∧ (↑wsN : CoPset) ⊆ ⊤ \ ↑mvcc.api.mvccN ∧
      (↑wsN : CoPset) ⊆ ⊤ \ ↑W.N⌝ ∗
    (□ ∀ L, W.histLb L -∗ □ W.histLb L) ∗
    (□ ∀ L L', W.histLb L -∗ W.histLb L' -∗ ⌜L <+: L' ∨ L' <+: L⌝) ∗
    (□ ∀ L L', ⌜L' <+: L⌝ -∗ W.histLb L -∗ W.histLb L') ∗
    (□ ∀ L, W.histLb L -∗ ⌜mvcc.LogWf' L ∧ L.length < 2 ^ 63 ∧ txn.LogSmall L ∧
      mvcc.LogPutsLe etcdKeyMax L⌝) ∗
    (□ ∀ c, W.crevOk c -∗ □ W.crevOk c))

/-- **The watch condition, the client's premise** (replacing `mvcc.watchNoDup`, which no longer
goes through v3rpc: the API states the watch facts under `onceUpTo`, and v3rpc forwards them
conditionally): every certified log and permitted compaction revision meet `onceUpTo` at every
first revision. Holds of a server that never compacts (`crevOk c → c = -1`: vacuous) and of one
whose revisions change each key at most once (`srvNoDupKeys`). -/
def srvOnce (W : SrvW GF) : IProp GF :=
  iprop(□ ∀ (L : mvcc.Log) (c : Int) (lo : Nat), W.histLb L -∗ W.crevOk c ={⊤}=∗
    ⌜mvcc.api.onceUpTo L lo c⌝)

/-! ## §3 One run's names and v3rpc's shared invariant -/

/-- **One run's mvcc-side values** (replacing `WRun`'s `wsp`, `γo`, `ch`, `γc`): the stream's handle
`wsp` (a `*watchStream`), its name `ι`, the registry `γreg` (id ↦ `RegInfo`, discarded entries),
the id tokens `γtok` (one per registered id: today's `idTok`), the received list `γr` (a mono list
of `WResp`, the send loop's authority), the close token `γcl`. The rest of `WRun` is unchanged
(`srv`, `st`, `γs`, `Up`, `Dn` at `WatchRespM2`, `ci`, `cd`, `γa`, `ctrl`, `γctrl`, `pm`, `vm`,
`fm`, `cc`, `γcc`). -/
structure WRunA (GF : BundledGFunctors) where
  srv : WSrv GF
  W : SrvW GF
  γs : StreamNames
  wsp : Loc
  ι : mvcc.api.WsName
  γreg : GName
  γtok : GName
  γr : GName
  γcl : GName
  γa : GName

/-- The run's ghost names its stream's auxiliary name publishes (today's `auxOf`; `ι` is not a
`GName`, and no client needs it). -/
def auxOf2 (r : WRunA GF) : List GName := [r.γreg, r.γtok, r.γr, r.γa]

/-- The registry's entry (persistent). -/
def regIs (γreg : GName) (id : w64) (i : RegInfo) : IProp GF :=
  ghostMapElem γreg id DFrac.discard i

/-- The id's token (exclusive; a stream announces an id once). -/
def idTok2 (γtok : GName) (id : w64) : IProp GF := ghostMapElem γtok id (DFrac.own 1) ()

/-- The send loop's received list has `l` first (persistent). -/
def rcvLb (γr : GName) (l : List mvcc.api.WResp) : IProp GF := monoListLbOwn γr l

/-- The close token (exclusive; `close`'s until it closes the stream). -/
def closeTok (γcl : GName) : IProp GF := dghostVar γcl (DFrac.own 1) ()

/-- The namespace of v3rpc's per-run invariant. -/
def wsN : Namespace := (nroot .@ "v3rpc") .@ "ws"

/-- **v3rpc's invariant of a run** (shared by `recvLoop`, `sendLoop`, `close`; all timeless but the
cancel facts, which are persistent): the stream's state `S`; the registry agrees with `S` (every
watcher's `RegInfo`, its discarded entries kept, so the snapshot can copy them; the id tokens
minted for exactly `S`'s ids); every watcher unfiltered;
every watcher not live was cancelled at the client's request (`cancelQ`: the reason today's
`Ψ`/`rsnFor` carried); the stream open, or the close token deposited. -/
def wsInv (r : WRunA GF) : IProp GF :=
  iprop(∃ (S : mvcc.api.StreamState) (R : GMap w64 RegInfo) (T : GMap w64 Unit),
    mvcc.api.wsState r.ι S ∗ ghostMapAuth r.γreg 1 R ∗ ghostMapAuth r.γtok 1 T ∗
    ⌜∀ id, R !! id = (S.ws !! id).map regInfoOf ∧ ((T !! id).isSome ↔ (S.ws !! id).isSome)⌝ ∗
    ⌜∀ id w, S.ws !! id = some w → w.fs = []⌝ ∗
    □ ([∗map] id ↦ i ∈ R, regIs r.γreg id i) ∗
    ([∗map] id ↦ w ∈ S.ws, ⌜w.live = true⌝ ∨ cancelQ r.γs id) ∗
    (⌜S.closed = false⌝ ∨ closeTok r.γcl))

/-! ## §4 The per-message stream spec -/

/-- **The send loop's snapshot of the received responses `rs`** (persistent; made right after the
receive of `rs`'s last, `snap_after_recv`): the API's watch guarantee at some state `σ` and stream
state `S` of that moment, the notified log's certified lower bound and the compaction revision's
permit at it, each of `S`'s watchers registered (`regIs`) and live or cancelled at the client's
request. -/
def rcvSnap (r : WRunA GF) (rs : List mvcc.api.WResp) (σ : mvcc.api.MvccState)
    (S : mvcc.api.StreamState) : IProp GF :=
  iprop(⌜mvcc.api.wsRecvOk σ S rs ∧ ∀ id w, S.ws !! id = some w → w.fs = []⌝ ∗
    r.W.histLb σ.notifiedLog ∗ r.W.crevOk σ.crev ∗
    □ ([∗map] id ↦ w ∈ S.ws, regIs r.γreg id (regInfoOf w) ∗ (⌜w.live = true⌝ ∨ cancelQ r.γs id)))

/-- **A response of the mvcc watch stream sent at position `j`** (persistent; today's `mvccOk` with
`mvccExtra`, `mvccCov`): the response of the `n`-th received response `x` (after `pre`), its
header's revision `x`'s, its id (unless `-1`) live after the `j` responses `L` sent before it; the
received list's lower bound and the snapshot at `pre ++ [x]`; for a `-1` response, every id live
after `L` is a watcher of the snapshot's `S` (its created response was sent before the receive, so
it registered before the snapshot); if `x` has events, its id's responses with events sent before
`j`, then `x`, are its id's responses with events received; no response before it came from `n`;
what was forwarded before it (`fwdEvs2`, `fwdIdx2`). -/
def mvccOk2 (r : WRunA GF) (j : Nat) (m : WatchRespM2) : IProp GF :=
  iprop(∃ (n : Nat) (x : mvcc.api.WResp) (pre : List mvcc.api.WResp) (L : List WatchRespM2)
      (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState),
    ⌜m = mvccResp2 n x m.hdr ∧ m.hdr.revision = x.rev ∧ L.length = j ∧ pre.length = n ∧
      (x.id ≠ W64 (-1) → idLive2 L x.id) ∧
      (x.id = W64 (-1) → ∀ X, idLive2 L X → X ≠ W64 (-1) → (S.ws !! X).isSome) ∧
      (x.evs ≠ [] → sentEvsOf2 L x.id ++ [x] =
        ((pre ++ [x]).filter (fun y => decide (y.id = x.id))).filter (fun y => decide (y.evs ≠ []))) ∧
      (∀ m' ∈ L, ∀ y, m'.src ≠ some (n, y)) ∧ fwdIdx2 L n x ∧
      (∀ X, fwdEvs2 L pre x X)⌝ ∗
    monoListLbOwn r.γs.down L ∗ rcvLb r.γr (pre ++ [x]) ∗
    rcvSnap r (pre ++ [x]) σ S)

/-- **The watcher a created response names** (today's `ctrlWatcher`): for a create request `c`
answered by a registered response `m`, its registry entry (the range of the request and the
response's id; its first revision the start revision, or for `0` the length of a certified
notified log, `σ.log` at the registration with nothing pending), its id token, the request's
authorization (unchanged), and the stream's sent count at the registration (`wsSentLb ι k`, what
the send loop's drain matches; the client needs only `RegInfo.k`). -/
def ctrlWatcher2 (r : WRunA GF) (tok : Option GoString) (req : WatchReqM) (m : WatchRespM2) :
    IProp GF :=
  match req with
  | .create c => if m.canceled then iprop(True) else
      iprop(∃ i : RegInfo, ⌜createRangeOk c m.watchId i.rg⌝ ∗ regIs r.γreg m.watchId i ∗
        idTok2 r.γtok m.watchId ∗ mvcc.api.wsSentLb r.ι i.k ∗
        (if c.startRev = W64 0 then ∃ Lr : mvcc.Log, r.W.histLb Lr ∗ ⌜i.lo = Lr.length⌝
         else iprop(⌜i.lo = sint.nat c.startRev⌝)) ∗
        watchAuthed r.srv.γ r.srv.s tok c.bound c.key c.rangeEnd)
  | _ => iprop(True)

/-- **A created response sent at `j` follows the `-1` responses received before the watcher's
stamp** (today's `createdAfter`, from the drain, now with `wsChan_tryRecv`): the send loop had
received `l` (at least the stamp `k` responses) and sent every `-1` among them before `j`. -/
def createdAfter2 (r : WRunA GF) (j : Nat) (m : WatchRespM2) : IProp GF :=
  if m.created && !m.canceled then
    iprop(∃ (i : RegInfo) (l : List mvcc.api.WResp) (L : List WatchRespM2),
      regIs r.γreg m.watchId i ∗ rcvLb r.γr l ∗ monoListLbOwn r.γs.down L ∗
      ⌜i.k ≤ l.length ∧ L.length = j ∧
        ∀ (n : Nat) (x : mvcc.api.WResp), l[n]? = some x → x.id = W64 (-1) →
          ∃ m' ∈ L, m'.src = some (n, x)⌝)
  else iprop(True)

/-- A control response (today's `ctrlOk`). -/
def ctrlOk2 (r : WRunA GF) (tok : Option GoString) (m : WatchRespM2) : IProp GF :=
  iprop(∃ (i : Nat) (req : WatchReqM), upAtW r.γs i req ∗ ⌜ctrlAnswers2 req m⌝ ∗
    ctrlWatcher2 r tok req m ∗ ansTok r.γa i)

/-- **What the watch server says of its `j`th response** (today's `watchDn`): the run's names
published (`streamAuxIs`), the header's ids, and a control response or an mvcc one. The run is
existential, as today's `γo`: the client agrees on it through `streamAuxIs`. -/
def watchDn2 (γs : StreamNames) (R : WSrv GF) (W : SrvW GF) (tok : Option GoString)
    (j : Nat) (m : WatchRespM2) : IProp GF :=
  iprop(∃ r : WRunA GF, ⌜r.srv = R ∧ r.W = W ∧ r.γs = γs⌝ ∗ streamAuxIs γs (auxOf2 r) ∗
    ⌜m.hdr.clusterId = R.cid ∧ m.hdr.memberId = R.mid⌝ ∗
    ((⌜m.src = none⌝ ∗ ctrlOk2 r tok m ∗ createdAfter2 r j m) ∨ mvccOk2 r j m))

def watchStreamSpec2 (γs : StreamNames) (R : WSrv GF) (W : SrvW GF) (tok : Option GoString)
    (Dn : Nat → WatchRespM2 → IProp GF) : IProp GF :=
  iprop(□ ∀ (j : Nat) (m : WatchRespM2), Dn j m ∗-∗ watchDn2 γs R W tok j m)

/-- The watch responses on the wire, at the model with the new source. -/
abbrev pbWatchResponse2 : StreamMsg GF where
  ty := etcdserverpb.WatchResponse.ty
  M := WatchRespM2
  cnt := inferInstance
  send l m := watchRespMsg l m.wire
  recv l m := watchRespRecv l m.wire
  own l := iprop(∃ v : etcdserverpb.WatchResponse, l ↦ v)

/-! ## §5 The client's content of a request -/

/-- **What the client's content of a request gives the server** (today's `upOk` without the watch
token, D19b's watcher budget, which the API's `Watch` does not take, and without `watchNoDup`,
which v3rpc no longer needs: the client discharges `onceUpTo` itself, `srvOnce`). `watchReqOk`
unchanged. -/
def upOk2 (M : auth.AuthMode) (Up : Nat → WatchReqM → IProp GF) : IProp GF :=
  iprop(□ ∀ (i : Nat) (m : WatchReqM), Up i m -∗ ⌜watchReqOk m⌝ ∗
    (match m with
     | .create c => □ auth.authPubLbM M c.bound
     | _ => iprop(True)))

def watchUp2 (R : WSrv GF) (_i : Nat) (m : WatchReqM) : IProp GF :=
  iprop(⌜watchReqOk m⌝ ∗
    (match m with
     | .create c => □ auth.authPubLbM R.E.authMode c.bound
     | _ => iprop(True)))

/-! ## §6 The run's facts and the specs that change -/

/-- **The run's `serverWatchStream` `sws`** (persistent; today's `swsIs` with its mvcc part
replaced): the fields (unchanged, `swsIs`'s first fifteen conjuncts, here the two that change),
the stream and its spec at the new model, the client's content (`upOk2`), the mvcc stream
(`isMvccWatchStream`, its interface value the field's), the run's invariant (`wsInv`), the
server's side (`srvWOk`); the control stream, `closec`, `mu` unchanged (`isSpsc` over `ctrlP` at
`ctrlOk2`, by reference). -/
def swsIs2 (sws : Loc) (r : WRunA GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM2 → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(⌜sws ≠ null⌝ ∗
    swsF sws go!"gRPCStream" ↦□ st ∗
    swsF sws go!"watchStream" ↦□ wspIface r.wsp ∗
    -- (the other thirteen fields as `swsIs`)
    srvStreamIs st r.γs pbWatchRequest pbWatchResponse2 Up Dn ci cd ∗
    watchStreamSpec2 r.γs r.srv r.W (auth.ctxTokenOf (GoInterface.ok ci)) Dn ∗
    streamAuxIs r.γs (auxOf2 r) ∗
    upOk2 r.srv.E.authMode Up ∗
    mvcc.api.isMvccWatchStream (wspIface r.wsp) r.W.γm r.ι ∗
    inv wsN (wsInv r) ∗
    srvWOk r.W r.srv.wsl wsN)

/-- **`sws.recvLoop()`** (changed): the receive loop now holds a thread token (the API's `Watch`,
`Cancel`, `Rev`, `RequestProgressAll` take one; today it held a reader slot, `recvRes`'s
`watchReader`, which goes). Its other resources unchanged. -/
abbrev recvLoop.spec : Prop :=
  ∀ (sws : Loc) (r : WRunA GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM2 → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (L : List WatchReqM) (γctrl : SpscNames)
    (sent : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      swsIs2 sws r Up Dn st ci cd ∗ srvRecvTok (Req := pbWatchRequest) r.γs L ∗
      spscProducer γctrl sent ∗ ansPool r.γa L.length ∗ r.srv.E.RD ∗ threadTok }}
    (App (Val (sws @!! go.GoType.PointerType serverWatchStream.ty @!! go!"recvLoop")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil ∨ context.isTypedErr err⌝ ∗
      threadTok ∗ ∃ sent' : List Loc, spscProducer γctrl sent' }}

/-- **`sws.sendLoop()`** (changed): the consumer's `wsRecv ι []` and the received list's authority
at `[]` in place of `watchConsumer`; no reader slot (`sendRes`'s `watchReader` goes; the thread
bound stays, for `GetProgressReportInterval`). -/
abbrev sendLoop.spec : Prop :=
  ∀ (sws : Loc) (r : WRunA GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM2 → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (γctrl : SpscNames) (pm vm fm : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      swsIs2 sws r Up Dn st ci cd ∗ srvSendTok (Rep := pbWatchResponse2) r.γs [] ∗
      spscConsumer γctrl ([] : List Loc) ∗ mvcc.api.wsRecv r.ι [] ∗
      monoListAuthOwn r.γr 1 ([] : List mvcc.api.WResp) ∗
      ⌜threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders⌝ ∗
      sync.ownRWMutex (swsF sws go!"mu") (swsMu pm vm fm) ∗ threadTok }}
    (App (Val (sws @!! go.GoType.PointerType serverWatchStream.ty @!! go!"sendLoop")) (Val #()))
  {{ RET #(); threadTok }}

/-- **`sws.close()`** (changed): the close token in place of mvcc's `watchStreamOpen`; and a thread
token (the API's `Close` takes one). -/
abbrev close.spec : Prop :=
  ∀ (sws : Loc) (r : WRunA GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM2 → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (cc : Loc) (γcc : ChanNames) (n : w32) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      swsIs2 sws r Up Dn st ci cd ∗ closeTok r.γcl ∗ threadTok ∗
      ownBroadcastChan cc γcc iprop(True) .Pending ∗
      sync.join.ownAdder (swsF sws go!"wg") n P }}
    (App (Val (sws @!! go.GoType.PointerType serverWatchStream.ty @!! go!"close")) (Val #()))
  {{ RET #(); threadTok }}

/-- **`ws.Watch(stream)`** (changed): the stream at the new model and spec (`watchStreamSpec2`, at
the server's side `W`), the client's content `upOk2`, the server's side (`srvWOk`, with v3rpc's
namespace); the run's resources: the auth reader (`R.E.RD`) and the thread bound (no reader
slots: `watchRunSlot` becomes `R.E.RD ∗ ⌜threadBound ...⌝`); and the handler's thread token. It
allocates the run's names and `wsInv` from `NewWatchStream`'s `wsState ι wsStart`. -/
abbrev watchServer.Watch.spec : Prop :=
  ∀ (p : Loc) (R : WSrv GF) (W : SrvW GF) (st : GoInterface) (γs : StreamNames)
    (Up : Nat → WatchReqM → IProp GF) (Dn : Nat → WatchRespM2 → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ∗ srvWOk W R.wsl wsN ∗
      srvStreamIs st γs pbWatchRequest pbWatchResponse2 Up Dn ci cd ∗
      watchStreamSpec2 γs R W (auth.ctxTokenOf (GoInterface.ok ci)) Dn ∗
      upOk2 R.E.authMode Up ∗
      srvRecvTok (Req := pbWatchRequest) γs [] ∗ srvSendTok (Rep := pbWatchResponse2) γs [] ∗
      streamAuxTok γs ∗ R.E.RD ∗ ⌜threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders⌝ ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType watchServer.ty @!! go!"Watch")) (Val #st))
  {{ (err : GoInterface), RET #err; threadTok ∗
      watchStreamSpec2 γs R W (auth.ctxTokenOf (GoInterface.ok ci)) Dn }}

/-! ## §7 The proof obligations the API introduces in v3rpc (statements) -/

/-- **The update `recvLoop` passes to `Watch`** (O1): from the run's invariant and the server's
peek, at `⊤ \ ↑mvccN` (both namespaces are inside it, `srvWOk`). At the commit, the registry and
the id tokens get `id` (fresh: `S.ws !! id = none`), the watcher is live, unfiltered. (`kk`, `e`, `endk`: the key, range end and its slice `recvLoop` passes, `createRangeOk`'s.) -/
def watch_au.stmt : Prop :=
  ∀ (sws : Loc) (r : WRunA GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM2 → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (c : CreateReqM) (kk e : List w8) (endk : GoSlice),
  swsIs2 sws r Up Dn st ci cd ⊢
    AU <{ ∃∃ (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState),
          mvcc.api.mvccState r.W.γm σ ∗ mvcc.api.wsState r.ι S }> @ ⊤ \ ↑mvcc.api.mvccN, ∅
      <{ ∀∀ (id : w64) (k : Nat), mvcc.api.mvccState r.W.γm σ ∗
          (if S.closed then ⌜id = W64 (-1)⌝ ∗ mvcc.api.wsState r.ι S
           else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ mvcc.api.wsSentLb r.ι k ∗
             mvcc.api.wsState r.ι (S.register id
               ⟨mvcc.watchRangeOf kk e endk c.startRev id, [], mvcc.api.watchLo σ c.startRev, k, true⟩)),
        COMM (if S.closed then iprop(⌜id = W64 (-1)⌝) else
          iprop(∃ i : RegInfo, regIs r.γreg id i ∗ idTok2 r.γtok id ∗ mvcc.api.wsSentLb r.ι i.k ∗
            r.W.histLb σ.log ∗ ⌜σ.pending = none ∧ i.lo = mvcc.api.watchLo σ c.startRev ∧
              i.rg = mvcc.watchRangeOf kk e endk c.startRev id⌝)) }>

/-- **The update `recvLoop` passes to `Cancel id`** (O2), with the client's cancel request
(`cancelQ`): the cancel facts kept for the watcher made not live. -/
def cancel_au.stmt : Prop :=
  ∀ (sws : Loc) (r : WRunA GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM2 → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (id : w64),
  swsIs2 sws r Up Dn st ci cd ∗ cancelQ r.γs id ⊢
    AU <{ ∃∃ (S : mvcc.api.StreamState), mvcc.api.wsState r.ι S }> @ ⊤ \ ↑mvcc.api.mvccN, ∅
      <{ mvcc.api.wsState r.ι (S.cancel id), COMM True }>

/-- **The update `close` passes to `Close`** (O3): the close token shows the stream open, and is
deposited. -/
def close_au.stmt : Prop :=
  ∀ (sws : Loc) (r : WRunA GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM2 → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)),
  swsIs2 sws r Up Dn st ci cd ∗ closeTok r.γcl ⊢
    AU <{ ∃∃ (S : mvcc.api.StreamState), mvcc.api.wsState r.ι S ∗ ⌜S.closed = false⌝ }>
        @ ⊤ \ ↑mvcc.api.mvccN, ∅
      <{ mvcc.api.wsState r.ι S.close, COMM True }>

/-- **The snapshot after a receive** (O4): the send loop, holding `wsRecv ι rs` (and the received
list's authority at `rs`), opens the run's invariant and the server's peek and applies the API's
`wsRecv_ok` law: a snapshot of `rs`. A ghost step (everything opened is timeless). -/
def snap_after_recv.stmt : Prop :=
  mvcc.api.wsRecv_ok.law (GF := GF) →
  ∀ (sws : Loc) (r : WRunA GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM2 → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (rs : List mvcc.api.WResp),
  swsIs2 sws r Up Dn st ci cd ∗ mvcc.api.wsRecv r.ι rs ={⊤}=∗
    mvcc.api.wsRecv r.ι rs ∗ ∃ σ S, rcvSnap r rs σ S

/-- **The drain's empty case** (O5): `wsChan_tryRecv`'s `Ψ` at the stamp `k` of the created
response's watcher (`ctrlWatcher2`'s `wsSentLb ι k`): `k` at most what was received, so the
created response's `createdAfter2` holds once every `-1` received has been sent (the loop sends a
`-1` at once). The drain's loop invariant carries `wsRecv ι rs ∗ monoListAuthOwn γr 1 rs`. -/
def drain_empty.stmt : Prop :=
  ∀ (r : WRunA GF) (rs : List mvcc.api.WResp) (i : RegInfo) (L : List WatchRespM2) (j : Nat)
    (mc : WatchRespM2),
  regIs r.γreg mc.watchId i ∗
    ⌜mc.created = true ∧ mc.canceled = false ∧ L.length = j ∧ i.k ≤ rs.length⌝ ∗
    monoListAuthOwn r.γr 1 rs ∗ monoListLbOwn r.γs.down L ∗
    ⌜∀ (n : Nat) (x : mvcc.api.WResp), rs[n]? = some x → x.id = W64 (-1) →
      ∃ m' ∈ L, m'.src = some (n, x)⌝ ⊢
  |==> monoListAuthOwn r.γr 1 rs ∗ createdAfter2 r j mc

end defs

end W14
end v3rpc

/-! ## §8 client/v3's changed bridge statements -/

namespace client
namespace W14

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3
open v3rpc.W14

section bridges
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **(S3) A response with events, or of an id other than `-1`, carries an id the run registered**
(today's `srvEventIdsAssigned`, now from the snapshot's conjunct 1 and its registry entries). -/
def srvEventIdsAssigned2.stmt : Prop :=
  ∀ (R : v3rpc.WSrv GF) (W : SrvW GF) (γs : StreamNames) (j : Nat) (m : WatchRespM2)
    (r : WRunA GF) (n : Nat) (x : mvcc.api.WResp),
  ⌜r.srv = R ∧ r.W = W ∧ r.γs = γs⌝ ∗ mvccOk2 r j m ⊢ ⌜m.src = some (n, x)⌝ -∗
    ⌜x.id ≠ W64 (-1)⌝ -∗ ∃ i : v3rpc.W14.RegInfo, regIs r.γreg x.id i

/-- **A watcher's events, from the snapshot** (replacing `watchRecvOk` in `recv_unfiltered` and
`dispatch_content`, `WatchContent.lean`, and in `reg_pre*`, `WatchRun.lean`): the `n`-th received
response `x` of the id `X` registered at `i`, under the client's watch condition (`srvOnce`):
`X`'s events received up to `x` are the range's events of the revisions `[i.lo, hi)` of a
certified log, `hi` at most its length. -/
def recvEvents.stmt : Prop :=
  ∀ (r : WRunA GF) (j : Nat) (m : WatchRespM2) (n : Nat) (x : mvcc.api.WResp) (i : v3rpc.W14.RegInfo),
  srvOnce r.W ∗ mvccOk2 r j m ∗ regIs r.γreg x.id i ⊢ ⌜m.src = some (n, x) ∧ x.id ≠ W64 (-1)⌝ ={⊤}=∗
    ∃ (pre : List mvcc.api.WResp) (L : mvcc.Log) (hi : Nat), rcvLb r.γr (pre ++ [x]) ∗
      r.W.histLb L ∗ ⌜pre.length = n ∧ hi ≤ L.length ∧
        mvcc.api.recvEvs (pre ++ [x]) x.id = mvcc.watchEvents L i.rg i.lo hi⌝

/-- **A progress response's coverage** (replacing `respCov`/`covFact`/`respCompl`/`regsAt`/
`chanRegAt`/`rsnW` in `WatchRun.lean` ~860-1980, `WatchCompl.lean` ~826 and
`watchGRPCStream__run.lean` ~2013): an event-less, non-compaction response at `j` from the `n`-th
received `x`, and a watch id `X` the client saw created at `p < j` and live after the responses
before `j`: `x` is `X`'s own or `-1` (the broadcast), and then `X`'s events received up to `x` are
exactly the range's events up to `x`'s revision, or (for `-1`) the client asked to cancel `X`. -/
def progressCov.stmt : Prop :=
  ∀ (r : WRunA GF) (j p : Nat) (m mc : WatchRespM2) (n : Nat) (x : mvcc.api.WResp) (i : v3rpc.W14.RegInfo)
    (Lj : List WatchRespM2),
  srvOnce r.W ∗ mvccOk2 r j m ∗ createdAfter2 r p mc ∗ regIs r.γreg mc.watchId i ∗
    monoListLbOwn r.γs.down Lj ⊢
  ⌜m.src = some (n, x) ∧ x.evs = [] ∧ x.compactRev = W64 0 ∧ mc.created = true ∧
    mc.canceled = false ∧ p < j ∧ Lj.length = j ∧ Lj[p]? = some mc ∧ idLive2 Lj mc.watchId ∧
    (x.id = mc.watchId ∨ x.id = W64 (-1))⌝ ={⊤}=∗
    (∃ (pre : List mvcc.api.WResp) (L : mvcc.Log), rcvLb r.γr (pre ++ [x]) ∗ r.W.histLb L ∗
      ⌜pre.length = n ∧ mvcc.api.recvEvs (pre ++ [x]) mc.watchId =
        mvcc.watchEvents L i.rg i.lo (sint.nat x.rev + 1)⌝) ∨
    (⌜x.id = W64 (-1)⌝ ∗ v3rpc.cancelQ r.γs mc.watchId)

/-- **A compaction response** (replacing `mvccOk_cmpPerm`/`cmpOkOf_of_mvccOk`, `WatchRun.lean`
1291-1312, and `respOk`'s shape in `reg_pre_cmp`): no events, its watcher's, at revision `0`
(the API's A3), its compaction revision positive and at most a permitted one (`crevOk`, which the
server links to the cluster's `kvCmpPermit`, downward closed). -/
def compactResp.stmt : Prop :=
  ∀ (r : WRunA GF) (j : Nat) (m : WatchRespM2) (n : Nat) (x : mvcc.api.WResp),
  mvccOk2 r j m ⊢ ⌜m.src = some (n, x) ∧ x.compactRev ≠ W64 0⌝ -∗
    ∃ c : Int, r.W.crevOk c ∗ ⌜x.evs = [] ∧ x.id ≠ W64 (-1) ∧ x.rev = W64 0 ∧
      0 < sint.Z x.compactRev ∧ sint.Z x.compactRev ≤ c⌝

/-- **The client's watched logs** (today's `srvWL R L := mvcc.evLog R.γ.st L ∗ ⌜LogSmall L ∧
LogPutsLe etcdKeyMax L ∧ ..⌝`): the server's certified lower bound, whose model facts (`LogWf'`,
the length, `LogSmall`, `LogPutsLe`) are `srvWOk`'s law, so `srvLogsSmall` and the pure conjuncts
go. `watchLaws_srv` (`cli/InvWatch.lean:425`) is re-proved over it from the server's
`histLb_model.law` (xreview §6b: `etcdReached`, `srvEtcdState`/`srvStep`, `LogPutsLe`). The
per-event positivity `wsRecvOk` carries (round 16) does not replace these: the client's model laws
are of the log's states (`stateAt_client_revs`, `evsOfRevM_state`, `stepPure_of_watch`), every
key-value of a state, not only the events delivered. -/
def srvWL2 (W : SrvW GF) (L : mvcc.Log) : IProp GF := W.histLb L

end bridges

end W14
end client

end EtcdGrove
end Perennial
