/-
mvccfull's watch streams (`notes/mvccfull-proof-plan.md`, "Draft (F1): the invariants in full", E,
and "Draft revision: readers per epoch"). Lean-first (no Rocq counterpart). Draft: the statements
in full; the lemmas' proofs `sorry` unless pure and short (each `sorry` marked).

**An epoch's stream** (`Strm`: the epoch's fixed part `Ep`, the stream's struct `s`, its mvcc
handle `ws`, its watchers' map `wm`, its ghost names `StreamNames`) belongs to one incarnation `ι`
of member `i` (`isInc`): `startEpoch` opens it on the incarnation's store, `endEpoch` closes it
before any restart. Two goroutines use it: the **registrar** (`act`: `watch`, `cancel`, progress
requests, `Rev`, an empty watch) and the **receiver** (`recvOne`, `receive`).

**The stream's invariant** (`streamInv`, namespace `streamN`, disjoint from `memberN i` and from
`mvccN`): the stream's state `S` (`wsState`), half of the closed flag `σs.cl` at `S.closed` (the
registrar holds the other half at `false` until it stops; then `endEpoch`, which closes the
stream), half of the registry `σs.reg` (the other half in `s.mu`'s invariant: a registration or a
cancel mark is made under `s.mu`, inside `Watch`'s update or with the invariant opened), half of the
registrar's cancel record `σs.cn` (the ids it called `Cancel` on; the registrar holds the other
half), and `regOk'`: the registry is exactly the stream's watchers, each with its registration
(range, `filterFs` of its filter, first revision `lo = watchLo σ start`, the stream's sent count `k`
at its registration), live unless the registrar cancelled it, and cancelled only once marked.

**`s.mu`'s invariant** (`smuInv`, the body `smuBody`): the watchers' map at the registry's
pointers and the order slice listing the registry's ids, the lock's halves of the registry and of
the received responses `σs.rcv` (the receiver holds the other half, with `wsRecv`), a lower bound of
the history, the largest revision of an eventless response so far (`eventless`, `eventlessOk`),
every response for a registered watcher (`rcvKnown`), and each watcher's struct (`watcherOwn'`):
its registration's fields, `stamped → k ≤ |rs|`, `compacted →` a compaction response received, its
position after its received (filtered) events (`wPosOk'`: `posOk`, or, for a watcher from
revision `0` not yet anchored, the floating window `floatLo ≤ lo ≤ rev`).

**The stamp** (`recvOne`): under `s.mu`, before blocking, the receiver polls the channel with
`wsChan_recv.law`'s non-blocking form at `wsSentLb ι n`, `n` the largest `k` of the registry (each
watcher's `wsSentLb ι k` is in its `watcherOwn'`; `wsSentLb_zero.law` for none). The empty case
gives `n ≤ |rs|`, `rs` the lock's received list (every response received so far was checked under
the lock), so every registered watcher may be marked stamped (`stamp_ok`). Registration happens only
under `s.mu`, so a watcher registered later is not stamped.

**The epoch's resources** (`epochTok`, one per stream, the writer's at `startEpoch`, back at
`endEpoch`): a history reader slot (the receiver's), two of the incarnation's reader tokens (the
registrar's and the receiver's) and a fraction of the incarnation's live token (`incLive`; see
below). Each goroutine returns its part through its wait group (`regDone`, `recvDone`; Perennial's
join idiom, one goroutine each).

**The incarnation's live share** (`epLive`, `Readers.lean`'s `incLive`: the incarnation's handles
and a share of its retirement token): what a goroutine needs to open `memberInv` (the share rules
out the retired branch). The readers' vocabulary (`runnerKeys`, `runnerH`, `ctrInv`, `readQ`) is
shared.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers
public import Perennial.Ghost.GhostMap
public import Perennial.Proof.sync.WaitGroupJoin

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- **A registry entry**: the watcher's struct, its range's key and end (`endNil`: a `nil` end), its
start revision and filter as `watch` registered them, its first revision `lo` (`watchLo σ start`
at the registration), the stream's sent count `k` at its registration, and its cancel mark
(`watcher.cancelled`). -/
structure Reg where
  wp : Loc
  key : GoString
  e : GoString
  endNil : Bool
  start : w64
  filter : w64
  lo : Nat
  k : Nat
  cm : Bool

instance Reg.countable : Pos.Countable Reg :=
  .ofInjective (fun r => Pos.Countable.encode
      (r.wp, r.key, r.e, r.endNil, r.start, r.filter, r.lo, r.k, r.cm))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
      subst h1 h2 h3 h4 h5 h6 h7 h8 h9; rfl)

/-- The changes the entry's watcher expects (`watcher.matches`). -/
def Reg.mt (x : Reg) : change → Bool := matchesM x.filter x.endNil x.key x.e

/-- **The registry is the stream's watchers** (`C` the ids the registrar called `Cancel` on): every
watcher of the stream is in the registry (no other: `Watch` registers no empty range, which the
tester's empty watch relies on, see the report), each entry a watcher of its range, filtered by its
filter's predicates, from its `lo`, after its `k` responses; live unless cancelled by the
registrar, and cancelled only once marked. -/
def regOk' (S : StreamState) (W : GMap w64 Reg) (C : List w64) : Prop :=
  (∀ id wi, S.ws !! id = some wi → (W !! id).isSome) ∧
  ∀ id x, W !! id = some x → ∃ wi, S.ws !! id = some wi ∧
    wi.rg = ⟨x.key, if x.endNil then none else some x.e, x.start, id⟩ ∧
    wi.fs = filterFs x.filter ∧ wi.lo = x.lo ∧ wi.k = x.k ∧
    (id ∉ C → wi.live = true) ∧ (id ∈ C → x.cm = true)

/-- **Every response but the stream's progress was for a registered watcher** (`receive` checks
it): so a watcher registered later has received nothing before. -/
def rcvKnown' (rs : List WResp) (W : GMap w64 Reg) : Prop :=
  ∀ r ∈ rs, r.id ≠ W64 (-1) → (W !! r.id).isSome

/-- **The largest eventless revision** (`s.eventless`): `0`, or the revision of a received
progress response (no events, not a compaction's); never negative. -/
def eventlessOk (rs : List WResp) (P : w64) : Prop :=
  0 ≤ sint.Z P ∧
  (P = W64 0 ∨ ∃ (i : Nat) (y : WResp), rs[i]? = some y ∧ y.evs = [] ∧ y.compactRev = W64 0 ∧ y.rev = P)

/-- **A watcher's position after `n` received events**, against the history `Hl`, for the
expected changes `mt` from its first revision `lo`: not yet anchored (from revision `0`, no event
yet: `floatLo` positive), the floating window `floatLo ≤ lo ≤ rev` at index `0`; else `posOk`,
its revision one of `Hl`'s or still `lo` with nothing received. -/
def wPosOk' (Hl : List HRev) (mt : change → Bool) (lo : Nat) (wv : watcher) (n : Nat) : Prop :=
  0 ≤ sint.Z wv.rev' ∧ 0 ≤ sint.Z wv.index' ∧ 0 ≤ sint.Z wv.floatLo' ∧
  sint.Z wv.rev' < 2 ^ 63 - 1 ∧
  (if 0 < sint.Z wv.floatLo' then
     n = 0 ∧ wv.index' = W64 0 ∧ sint.Z wv.floatLo' ≤ (lo : Int) ∧ (lo : Int) ≤ sint.Z wv.rev'
   else
     posOk Hl mt lo (sint.nat wv.rev') (sint.nat wv.index') n ∧
     (sint.nat wv.rev' < Hl.length ∨ (sint.nat wv.rev' = lo ∧ wv.index' = W64 0 ∧ n = 0)))

/-- The pure part of a registered watcher under `s.mu` (`watcherOwn'`), after the responses `rs`. -/
def watcherOk (Hl : List HRev) (rs : List WResp) (id : w64) (x : Reg) (wv : watcher) : Prop :=
  x.endNil = decide (wv.end' = slice.nil) ∧ x.key ≠ [] ∧ wv.filter' = x.filter ∧
  wv.start' = x.start ∧ 0 ≤ sint.Z x.start ∧ sint.Z x.start < 2 ^ 63 - 1 ∧
  1 ≤ x.lo ∧ x.lo < 2 ^ 63 - 1 ∧ (x.start ≠ W64 0 → x.lo = sint.nat x.start) ∧
  (x.start ≠ W64 0 → wv.floatLo' = W64 0) ∧
  wv.cancelled' = x.cm ∧
  (wv.stamped' = true → x.k ≤ rs.length) ∧
  (wv.compacted' = true → ∃ r ∈ rs, r.id = id ∧ r.compactRev ≠ W64 0) ∧
  wPosOk' Hl x.mt x.lo wv (recvEvs rs id).length

/-- **The stamp** (`recvOne`'s default branch): the poll's bound `n` is at least every
registration's `k`, and at most the responses received, so every registered watcher may be
stamped. (Pure; proved.) -/
theorem stamp_ok (W : GMap w64 Reg) (rs : List WResp) (n : Nat)
    (hn : ∀ id x, W !! id = some x → x.k ≤ n) (hle : n ≤ rs.length) :
    ∀ id x, W !! id = some x → x.k ≤ rs.length :=
  fun id x hx => Nat.le_trans (hn id x hx) hle

/-- **The poll's bound is one registration's** (or `0`): the registry's largest `k`, attained.
(Pure; proof `sorry`, Draft.) -/
theorem maxK_attained (W : GMap w64 Reg) :
    ∃ n, (∀ id x, W !! id = some x → x.k ≤ n) ∧
      (n = 0 ∨ ∃ id x, W !! id = some x ∧ x.k = n) := by
  sorry

end model

/-- **A stream's ghost names.** -/
structure StreamNames where
  /-- mvcc's name of the stream -/
  ws : WsName
  /-- whether the stream is closed (the invariant's half; the registrar's, then `endEpoch`'s) -/
  cl : GName
  /-- the registry, id to `Reg` (the invariant's half, `s.mu`'s half) -/
  reg : GName
  /-- the responses the receiver has checked (`s.mu`'s half, the receiver's half) -/
  rcv : GName
  /-- the ids the registrar called `Cancel` on (the invariant's half, the registrar's half) -/
  cn : GName

section records
variable [GooseExts]

/-- **An epoch's fixed part**: the runner, its history, keys and configuration, and the member
`i` (struct `mp`, names `m`) at its incarnation `ι` (store handle `kv`). -/
structure Ep where
  x : Loc
  h : Loc
  ks : List GoString
  γh : HistNames
  cfg : Config
  i : Nat
  mp : Loc
  m : MemberNames
  ι : IncNames
  kv : GoInterface

/-- **A stream of an epoch**: its struct, its mvcc handle, its watchers' map, its names. -/
structure Strm where
  ep : Ep
  s : Loc
  ws : GoInterface
  wm : GoMap
  σs : StreamNames

end records

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A field of a stream. -/
abbrev sF (f : GoString) (s : Loc) : Loc := structFieldRef stream f s

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The streams' invariants' namespace (disjoint from `memberN i` and `mvccN`). -/
def streamN : Namespace := (nroot .@ "mvccfull") .@ "stream"

/-- The streams' counters' invariants' namespace (`ctrInv`, `Readers.lean`: the report counters
the streams add to, a member's `regs`, a stream's `stop`; disjoint from `streamN`). -/
def sCtrN : Namespace := (nroot .@ "mvccfull") .@ "streamctr"

/-- **The runner's read-only part the streams read** (persistent; `Readers.lean`'s `runnerKeys`,
`runnerH`): the packages, the keys (each non-empty: `keysOf_ne_nil`), the history, the
configuration and the weights the registrar reads, the report counters the streams add to. -/
def rnCtx (x : Loc) (ks : List GoString) (cfg : Config) (h : Loc) (γh : HistNames) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
    runnerKeys x ks ∗ ⌜∀ k ∈ ks, k ≠ []⌝ ∗ runnerH x h ∗ isHistory h γh ∗
    rF go!"cfg" x ↦□ cfg ∗
    (∃ wa : List w64, cfg.Mix'.Act' ↦*□ wa) ∗ (∃ wst : List w64, cfg.Mix'.Start' ↦*□ wst) ∗
    ctrInv (sCtrN .@ "events") (rF go!"events" x) ∗
    ctrInv (sCtrN .@ "progress") (rF go!"progress" x) ∗
    ctrInv (sCtrN .@ "compacted") (rF go!"compacted" x) ∗
    ctrInv (sCtrN .@ "cancels") (rF go!"cancels" x))

/-- **A share `q` of the epoch's incarnation, live** (`incLive`, `Readers.lean`: its handles and a
share of its retirement token, what a goroutine needs to open `memberInv`). -/
abbrev epLive (E : Ep) (q : Qp) : IProp GF := incLive E.ks E.γh E.i E.mp E.m E.ι E.kv q

/-- **An epoch's handles** (persistent): the runner's, the incarnation's, the member's `regs`. -/
def epCtx (E : Ep) : IProp GF :=
  iprop(rnCtx E.x E.ks E.cfg E.h E.γh ∗ isInc E.ks E.γh E.i E.mp E.m E.ι E.kv ∗
    ctrInv (sCtrN .@ "regs") (mF go!"regs" E.mp))

/-- **The stream's invariant** (see the file header). -/
def streamInv (σs : StreamNames) : IProp GF :=
  iprop(∃ (S : StreamState) (W : GMap w64 Reg) (C : List w64),
    wsState σs.ws S ∗ ghostVar σs.cl (1 : Qp).half S.closed ∗
    ghostMapAuth σs.reg (1 : Qp).half W ∗ ghostVar σs.cn (1 : Qp).half C ∗ ⌜regOk' S W C⌝)

/-- **A registered watcher under `s.mu`** (see the file header): its struct, its range's slices
(read-only), the stream's sent count at its registration, and `watcherOk`. -/
def watcherOwn' (Hl : List HRev) (rs : List WResp) (ws : WsName) (id : w64) (x : Reg) : IProp GF :=
  iprop(∃ wv : watcher, x.wp ↦ wv ∗ wv.key' ↦*□ x.key ∗ wv.end' ↦*□ x.e ∗ wsSentLb ws x.k ∗
    ⌜watcherOk Hl rs id x wv⌝)

/-- **`s.mu`'s invariant's body** at the received responses `rs`, the registry `W`, the history's
lower bound `Hl` and the eventless revision `P` (see the file header). -/
def smuBody (T : Strm) (rs : List WResp) (W : GMap w64 Reg) (Hl : List HRev) (P : w64) :
    IProp GF :=
  iprop(T.wm ↦$ W.fmap Reg.wp ∗
    (∃ (osl : GoSlice) (ids : List w64), sF go!"order" T.s ↦ osl ∗ osl ↦* ids ∗
      ownSliceCap w64 osl (DFrac.own 1) ∗ ⌜ids.Nodup ∧ ∀ id, id ∈ ids ↔ (W !! id).isSome⌝) ∗
    sF go!"eventless" T.s ↦ P ∗
    ghostMapAuth T.σs.reg (1 : Qp).half W ∗ ghostVar T.σs.rcv (1 : Qp).half rs ∗
    monoListLbOwn T.ep.γh.l Hl ∗ ⌜rcvKnown' rs W ∧ eventlessOk rs P⌝ ∗
    [∗map] id ↦ x ∈ W, watcherOwn' Hl rs T.σs.ws id x)

/-- **`s.mu`'s invariant.** -/
def smuInv (T : Strm) : IProp GF :=
  iprop(∃ (rs : List WResp) (W : GMap w64 Reg) (Hl : List HRev) (P : w64), smuBody T rs W Hl P)

/-- **A stream's handles** (persistent): the epoch's, the struct's read-only fields, the mvcc
stream, the stream's invariant and lock, its stop flag. -/
def streamCtx (T : Strm) : IProp GF :=
  iprop(epCtx T.ep ∗
    sF go!"x" T.s ↦□ T.ep.x ∗ sF go!"m" T.s ↦□ T.ep.mp ∗ sF go!"kv" T.s ↦□ T.ep.kv ∗
    sF go!"ws" T.s ↦□ T.ws ∗ sF go!"watchers" T.s ↦□ T.wm ∗
    isMvccWatchStream T.ws T.ep.ι.kv T.σs.ws ∗
    inv streamN (streamInv T.σs) ∗ sync.isMutex (sF go!"mu" T.s) (smuInv T) ∗
    ctrInv (sCtrN .@ "stop") (sF go!"stop" T.s))

/-- **The registrar's resources** (exclusive), its cancel record at `C`. -/
def regOwn (T : Strm) (q : Qp) (C : List w64) : IProp GF :=
  iprop(mvccReaders T.ep.ι.kv 1 ∗ epLive T.ep q ∗ ghostVar T.σs.cl (1 : Qp).half false ∗
    ghostVar T.σs.cn (1 : Qp).half C)

/-- **The receiver's resources** (exclusive), after the responses `rs`. -/
def rcvOwn (T : Strm) (q : Qp) (rs : List WResp) : IProp GF :=
  iprop(mvccReaders T.ep.ι.kv 1 ∗ epLive T.ep q ∗ histRd T.ep.h T.ep.γh ∗
    wsRecv T.σs.ws rs ∗ ghostVar T.σs.rcv (1 : Qp).half rs)

/-- **One stream's share of the epoch's resources** (`startEpoch` takes one per stream,
`endEpoch` gives it back). -/
def epochTok (E : Ep) (q : Qp) : IProp GF :=
  iprop(histRd E.h E.γh ∗ mvccReaders E.ι.kv 2 ∗ epLive E q)

/-- **The writer's part of an open stream** (between `startEpoch` and `endEpoch`): its handles,
and its two wait groups, each giving back its goroutine's resources (a goroutine stops only when
asked to: the registrar at the stop flag, the receiver at the channel's close). -/
def epochStream (E : Ep) (q : Qp) (s : Loc) : IProp GF :=
  iprop(∃ T : Strm, ⌜T.ep = E ∧ T.s = s⌝ ∗ streamCtx T ∗
    sync.join.ownAdder (sF go!"regDone" s) (W32 1) iprop(True ∗ ∃ C, regOwn T q.half C) ∗
    sync.join.ownAdder (sF go!"recvDone" s) (W32 1) iprop(True ∗ ∃ rs, rcvOwn T q.half rs))

/-- **The receiver's facts** at its state (mvccrand's `recv_facts`, with compaction): opening the
incarnation's invariant (its live share excludes the retired branch, `memberInv_live`) and the
stream's, at the store's state `σ` (what a read learns of it, `readQ`: lower bounds of its
revision and compaction revision for the checks against `revHi`/`cmpHi` loaded after, a lower bound
of the history covering its notified log, its reachability), mvcc's watch guarantee of the
responses received (`wsRecv_ok.law`), every revision changing each key at most once (`onceUpTo` at
any first revision and the compaction revision, from `memberState`'s `onceUpToAll`), the registry
(`regOk'`, for some cancel record), the notified log well-formed and small. (Proof `sorry`, Draft:
`iinv` of both, `memberInv_live`, the laws.) -/
theorem recv_facts (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hrok : mvcc.api.wsRecv_ok.law (GF := GF) (hG := hG))
    (T : Strm) (q : Qp) (rs : List WResp) (W : GMap w64 Reg) :
    epLive T.ep q ∗ inv streamN (streamInv T.σs) ∗ isMvccWatchStream T.ws T.ep.ι.kv T.σs.ws ∗
        wsRecv T.σs.ws rs ∗ ghostMapAuth T.σs.reg (1 : Qp).half W ⊢
      |={⊤}=> epLive T.ep q ∗ wsRecv T.σs.ws rs ∗ ghostMapAuth T.σs.reg (1 : Qp).half W ∗
        ∃ (σ : MvccState) (S : StreamState) (C : List w64), readQ T.ep.ks T.ep.γh T.ep.m σ ∗
          ⌜wsRecvOk σ S rs ∧ (∀ lo, onceUpTo σ.notifiedLog lo σ.crev) ∧ regOk' S W C ∧
            LogWf' σ.notifiedLog ∧ σ.notifiedLog.length < 2 ^ 63⌝ := by
  sorry

end defs


end mvccfull
end EtcdGrove
end Perennial
