/-
mvccfull's writer (`notes/mvccfull-proof-plan.md`, "Draft (F1): the invariants in full", W, and the
revisions after it). Lean-first (no Rocq counterpart). Draft: the statements in full; the lemmas'
proofs `sorry` unless pure and short (each `sorry` marked).

**The operation log** (`x.log`, a slice of `*op` the writer alone reads and appends to): each
`op` struct is written once, by `gen`, and read only after, so the writer holds it persistently
(`opIs`) at a pure value `OpM` (the op's choices, its slices' contents as strings). The tester's
model is a pure function of the log's prefixes (`runM ks ops n`, `MSt`): the history of revisions
(`hs`: each revision's state and changes, as the history struct holds them), the compaction
revision, the live leases (increasing: ids are granted in increasing order), the ids ever granted.
A member that has applied `n` operations is at the store state `σOf ks ops n` (its log the
history's changes, `logOfHist`; nothing pending) and its Go model fields are `revAfter`,
`cmpAfter`, `leasesAfter` of `n`. The leader's history (`histW`, the writer's part) is the model's
at the leader's count; the follower and the builder find their revisions in it (a lower bound).
**`logOk`**: every operation is valid for the state it applies to (`opValid`): a put's lease is `0`
or live; a revoke's lease is live; a grant's id is positive and above every id granted before; a
compaction's revision is positive (the tester's restriction); a write transaction's sub-operations
are as `genSubs` makes them (puts' keys distinct, none in a delete's range: etcd's
`checkIntervals`). From it the log changes each key at most once per revision (`onceUpToAll`,
`logOk_once`), which `memberState` keeps.

**A member, as the writer holds it** (`memW`, for the leader, the follower and the builder alike;
`MemS` its record): its Go fields (`path`, `be`, `le`, the writer's share of `kv`, `ops`, `rev`,
`cmp`, `leases`; `hook` and `id` read-only), its current incarnation `ι` (`isInc`, the writer's
share `qw` of the retirement token and of `kv`, its halves of `m.σ` at `σOf ks ops n` and of `m.bnd`), the
store (`mvccOpen`, the whole backend share at the tester's real backend `bk`, the hook frozen at
the member's closure `f` (`hookIs`), its own `nw` reader tokens), the backend's kept part
(`bkKeep`: its contract and stop channels, its file, the census for `backend.Close`, the lessor's
write right and write-back tokens), the lessor (`lessorW`: its invariant, configuration, guard
`True`, the revocable mode, its write contract on any backend (`lessorApplyOk`, `NewLessor`'s: at the
member's backend through `lessorW_backend`, at the snapshot's after `Recover` moves the lessor there
through `lessorApplyOk_at`), a reader slot, the owner's part at the live leases
and the store's items, the revokers, the ids ever granted with their requests (`3600`), the range
deleter at the store's, the lease bucket's part holding exactly the live leases' records,
`leaseRecsOk`, the stop right), and the hook's counters (`applying`, `saved`, owned outright, as
mvccrand's). The shares `qw`, `nw` are the writer's after what it lent to the epoch's readers
(`rdStock`) and streams (`epochTok`), each of which holds the same share of the retirement token and
of the `kv` field (`incRd`), so one share `qw` is the writer's of both; a restart needs them whole
(`qw = 1`, `nw = mvccReaderN`). While an epoch runs the writer keeps at least one reader token
(`1 ≤ nw`: `apply`'s transactions, `restart`'s `endEpoch`), which `Run` gets from `runCfgOk`'s thread
bound (`2·Readers + 4·Streams + 3 ≤ 2 ^ 28`, below `mvccReaderN = rdStockN - 7`, about `2 ^ 29`).

**The builder** (`restore`'s third store) is a member like the others, with an incarnation of its
own (namespace `memberN 2`): no reader or stream ever holds a share, so the writer retires it at
its `shut` as at a restart. (A deviation from the plan's W, "the builder has no invariant": one
spec of `apply` for every member needs one shape of the store's access; the invariant costs only
ghost state.)

**The restart chain** (`restart`; `Run`'s final reopen; the builder's `shut`):
1. *retire* (`inc_retire`): with the whole retirement token (every share back: `stopReaders`,
   `endEpoch`), the incarnation's contents out (`memberState`), split into the store's state and
   what is carried (`memberState_split`: `m.σ`'s half, the atomics, the monotone counters, the
   history's lower bound);
2. *close* (`runner.shut`): `KV.Close` (`mvccClosed`); the census (`mvccClosed_rest.law` with every
   reader token, then `bkCensus`) gives `bOpen 1`; `lessor.Stop`; `backend.Close` (at
   `dbCloseOk`): the stopped lock's view at the file's data `D` (`bStopView`) and `fileHolds path
   D`; `mvccImage_stop.law` at the retired store's state: `mvccImage D σ.log σ.crev u`; the lease
   bucket's part agrees with the stopped lock's (`rbOwn`), so `D`'s lease bucket holds the live
   leases' records (`leaseRecsOk (rbData P D)`);
3. *reopen* (`runner.open`): `backend.New` on `fileHolds path D` (`newPostK`, at `mvccW gx` of a
   fresh registration, `mvccW_alloc.law`), the backend opened for the store (`etcdStorage_open.law`,
   `backendRest_open.law`: `inc_open_backend`, `mvccrand.rc_open` at any image), `NewLessor.spec`
   over the records (`GA := True`, `reqOf := 3600`), `mvcc.api.New.spec` at the image's state (the
   lessor's owner part at the live leases, every key's lease live: `logOk_items`), the hook set and
   frozen (`SetTxPostLockInsideApplyHook`), a new incarnation's invariant allocated with the carried
   parts (`inc_alloc`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Streams
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LogLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.RunChecksBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.StopLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.BkRTLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WbTokLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.NewKLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClientLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorApplyLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RwLensLaws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

/-! ## The writer's resources -/

section record
variable [GooseExts]

/-- **A member's record, as the writer holds it** (see the file header): its file, its lessor,
its store's handle, its operations applied, its backend's instance, its incarnation, the ids its
lessor ever had, the bound atomics' values. -/
structure MemS where
  path : GoString
  lp : Loc
  kv : GoInterface
  ops : Nat
  bk : mvcc.KBReal
  ι : IncNames
  U : List w64
  b : Bnd

end record

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A range request's value is `q`** (its slices read-only). -/
def rangeIs (v : rangeReq) (q : RangeM) : IProp GF :=
  iprop(v.key' ↦*□ q.key ∗ v.end' ↦*□ q.e ∗ ⌜q.endNil = decide (v.end' = slice.nil) ∧ v.ro' = q.ro⌝)

instance rangeIs_persistent (v : rangeReq) (q : RangeM) : Persistent (rangeIs (GF := GF) v q) := by
  unfold rangeIs; infer_instance

/-- **A sub-operation's value is `s`** (read-only). -/
def subIs (v : subOp) (s : SubM) : IProp GF :=
  iprop(v.key' ↦*□ s.key ∗ v.end' ↦*□ s.e ∗ rangeIs v.q' s.q ∗
    ⌜v.kind' = s.kind ∧ s.endNil = decide (v.end' = slice.nil) ∧ v.val' = s.val ∧
      v.lease' = s.lease⌝)

instance subIs_persistent (v : subOp) (x : SubM) : Persistent (subIs (GF := GF) v x) := by
  unfold subIs; infer_instance

/-- **The op at `p` is `o`** (persistent: `gen` writes it, nothing after). -/
def opIs (p : Loc) (o : OpM) : IProp GF :=
  iprop(∃ (v : op) (subs : List subOp), p ↦□ v ∗ v.key' ↦*□ o.key ∗ v.end' ↦*□ o.e ∗
    rangeIs v.q' o.q ∗ v.subs' ↦*□ subs ∗ ⌜subs.length = o.subs.length⌝ ∗
    ([∗list] x ∈ subs.zip o.subs, subIs x.1 x.2) ∗
    ⌜v.kind' = o.kind ∧ o.endNil = decide (v.end' = slice.nil) ∧ v.val' = o.val ∧
      v.lease' = o.lease ∧ v.write' = o.write ∧ v.shared' = o.shared ∧ v.id' = o.id ∧
      v.rev' = o.rev ∧ v.wait' = o.wait⌝)

instance opIs_persistent (p : Loc) (o : OpM) : Persistent (opIs (GF := GF) p o) := by
  unfold opIs; infer_instance

/-- **The writer's log** (`x.log` at the operations `ops`, valid). -/
def logOwn (x : Loc) (ks : List GoString) (ops : List OpM) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ps : List Loc), rF go!"log" x ↦ sl ∗ sl ↦* ps ∗
    ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ps.length = ops.length ∧ logOk ks ops⌝ ∗
    [∗list] x ∈ ps.zip ops, opIs x.1 x.2)

/-- **The hook's counters** (`m.applying` at `i`, `m.saved` at `s ≤ i`; the writer's outright). -/
def hookPre (mp : Loc) (i s : w64) : IProp GF :=
  iprop(sync.atomic.ownInt64 (mF go!"applying" mp) (DFrac.own 1) i ∗
    sync.atomic.ownInt64 (mF go!"saved" mp) (DFrac.own 1) s ∗ ⌜sint.Z s ≤ sint.Z i⌝)

/-- What the hook gives: `saved` at `i`. -/
def hookPost (mp : Loc) (i : w64) : IProp GF :=
  iprop(sync.atomic.ownInt64 (mF go!"applying" mp) (DFrac.own 1) i ∗
    sync.atomic.ownInt64 (mF go!"saved" mp) (DFrac.own 1) i)

/-- **The member's hook `f`** (persistent; `newMember`'s closure): its triple at every index, under
the batch lock (invariant `True`: the tester's backend has none). -/
def hookOk (mp : Loc) (f : GoFunc) : IProp GF :=
  iprop(⌜f ≠ func.nil⌝ ∗ □ ∀ i s, mvcc.api.hookRun iprop(True) f (hookPre mp i s) iprop(True ∗ hookPost mp i))

/-- **The census before the backend's `Close`** (a backend `bk` the store used): with the lessor's
write right's open share, the half the writer keeps and the store's rest (`storageRest`: from the
closed store and every reader token, `mvccClosed_rest.law`, or from `Restore` replacing the
backend), the whole open token. It holds the other shares (a second reader's, the pool's, the auth
store's; `etcdserver.stop_census_open`'s). -/
def bkCensus (bk : mvcc.KBReal) : IProp GF :=
  iprop(backend.bOpen bk.γB backend.rdOpen -∗ backend.bOpen bk.γB (1 : Qp).half -∗
    storageRest (etcdStorage bk) ={⊤}=∗ backend.bOpen bk.γB 1)

/-- **What the writer keeps of a member's opened backend `bk`** (the tester's parameters at the
batch limit `lim`, `mvccrand.rcP`, at the store's write invariant `mvccW bk.gx`, the batch lock's
invariant `True`): its contract and stop channels, its file `path`, half of the open token, the
lessor's write right (a reader slot with its open share, `apply.bkRT`), `k` write-back tokens (one
per lease grant), the census. -/
def bkKeep (bk : mvcc.KBReal) (path : GoString) (k : Nat) : IProp GF :=
  iprop(⌜bk.P = mvccrand.rcP bk.limit ∧ bk.cm = true⌝ ∗
    □ backend.isBackend bk.γB bk.P (mvccW bk.gx) iprop(True) bk.be ∗
    □ backend.isStopChans bk.γB bk.P (mvccW bk.gx) iprop(True) bk.be ∗
    backend.bFile bk.γB path ∗ backend.bOpen bk.γB (1 : Qp).half ∗ apply.bkRT bk ∗
    ownToks bk.γB.wb k ∗ bkCensus bk)

/-- **The writer's lessor of a member** (`lp`, the store `γk`'s, on the backend `bk`, the hook `f`),
at the live leases `L` and the store state `σ`, the ids it ever had `U` (see the file header);
(F1 Prove, 2026-11-10) the lessor's reader pool (`lessorRdPool`, made at `open` of `NewLessor`'s
reader slots the member does not keep), which `checkLeases`' `Leases()` borrows from. -/
def lessorW (γk : MvccName) (bk : mvcc.KBReal) (f : GoFunc) (lp : Loc) (L U : List w64)
    (σ : MvccState) : IProp GF :=
  iprop(∃ (rd : GoFunc) (r : GMap GoString backend.BktData),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
    lease.lessorInv lp (mvccLeases γk) ∗ lease.lessorCfg lp ∗
    lease.lessorGuard (mvccLeases γk) (fun _ => iprop(True)) ∗ lease.lessorRevocable (mvccLeases γk) ∗
    lessorApplyOk lp ∗
    lease.lessorRd lp (mvccLeases γk) ∗
    lease.leaseOwn (mvccLeases γk) L (pendItems σ.log []) ∗ lease.leaseRevokers (mvccLeases γk) L ∗
    lease.leaseEver (mvccLeases γk) U ∗
    □ ([∗list] id ∈ U, lease.leaseReqIs (mvccLeases γk) id (W64 3600)) ∗
    lease.rdOwn (mvccLeases γk) rd ∗ mvccDeleter rd γk ∗ lease.lessorBeOn lp bk.be ∗
    backend.rbPart bk.γB (· = leaseName) r ∗ ⌜leaseRecsOk r L⌝ ∗ lease.lessorStopTok lp ∗
    lease.lessorRdPool (mvccLeases γk))

/-- **The writer's part of an incarnation** `ι` (handle `kv`) of member `i`: its handles, the
writer's share `qw` of the retirement token (so it may open the invariant), its halves of `m.σ` (at
`σ`) and of `m.bnd` (at `b`), which make it the one thread that changes the state and the bounds. -/
def incW (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (qw : Qp) (σ : MvccState) (b : Bnd) : IProp GF :=
  iprop(isInc ks γh i mp m ι kv ∗ ghostVar ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half σ ∗
    ghostVar m.bnd (1 : Qp).half b)

/-- **`end`'s callback** (`tw.End`, or `apply`'s revoke closure): from the writer's part of the
incarnation at `σ` (nothing pending) and a lower bound `Hs'` of the history with the transaction's
revision, the store's state committed (`commitSt σ pend`, under the bounds the writer set: `b`'s
`revHi` above it) and the transaction's reader token back; `E`, `E'` the caller's. -/
def endCb (e : GoFunc) (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (qw : Qp) (σ : MvccState) (b : Bnd) (pend : List Change)
    (Hs' : List HRev) (E E' : IProp GF) : IProp GF :=
  iprop(∀ Φ, incW ks γh i mp m ι kv qw σ b ∗ monoListLbOwn γh.l Hs' ∗ E -∗
    ▷ (incW ks γh i mp m ι kv qw (commitSt σ pend) b ∗ mvccReaders ι.kv 1 ∗ E' -∗ Φ #()) -∗
    WP (App (Val #e) (Val #())) {{ Φ }})

/-- **A member's store, backend and lessor, as the writer holds them** (all of `memW` but the
`ops` field and the hook's counters, which `apply` moves first): the `i`-th member (`0` the leader,
`1` the follower, `2` a builder), struct `mp`, names `m`, hook `f`, record `v`, at the model after
`v.ops` operations of the log `ops` (`σOf`, `revAfter`, ...), the writer's shares `qw` (of the
retirement token and of the `kv` field: the readers and streams hold the rest) and `nw` (reader
tokens), `k` write-back tokens left. -/
def memCore (ks : List GoString) (γh : HistNames) (ops : List OpM) (i : Nat) (mp : Loc)
    (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat) : IProp GF :=
  let σ := σOf ks ops v.ops
  iprop(mF go!"id" mp ↦□ (W64 (i : Int)) ∗ mF go!"hook" mp ↦□ f ∗ hookOk mp f ∗
    mF go!"path" mp ↦ v.path ∗
    mF go!"be" mp ↦ (interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #v.bk.be :
        GoInterface) ∗
    mF go!"le" mp ↦ lease.lessorIface v.lp ∗ mF go!"kv" mp ↦{DFrac.own qw} v.kv ∗
    mF go!"rev" mp ↦ (W64 (revAfter ks ops v.ops : Int)) ∗
    mF go!"cmp" mp ↦ (W64 (cmpAfter ks ops v.ops)) ∗
    (∃ sl : GoSlice, mF go!"leases" mp ↦ sl ∗ sl ↦* leasesAfter ks ops v.ops ∗
      ownSliceCap w64 sl (DFrac.own 1)) ∗
    ⌜v.ops ≤ ops.length⌝ ∗
    incW ks γh i mp m v.ι v.kv qw σ v.b ∗
    mvccOpen v.ι.kv ∗ mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True) ∗
    hookIs (etcdStorage v.bk) f ∗ mvccReaders v.ι.kv nw ∗
    bkKeep v.bk v.path k ∗ lessorW v.ι.kv v.bk f v.lp (leasesAfter ks ops v.ops) v.U σ ∗
    ⌜∀ id ∈ v.U, id ∈ grantedAfter ks ops v.ops⌝)

/-- **A member, as the writer holds it between operations** (see the file header): `memCore`, the
`ops` field, and the hook's counters (`applying` at most the operations applied: a restore moves
`ops` forward and leaves it). -/
def memW (ks : List GoString) (γh : HistNames) (ops : List OpM) (i : Nat) (mp : Loc)
    (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat) : IProp GF :=
  iprop(mF go!"ops" mp ↦ (W64 (v.ops : Int)) ∗
    (∃ a s : w64, hookPre mp a s ∗ ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ v.ops⌝) ∗
    memCore ks γh ops i mp m f v qw nw k)

/-- **The history part of a member's operation** (`apply`'s `lead`): the leader appends the
revision, so it holds the history's writer part at the model's history and compactions after `n`
operations; the follower and the builder find the revision there (a lower bound after `n + 1`). -/
def leadPre (γh : HistNames) (ks : List GoString) (ops : List OpM) (n : Nat) (lead : Bool) :
    IProp GF :=
  if lead then histW γh (histAt ks ops n) (compsAt ks ops n)
  else monoListLbOwn γh.l (histAt ks ops (n + 1))

/-- What the leader's operation gives back: the history's writer part after `n + 1`. -/
def leadPost (γh : HistNames) (ks : List GoString) (ops : List OpM) (n : Nat) (lead : Bool) :
    IProp GF :=
  if lead then histW γh (histAt ks ops (n + 1)) (compsAt ks ops (n + 1)) else iprop(True)

/-- **The writer's context** (persistent): the run's read-only part the streams read (`rnCtx`) and
the readers' (`runnerCfg` at the read weights `wr`, F1's scope `readMixOk`, `rdShared`), the other
packages, the keys' lengths, the logger, the writer's weights, the report counters it adds to, and
the bound on the operations (`Run`'s `runCfgOk`: `cfg.Ops < 2 ^ 38`, so that a member's `Ops + 1`
write-back tokens fit in a fresh backend's, `inc_open_backend`); and (post-Freeze) the number of
keys, `< 2 ^ 60`, `Run`'s `runCfgOk` (a transaction's changes and the keys within `writeSub`'s
`2 ^ 62`). -/
def writerCtx (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc)
    (γh : HistNames) : IProp GF :=
  iprop(rnCtx x ks cfg h γh ∗ runnerCfg x cfg wr ∗ ⌜readMixOk (wr.map sint.Z)⌝ ∗ rdShared x ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
    ⌜∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1⌝ ∗
    (∃ lg : Loc, rF go!"lg" x ↦□ lg ∗ zapLoggerOk lg) ∗
    (∃ wo : List w64, cfg.Mix'.Op' ↦*□ wo) ∗ (∃ wc : List w64, cfg.Mix'.CompactAt' ↦*□ wc) ∗
    (∃ ws : List w64, cfg.Mix'.Step' ↦*□ ws) ∗
    ctrInv (readersN .@ "revisions") (rF go!"revisions" x) ∗
    ctrInv (readersN .@ "compactions") (rF go!"compactions" x) ∗
    ctrInv (readersN .@ "restores") (rF go!"restores" x) ∗
    ctrInv (readersN .@ "restarts") (rF go!"restarts" x) ∗
    ⌜0 ≤ sint.Z cfg.Ops' ∧ sint.Z cfg.Ops' < 2 ^ 38 ∧ ks.length < 2 ^ 60⌝)

instance writerCtx_persistent (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64)
    (h : Loc) (γh : HistNames) : Persistent (writerCtx (GF := GF) x ks cfg wr h γh) := by
  unfold writerCtx rnCtx runnerKeys runnerH runnerCfg runnerRangeMix rdShared ctrInv
  infer_instance

/-- **The writer's own counters**: `nextLease` at the largest id granted (`0` before any; at most one
per operation, so at most the log's length: post-Freeze, for `gen`'s `nextLease + 1 < 2 ^ 63`),
`vals` at `nv`, `builds` at `nb`, each in range. -/
def writerCtrs (x : Loc) (ks : List GoString) (ops : List OpM) (nv nb : Nat) : IProp GF :=
  iprop(∃ nl : w64, rF go!"nextLease" x ↦ nl ∗ rF go!"vals" x ↦ (W64 (nv : Int)) ∗
    rF go!"builds" x ↦ (W64 (nb : Int)) ∗
    ⌜0 ≤ sint.Z nl ∧ (∀ id ∈ grantedAfter ks ops ops.length, sint.Z id ≤ sint.Z nl) ∧
      sint.Z nl ≤ ops.length⌝)

/-- **What the writer lent of a running member's incarnation** (to `n = 2·Readers` readers at the
share `q`, `rdStock`, and to `Streams` streams at `qs` each, `epochTok`), against what it keeps
(`qw` of the retirement token and of the `kv` field, `nw` reader tokens): together, the whole of
each (the readers' and the streams' tokens: one per reader, two per stream). -/
def lentOk [GooseExts] (cfg : Config) (q qs qw : Qp) (nw : Nat) : Prop :=
  qw.val + q.val + ((sint.Z cfg.Streams').toNat : Rat) * qs.val = 1 ∧
  nw + 2 * (sint.Z cfg.Readers').toNat + 2 * (sint.Z cfg.Streams').toNat = mvccReaderN

/-- **The writer between steps, both members running an epoch** (`write`'s loop; `ms` the members'
records, `q` the shares lent to the readers, `qs` to each member's streams): the log, the counters,
the leader's part of the history at the model's history and compactions (`histW`), a reader slot
of the history, the builders' files not yet used (`nb` builds so far: at most one per leader
operation, since a restore needs the follower behind and leaves it caught up), both members
(`memW`, each keeping a reader token of its own, `1 ≤ nw`) with their epoch's streams
(`epochStream`, `m.streams`) and the readers' join (`startReaders`' post: the lent stock). The leader
is at the log's end, the follower behind; the log is at most `cfg.Ops` long (`write` appends only
under its loop guard `l.ops < x.cfg.Ops`). -/
def writerOwn (x : Loc) (ks : List GoString) (cfg : Config) (h : Loc) (γ : FullNames)
    (mp0 mp1 : Loc) (f0 f1 : GoFunc) (ops : List OpM) (v0 v1 : MemS)
    (nv nb : Nat) (q qs : Qp) : IProp GF :=
  let n := 2 * (sint.Z cfg.Readers').toNat
  let ns := (sint.Z cfg.Streams').toNat
  let E0 : Ep := ⟨x, h, ks, γ.h, cfg, 0, mp0, γ.m0, v0.ι, v0.kv⟩
  let E1 : Ep := ⟨x, h, ks, γ.h, cfg, 1, mp1, γ.m1, v1.ι, v1.kv⟩
  iprop(runnerMs x mp0 mp1 ∗ ctrInv (sCtrN .@ "regs") (mF go!"regs" mp0) ∗
    ctrInv (sCtrN .@ "regs") (mF go!"regs" mp1) ∗ logOwn x ks ops ∗ writerCtrs x ks ops nv nb ∗
    histW γ.h (histAt ks ops ops.length) (compsAt ks ops ops.length) ∗ histRd h γ.h ∗
    ⌜v0.ops = ops.length ∧ v1.ops ≤ v0.ops ∧ ops.length ≤ (sint.Z cfg.Ops').toNat⌝ ∗
    ⌜nb ≤ v0.ops ∧ (nb = v0.ops → v1.ops = v0.ops)⌝ ∗
    ([∗list] j ∈ List.range' (nb + 1) ((sint.Z cfg.Ops').toNat - nb),
      backend.fileHolds (buildPathM cfg.Prefix' j) ∅) ∗
    (∃ (qw : Qp) (nw k : Nat), memW ks γ.h ops 0 mp0 γ.m0 f0 v0 qw nw k ∗
      ⌜lentOk cfg q qs qw nw ∧ 1 ≤ nw ∧ (sint.Z cfg.Ops').toNat ≤ k + v0.ops⌝) ∗
    (∃ (qw : Qp) (nw k : Nat), memW ks γ.h ops 1 mp1 γ.m1 f1 v1 qw nw k ∗
      ⌜lentOk cfg q qs qw nw ∧ 1 ≤ nw ∧ (sint.Z cfg.Ops').toNat ≤ k + v1.ops⌝) ∗
    (∃ (sl : GoSlice) (ss : List Loc), mF go!"streams" mp0 ↦ sl ∗ sl ↦* ss ∗
      ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ss.length = ns⌝ ∗ [∗list] s ∈ ss, epochStream E0 qs s) ∗
    (∃ (sl : GoSlice) (ss : List Loc), mF go!"streams" mp1 ↦ sl ∗ sl ↦* ss ∗
      ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ss.length = ns⌝ ∗ [∗list] s ∈ ss, epochStream E1 qs s) ∗
    sync.tokJoin.ownAdder rdWgN iprop(False) (rF go!"readWg" x) n
      (rdStock h γ mp0 mp1 (v0.ι, v0.kv) (v1.ι, v1.kv) n q))

/-- **Two records of the same incarnation and files** (an operation changes the count, the bounds and
the ids ever granted, nothing else). -/
def MemS.sameInc [GooseExts] (v v' : MemS) : Prop :=
  v'.path = v.path ∧ v'.lp = v.lp ∧ v'.kv = v.kv ∧ v'.bk = v.bk ∧ v'.ι = v.ι

/-- **A transaction's sub-operation keeps each key changed once** (`genSubs`' rule, step by step,
against the changes `chs` so far): a put's key is no earlier change's; a delete's range holds no
earlier put's key. -/
def subFresh [GooseExts] (chs : List change) (x : SubM) : Prop :=
  (x.kind = W64 0 → ∀ c ∈ chs, c.key' ≠ x.key) ∧
  (x.kind = W64 1 → ∀ c ∈ chs, c.del' = false → inRangeM x.endNil x.key x.e c.key' = false)

/-- **What is carried across a member's incarnations** (the incarnation's contents but the store's
state, `memberState_split`): `m.σ`'s half at `σ`, the four atomics at `b`, `m.bnd`'s half, the
monotone counters at `σ`'s revisions and notified log's length, the history's lower bound `Hl`, the
bounds' facts. -/
def memberCarry (ks : List GoString) (γh : HistNames) (mp : Loc) (m : MemberNames) (σ : MvccState)
    (b : Bnd) (Hl : List HRev) : IProp GF :=
  iprop(ghostVar m.σ (1 : Qp).half σ ∗
    sync.atomic.ownInt64 (mF go!"revLo" mp) (DFrac.own 1) b.1 ∗
    sync.atomic.ownInt64 (mF go!"revHi" mp) (DFrac.own 1) b.2.1 ∗
    sync.atomic.ownInt64 (mF go!"cmpLo" mp) (DFrac.own 1) b.2.2.1 ∗
    sync.atomic.ownInt64 (mF go!"cmpHi" mp) (DFrac.own 1) b.2.2.2 ∗
    ghostVar m.bnd (1 : Qp).half b ∗
    monoNatAuthOwn m.rev 1 σ.rev ∗ monoNatAuthOwn m.crev 1 (Int.toNat (σ.crev + 1)) ∗
    monoNatAuthOwn m.nrev 1 σ.notifiedLog.length ∗
    monoListLbOwn γh.l Hl ∗
    ⌜1 ≤ sint.Z b.1 ∧ sint.Z b.1 ≤ σ.rev ∧ (σ.rev : Int) ≤ sint.Z b.2.1 ∧ sint.Z b.2.1 < 2 ^ 62 ∧
      (σ.notifiedLog.length : Int) ≤ sint.Z b.2.1 + 1 ∧
      sint.Z b.2.2.1 ≤ σ.crev ∧ σ.crev ≤ sint.Z b.2.2.2 ∧ -1 ≤ σ.crev ∧
      histOkM ks σ Hl ∧ onceUpToAll σ.notifiedLog⌝)

end defs

/-! ## The restart chain (statements; proofs to come, `sorry`) -/

section chain
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **An incarnation's contents are the store's state and what is carried.** (Proof to come:
`sorry`; unfolding.) -/
theorem memberState_split (ks : List GoString) (γh : HistNames) (mp : Loc) (m : MemberNames)
    (γk : MvccName) :
    memberState (GF := GF) ks γh mp m γk ⊣⊢
      ∃ (σ : MvccState) (b : Bnd) (Hl : List HRev), mvccState γk σ ∗ memberCarry ks γh mp m σ b Hl := by
  unfold memberState memberCarry
  constructor
  · iintro ⟨%σ, %b, %Hl, Hs, Hσ, H1, H2, H3, H4, Hb, Hr, Hc, Hn, Hl', %Hp⟩
    iexists σ, b, Hl
    iframe
    ipureintro; exact Hp
  · iintro ⟨%σ, %b, %Hl, Hs, Hσ, H1, H2, H3, H4, Hb, Hr, Hc, Hn, Hl', %Hp⟩
    iexists σ, b, Hl
    iframe
    ipureintro; exact Hp

/-- **Retire** (step 1): with the whole retirement token (no reader or stream of the incarnation
left), the incarnation's contents out; the invariant holds the token from then on. (Proof to come:
`sorry`; `iinv`, `memberInv_live` with the token, the token swapped in; the contents timeless by
`persistent.law`.) -/
theorem inc_retire (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ ghostVar ι.ret 1 () ={⊤}=∗ memberState ks γh mp m ι.kv := by
  haveI := hpers.2.2.2.2.2.1
  haveI : Timeless (memberState (GF := GF) ks γh mp m ι.kv) := by
    unfold memberState
    refine @exists_timeless _ _ _ _ (fun σ => ?_)
    refine @exists_timeless _ _ _ _ (fun b => ?_)
    refine @exists_timeless _ _ _ _ (fun Hl => ?_)
    infer_instance
  unfold isInc
  iintro ⟨⟨#Hinv, -, -⟩, Hret⟩
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold memberInv at Hi
  icases Hi with (>Hs | >Hr)
  · imod Hclose $$ [Hret] with -
    · inext; iunfold memberInv; iright; iexact Hret
    imodintro; iexact Hs
  · icombine Hret Hr gives %Hq0
    obtain ⟨Hq, -⟩ := Hq0
    exfalso
    have h := Qp.le_iff.mp Hq
    simp only [Qp.val_add, Qp.val_one] at h
    grind

/-- **Close, the census** (step 2, before `backend.Close`): the closed store, every reader token and
the whole backend share give the store's rest (`mvccClosed_rest.law`), with which the kept part's
census gives the whole open token; the kept contract, stop channels and file stay. (Proof to come:
`sorry`.) -/
theorem inc_census (hCR : mvcc.api.mvccClosed_rest.law (GF := GF)) (γk : MvccName)
    (bk : mvcc.KBReal) (path : GoString) (k : Nat) :
    mvccClosed (GF := GF) γk ∗ mvccReaders γk mvccReaderN ∗
      mvccBackend γk 1 (etcdStorage bk) iprop(True) ∗ bkKeep bk path k ={⊤}=∗
    mvccBackend γk 1 (etcdStorage bk) iprop(True) ∗ backend.bOpen bk.γB 1 ∗
      □ backend.isBackend bk.γB bk.P (mvccW bk.gx) iprop(True) bk.be ∗
      □ backend.isStopChans bk.γB bk.P (mvccW bk.gx) iprop(True) bk.be ∗ backend.bFile bk.γB path := by
  iintro ⟨Hcl, Hrd, Hmb, Hbk⟩
  iunfold bkKeep at Hbk
  icases Hbk with ⟨%HP, #Hisb, #Hsc, Hbf, Hoh, HRT, -, Hcen⟩
  imod hCR γk 1 _ _ $$ [Hcl Hrd Hmb] with ⟨Hrest, Hmb⟩
  · iframe
  icases (apply.bkRT_eq bk).1 $$ HRT with ⟨-, Hor⟩
  iunfold bkCensus at Hcen
  imod Hcen $$ Hor Hoh Hrest with Hone
  imodintro
  iframe
  iframe #

/-- **Close, the image** (step 2, after `backend.Close` at the data `D`): the retired store's state
`σ` (nothing pending) is what `D` holds (`mvccImage_stop.law`), and `D`'s lease bucket is the
writer's part's (`rbPart` against the stopped lock's `rbOwn`), so it holds the live leases'
records. (Proof to come: `sorry`; `hstop` at the update committing `σ` unchanged,
`backend.rbPart`/`rbOwn` agreement.) -/
theorem inc_stop_image (hstop : mvccImage_stop.law (GF := GF)) (kv : GoInterface) (γk : MvccName)
    (bk : mvcc.KBReal) (D : backend.Data) (σ : MvccState) (r : GMap GoString backend.BktData)
    (L : List w64) (hσ : σ.pending = none) (hr : leaseRecsOk r L) :
    isMvcc (GF := GF) kv γk ∗ mvccBackend γk 1 (etcdStorage bk) iprop(True) ∗
      backend.bStopView bk.γB bk.P (mvccW bk.gx) iprop(True) D ∗ mvccState γk σ ∗
      backend.rbPart bk.γB (· = leaseName) r ={⊤}=∗
    ∃ u : Bool, mvccImage D σ.log σ.crev u ∗ ⌜leaseRecsOk (backend.rbData bk.P D) L⌝ := by
  iintro ⟨Hkv, Hmb, Hsv, Hσ, Hrb⟩
  -- the lease bucket: the writer's part against the stopped lock's `rbOwn`
  icases backend.bStopView_rbPart_agree bk.γB bk.P (mvccW bk.gx) iprop(True) D (· = leaseName) r
    $$ [$Hsv $Hrb] with ⟨Hsv, -, %Ha⟩
  have Hag : r.lookup leaseName = (backend.rbData bk.P D).lookup leaseName := Ha leaseName rfl
  imod hstop kv γk bk iprop(True) D (fun σ' => iprop(⌜σ' = σ⌝)) $$ [Hkv Hmb Hsv Hσ]
    with ⟨-, -, %σ', %u, %Hσ', Himg⟩
  · iframe Hmb Hsv Hkv
    iauintro
    unfold atomic_acc
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑mvccN from Std.LawfulSet.empty_subset)
    iintro Hclose
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ
    iframe Hσ
    isplitr
    · ipureintro; exact hσ
    isplit
    · iintro ⟨Hσ, -⟩; imod Hclose with -; imodintro; iexact Hσ
    · iintro -; imod Hclose with -; imodintro; ipureintro; rfl
  subst Hσ'
  imodintro
  iexists u
  iframe Himg
  ipureintro
  obtain ⟨recs, h1, h2, h3⟩ := hr
  exact ⟨recs, by rw [← Hag]; exact h1, h2, h3⟩

/-- The write-back stock's namespace (`wbStock`). -/
def wbStockN : Namespace := (nroot .@ "mvccfull") .@ "wbstock"

/-- **A backend's stock of write-back tokens** (persistent; mvccrand's `rcStock`, without mvccrand's
package assumptions): `n` tokens and the `a` receipts taken so far, `receiptBound ≤ a + n + 1`. -/
def wbStock (γB : backend.BNames) : IProp GF :=
  inv wbStockN iprop(∃ (a n : Nat), ⧗ a ∗ ownToks γB.wb n ∗ ⌜receiptBound GF ≤ a + n + 1⌝)

theorem wbStock_alloc (γB : backend.BNames) (n : Nat) (h : receiptBound GF ≤ n + 1) (E : CoPset) :
    ownToks (GF := GF) γB.wb n ⊢ |={E}=> wbStock γB := by
  iintro Hn
  imod receipt_zero (GF := GF) with H0
  unfold wbStock
  iapply inv_alloc wbStockN E
  inext
  iexists 0, n
  iframe H0 Hn
  ipureintro; omega

theorem wbStock_supply (γB : backend.BNames) :
    wbStock (GF := GF) γB ⊢ □ (⧗ 1 ={⊤}=∗ backend.wbTok γB) := by
  haveI : Persistent (wbStock (GF := GF) γB) := by unfold wbStock; infer_instance
  iintro #Hs
  iintro !> Hr
  unfold wbStock
  iinv Hs with ⟨%a, %n, >Ha, >Hn, >%Hb⟩ Hclose
  icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
  · iframe
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  icases ownToks_add_1 1 n' γB.wb $$ Hn with ⟨Hn, Ht⟩
  imod Hclose $$ [Ha Hn] with -
  · inext
    iexists a + 1, n'
    iframe Ha Hn
    ipureintro; omega
  imodintro
  iapply (backend.wbTok_toks γB).2
  iexact Ht

/-- **Reopen, the backend** (step 3, after `backend.New` on the file's data `D` at a fresh
registration `gx` and the limit `lim`; `mvccrand.rc_open` at any image): the store's storage at the
image's history (`mvccStorageFor`), what the writer keeps (`bkKeep`, `k` write-back tokens), the
hook's half unset, the lease bucket's part of the tracked buckets at `D` (for `NewLessor`), the
open share and token `NewLessor` and `SetTxPostLockInsideApplyHook` take. (Proof to come: `sorry`;
`rc_open`'s, with `etcdStorage_open.law` at the image in place of `mvccImage_fresh.law`.) -/
theorem inc_open_backend [ThreadBoundLe GF (2 ^ 28)] (hopen : etcdStorage_open.law (GF := GF))
    (hrest : backendRest_open.law (GF := GF)) (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) (path : GoString) (D : backend.Data)
    (L : Log) (c : Int) (u : Bool) (k : Nat) (hk : receiptBound GF + k + 4 ≤ backend.wbInit) :
    let bk := mvccrand.rcKB γB be gx lim
    □ (∀ (γ : backend.BNames) (P : backend.BParams) (b' : Loc), keySized (GF := GF) γ P b') ∗
      mvccWReg gx ∗ mvccImage D L c u ∗ backend.bFile γB path ∗
      backend.newPostK γB (mvccrand.rcP lim) (fun _ => mvccW gx) (fun _ => iprop(True))
        (backend.bFresh (GF := GF)) be D ={⊤}=∗
    mvccStorageFor (etcdStorage bk) iprop(True) L c u ∗ bkKeep bk path k ∗
      backend.plHook γB func.nil ∗ backend.rbPart γB (· = leaseName) (backend.rbData bk.P D) ∗
      backend.wbTok γB ∗ backend.wbTok γB := by
  intro bk
  have hT : threadBound GF ≤ backend.rdPoolN :=
    ThreadBoundLe.le_of (2 ^ 28) (Nat.le_of_eq backend.rdPoolN_val.symm)
  iintro ⟨#Hks, Hreg, Himg, Hbf, Hnew⟩
  icases backend.newPostK_named γB (mvccrand.rcP lim) (fun _ => mvccW gx) (fun _ => iprop(True))
    backend.bFresh be D $$ Hnew with ⟨#Hb, #Hsc, Hk, Hv, Hh, Hrb, Hrd, Hdl, Hfk, Hsr⟩
  icases (backend.bFresh_eq γB).1 $$ Hk with ⟨Hwb, Ho⟩
  icases (backend.bOpen_one_pool γB).1 $$ Ho with ⟨Hoh, Hpl, Hos⟩
  imod backend.rdToks_pool hT ⊤ γB (mvccrand.rcP lim) be $$ Hrd with ⟨#Hpool, Hrs⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, backend.rdStockN = n2 + 2 :=
    ⟨backend.rdStockN - 2, by have := backend.rdStockN_val; omega⟩
  have hn2' : backend.rdStockN - 2 = n2 := by omega
  rw [hn2]
  icases (backend.bigSepL_replicate_add _ n2 2).1 $$ Hos with ⟨Hos, Ho2⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Ho2 with ⟨Hor, Ho2⟩
  rw [List.replicate_one]
  ihave Ho2 := (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Ho2
  -- the write-back tokens: two for the open, two given back, `k` kept, the stock
  obtain ⟨N, hN⟩ : ∃ N, backend.wbInit = N + (4 + k) := ⟨backend.wbInit - (4 + k), by omega⟩
  rw [hN]
  icases ownToks_add_1 (4 + k) N γB.wb $$ Hwb with ⟨HwN, Hw⟩
  icases ownToks_add_1 k 4 γB.wb $$ Hw with ⟨Hw4, Hwk⟩
  icases ownToks_add_1 2 2 γB.wb $$ Hw4 with ⟨Hw2, Hw2'⟩
  icases ownToks_add_1 1 1 γB.wb $$ Hw2 with ⟨Hw1, Hw1'⟩
  icases ownToks_add_1 1 1 γB.wb $$ Hw2' with ⟨Hw3, Hw3'⟩
  haveI : Persistent (wbStock (GF := GF) γB) := by unfold wbStock; infer_instance
  imod wbStock_alloc γB N (by omega) ⊤ $$ HwN with #Hstock
  ihave #Hsup := wbStock_supply γB $$ Hstock
  ihave Hnp : backend.newPostKP (GF := GF) γB (mvccrand.rcP lim) (fun _ => mvccW gx)
      (fun _ => iprop(True)) (fun _ => iprop(True)) be D $$ [Hv Hh Hrb Hrs Hdl Hfk Hsr]
  · iapply backend.newPostKP_intro
    isplitr; iexact Hb
    isplitr; iexact Hsc
    isplitr; itrivial
    isplitl [Hv]; iexact Hv
    isplitl [Hh]; iexact Hh
    isplitl [Hrb]; iexact Hrb
    isplitr; iexact Hpool
    icases Hrs with ⟨Hra, Hrst⟩
    isplitl [Hra]; iexact Hra
    isplitl [Hrst]; iexact Hrst
    isplitl [Hdl]; iexact Hdl
    isplitl [Hfk]; iexact Hfk
    iexact Hsr
  ihave Hks' : (□ (∀ (γ : backend.BNames) (b' : Loc), keySized (GF := GF) γ (mvccrand.rcP lim) b'))
    $$ []
  · iintro !> %γ %b'; iapply Hks
  rw [← hn2']
  imod hopen bk (fun _ => iprop(True)) (fun _ => iprop(True)) D L c u (mvccrand.rcP_bridge lim)
      (mvccrand.rcP_lease lim) rfl
      $$ [Hks' Himg Hnp Hreg Hw1 Hw1' Hsup Hos] with ⟨Hsf, Hrest, Hrt, -⟩
  · rw [mvccrand.rcKB_P, mvccrand.rcKB_γB, mvccrand.rcKB_be, mvccrand.rcKB_gx]
    isplitl [Hks']; iexact Hks'
    isplitl [Himg]; iexact Himg
    isplitl [Hnp]; iexact Hnp
    isplitl [Hreg]; iexact Hreg
    isplitl [Hw1]; iapply (backend.wbTok_toks γB).2; iexact Hw1
    isplitl [Hw1']; iapply (backend.wbTok_toks γB).2; iexact Hw1'
    isplitl [Hsup]; iexact Hsup
    iexact Hos
  ihave ⟨-, -, Hhk, Hrbo, -⟩ := hrest _ _ _ _ _ $$ Hrest
  icases (backend.rbOwn_split γB (· = leaseName) _).1 $$ Hrbo with ⟨Hrbl, -⟩
  imodintro
  iframe Hsf Hhk Hrbl
  isplitl [Hbf Hoh Hor Hrt Hwk Ho2 Hpl]
  · iunfold bkKeep
    isplitr
    · ipureintro; exact ⟨mvccrand.rcKB_P γB be gx lim, rfl⟩
    simp only [bk, mvccrand.rcKB_P, mvccrand.rcKB_γB, mvccrand.rcKB_be, mvccrand.rcKB_gx]
    iframe #; iframe
    isplitl [Hrt Hor]
    · iapply (apply.bkRT_eq _).2
      simp only [mvccrand.rcKB_P, mvccrand.rcKB_γB, mvccrand.rcKB_be]
      iframe
    iunfold bkCensus
    simp only [mvccrand.rcKB_γB]
    iintro Ho1 Hhalf Hst
    rw [etcdStorage_rest]
    simp only [mvccrand.rcKB_γB]
    rw [hn2']
    imodintro
    iapply (backend.bOpen_one_pool γB).2
    rw [hn2]
    iframe Hhalf Hpl
    iapply (backend.bigSepL_replicate_add _ n2 2).2
    iframe Hst
    rw [List.replicate_succ, List.replicate_one]
    iapply BigSepL.bigSepL_cons.2
    iframe Ho1
    iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
    iexact Ho2
  isplitl [Hw3]
  · iapply (backend.wbTok_toks γB).2; iexact Hw3
  · iapply (backend.wbTok_toks γB).2; iexact Hw3'

/-- **The lessor's write contract at the member's backend** (`lessorW` keeps only `NewLessor`'s on
any backend, `lessorApplyOk`; review round 2's S5): at `bk`, from its contract (`bkKeep`'s) and the
hook frozen at `f` (`hookIs`, `memCore`'s; not `nil`, `hookOk`'s). (Proved: `lessorApplyOk_at`,
`rwLens_refl`.) -/
theorem lessorW_backend (γk : MvccName) (bk : mvcc.KBReal) (f : GoFunc) (lp : Loc) (L U : List w64)
    (σ : MvccState) (hf : f ≠ func.nil) :
    lessorW (GF := GF) γk bk f lp L U σ ∗ backend.isBackend bk.γB bk.P (mvccW bk.gx) iprop(True) bk.be ∗
      hookIs (etcdStorage bk) f ⊢
    lessorW γk bk f lp L U σ ∗
      lease.lessorBackend lp iprop(True) #f (backend.wbTok bk.γB) (lease.lessorBeOn lp bk.be)
        (apply.bkRT bk) (backend.rbPart bk.γB (· = leaseName)) := by
  iintro ⟨Hl, #Hb, #Hh⟩
  iunfold lessorW at Hl
  icases Hl with ⟨%rd, %r, #Hpkg, #Hinv, #Hcfg, #Hg, #Hrv, #Hok, Hrest⟩
  isplitl [Hrest]
  · iunfold lessorW; iexists rd, r; iframe #; iframe
  have hln : leaseName = go!"lease" := rfl
  rw [hln]
  iapply lessorApplyOk_at lp bk (mvccW bk.gx) iprop(True) f (lease.lessorBeOn lp bk.be)
  isplitr; iexact Hok
  isplitr; iexact Hb
  isplitr
  · rw [← etcdStorage_hookIs]; iexact Hh
  isplitr
  · ipureintro; exact hf
  · iapply rwLens_refl

/-- **Reopen, the incarnation** (step 3, after `mvcc.New`): a new incarnation's invariant (namespace
`memberN i`) at the new store `γk`, with the carried parts; the writer gets the whole retirement
token. (Proof to come: `sorry`; a fresh ghost variable, `inv_alloc` of the left disjunct.) -/
theorem inc_alloc (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (γk : MvccName) (kv : GoInterface) (σ : MvccState) (b : Bnd) (Hl : List HRev)
    (hkv : ∃ s : Loc, kv = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #s) :
    isMvcc (GF := GF) kv γk ∗ mvccState γk σ ∗ memberCarry ks γh mp m σ b Hl ={⊤}=∗
    ∃ ι : IncNames, ⌜ι.kv = γk⌝ ∗ isInc ks γh i mp m ι kv ∗ ghostVar ι.ret 1 () := by
  iintro ⟨Hkv, Hσ, Hcarry⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γr, Hret⟩
  imod inv_alloc (memberN i) ⊤ (memberInv (GF := GF) ks γh mp m ⟨γk, γr⟩) $$ [Hσ Hcarry] with #Hinv
  · inext; iunfold memberInv; ileft
    iapply (memberState_split ks γh mp m γk).2
    iexists σ, b, Hl; iframe
  imodintro
  iexists ⟨γk, γr⟩
  iframe Hret
  isplitr
  · ipureintro; rfl
  iunfold isInc; iframe; iframe #
  ipureintro; exact hkv

end chain

end mvccfull
end EtcdGrove
end Perennial
