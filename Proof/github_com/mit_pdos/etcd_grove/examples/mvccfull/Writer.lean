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
`True`, the revocable mode, its write contract, a reader slot, the owner's part at the live leases
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
   `backendRest_open.law`: `inc_open_backend`, `mvccrand.rc_open` at any image), `NewLessor.specR`
   over the records (`GA := True`, `reqOf := 3600`), `mvcc.New.specR` at the image's state (the
   lessor's owner part at the live leases, every key's lease live: `logOk_items`), the hook set and
   frozen (`SetTxPostLockInsideApplyHook`), a new incarnation's invariant allocated with the carried
   parts (`inc_alloc`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Streams
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.RunChecksBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiNewRestoring
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessorR
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

/- mvccrand's writer stack (imported for `rcP`, `rcKB`, `rc_open`) declares its own `Pos.Countable`
instances of mvcc's `MvccState` and `Change`, equal in body to `History.lean`'s but distinct
constants; `Members.lean`'s ghost variables (`memberState`'s `m.σ`) use `History.lean`'s. Prefer them
here, so that the writer's halves (`incW`, `memberCarry`) are syntactically the same ghost
variables as the incarnation invariant's (`icombine`, `ghostVar_agree` match syntactically). -/
attribute [local instance high] mvccfull.mvccState_countable mvccfull.change_api_countable

/-! ## The operation log's model (pure) -/

section model
variable [GooseExts]

/-- The operations' kinds (`opPut`, ..., `opLeases`). -/
abbrev kPut : w64 := W64 0
abbrev kDelete : w64 := W64 1
abbrev kTxn : w64 := W64 2
abbrev kGrant : w64 := W64 3
abbrev kRevoke : w64 := W64 4
abbrev kCompact : w64 := W64 5
abbrev kCommit : w64 := W64 6
abbrev kRead : w64 := W64 7
abbrev kLeases : w64 := W64 8

/-- **A range read's request** (`rangeReq`), its slices as strings (`endNil`: a `nil` end). -/
structure RangeM where
  key : GoString
  e : GoString
  endNil : Bool
  ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions

/-- **A transaction's sub-operation** (`subOp`): a put (`0`), a range delete (`1`) or a range read
(`2`). -/
structure SubM where
  kind : w64
  key : GoString
  e : GoString
  endNil : Bool
  val : GoString
  lease : w64
  q : RangeM

/-- **An operation of the log** (`op`), every choice made. -/
structure OpM where
  kind : w64
  key : GoString
  e : GoString
  endNil : Bool
  val : GoString
  lease : w64
  q : RangeM
  write : Bool
  shared : Bool
  subs : List SubM
  id : w64
  rev : w64
  wait : Bool

/-- **The model after a prefix of the log**: the history of revisions (`hs[r]`: revision `r`'s
state and changes; revisions `0` and `1` empty), the compaction revision (`-1`: none), the live
leases (in grant order, so increasing), every id ever granted. -/
structure MSt where
  hs : List HRev
  crev : Int
  leases : List w64
  granted : List w64
  /-- the revisions of the successful compactions, in order (the history's `comps`) -/
  comps : List w64

/-- The model before any operation. -/
def mStart : MSt := ⟨hist0, -1, [], [], []⟩

/-- The model's revision (the history's last). -/
def MSt.rev (s : MSt) : Nat := s.hs.length - 1

/-- The last revision's state of a history. -/
def lastSt (Hs : List HRev) : GMap GoString kvRec := (Hs[Hs.length - 1]?.map Prod.fst).getD ∅

/-- The history after a revision's model: the pending revision appended if it has a change. -/
def histAfter (Hs : List HRev) (P : PendM) : List HRev :=
  if P.chs = [] then Hs else Hs ++ [(P.st, P.chs)]

/-- **The tester's test of a key on the lease `id`** in `M` (`ok && e.lease == id`). -/
def onLease (M : GMap GoString kvRec) (id : w64) (k : GoString) : Bool :=
  match M !! k with
  | some e => decide (e.lease' = id)
  | none => false

/-- A write transaction's sub-operation on its pending model (`writeSub`). -/
def subStep (ks : List GoString) (P : PendM) (s : SubM) : PendM :=
  if s.kind = W64 0 then P.put s.key s.val s.lease
  else if s.kind = W64 1 then P.del ks s.endNil s.key s.e
  else P

/-- **The pending model of the revision an operation makes** at the model `s` (`apply`'s `p`):
from the last state at the next revision number, a put, a range delete, a write transaction's
sub-operations, a revoke's deletes (the keys on the lease, in order); nothing for the others. -/
def opPend (ks : List GoString) (s : MSt) (o : OpM) : PendM :=
  let P0 : PendM := ⟨W64 (s.hs.length : Int), lastSt s.hs, []⟩
  if o.kind = kPut then P0.put o.key o.val o.lease
  else if o.kind = kDelete then P0.del ks o.endNil o.key o.e
  else if o.kind = kTxn then (if o.write then o.subs.foldl (subStep ks) P0 else P0)
  else if o.kind = kRevoke then (ks.filter (onLease P0.st o.id)).foldl PendM.delOne P0
  else P0

/-- **One operation's model step**: the revision appended if it changed something, the
compaction revision raised by a compaction above it and not past the revision, the live leases
after a grant or a revoke, the granted ids after a grant. -/
def opStep (ks : List GoString) (s : MSt) (o : OpM) : MSt :=
  let cok := decide (o.kind = kCompact ∧ s.crev < sint.Z o.rev ∧ sint.Z o.rev ≤ (s.rev : Int))
  { hs := histAfter s.hs (opPend ks s o),
    crev := if cok then sint.Z o.rev else s.crev,
    comps := if cok then s.comps ++ [o.rev] else s.comps,
    leases := if o.kind = kGrant then s.leases ++ [o.id]
      else if o.kind = kRevoke then s.leases.filter (· != o.id) else s.leases,
    granted := if o.kind = kGrant then s.granted ++ [o.id] else s.granted }

/-- **The model after the first `n` operations of the log.** -/
def runM (ks : List GoString) (ops : List OpM) (n : Nat) : MSt := (ops.take n).foldl (opStep ks) mStart

/-- The member's `rev`, `cmp`, `leases` after `n` operations, and the history then. -/
abbrev revAfter (ks : List GoString) (ops : List OpM) (n : Nat) : Nat := (runM ks ops n).rev
abbrev cmpAfter (ks : List GoString) (ops : List OpM) (n : Nat) : Int := (runM ks ops n).crev
abbrev leasesAfter (ks : List GoString) (ops : List OpM) (n : Nat) : List w64 := (runM ks ops n).leases
abbrev grantedAfter (ks : List GoString) (ops : List OpM) (n : Nat) : List w64 :=
  (runM ks ops n).granted
abbrev histAt (ks : List GoString) (ops : List OpM) (n : Nat) : List HRev := (runM ks ops n).hs
abbrev compsAt (ks : List GoString) (ops : List OpM) (n : Nat) : List w64 := (runM ks ops n).comps

/-- mvcc's change of a tester's change. -/
def toChange (c : change) : Change :=
  if c.del' then .del c.key' else .put c.key' c.kv'.val' c.kv'.lease'

/-- **mvcc's log of a history**: each revision's changes. -/
def logOfHist (Hs : List HRev) : Log := Hs.map fun e => e.2.map toChange

/-- **The store's state of a member that applied `n` operations** (nothing pending). -/
def σOf (ks : List GoString) (ops : List OpM) (n : Nat) : MvccState :=
  ⟨logOfHist (histAt ks ops n), cmpAfter ks ops n, none⟩

/-- The store's state after a write transaction begun at `σ` (nothing pending) ends with `pend`. -/
def commitSt (σ : MvccState) (pend : List Change) : MvccState := (σ.notify pend).commitPending

/-- **A pending transaction's model is the tester's** (mvccrand's, over the keys `ks`): inside a
write transaction begun at `σ`, the member's history at `Hs` (its revisions, `σ`'s), mvcc's pending
changes `pend`: `pendOf` of the last revision's state, holding the store's state after them. -/
def pendOk (ks : List GoString) (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM) :
    Prop :=
  P = pendOf (lastSt Hs) (W64 (Hs.length : Int)) pend ∧
  stMatch ks P.st (applyChanges (W64 (σ.log.length : Int)) (stateAfter σ.log) pend)

/-- What `view` returns: the states (the pending one appended once it has a change), their
fractions, the revision a read in the transaction is at. -/
def viewSt (Hs : List HRev) (P : PendM) : List (GMap GoString kvRec) :=
  Hs.map Prod.fst ++ (if P.chs = [] then [] else [P.st])

def viewDq (Hs : List HRev) (P : PendM) : List DFrac :=
  List.replicate Hs.length DFrac.discard ++ (if P.chs = [] then [] else [DFrac.own 1])

def viewRev (P : PendM) : w64 := if P.chs = [] then P.rev - W64 1 else P.rev

/-- The batch limit `openBackend` configures (`cfg.BatchLimit` if positive, else
`DefaultBackendConfig`'s `10000`). -/
def limOf (cfg : Config) : w64 := if 0 < sint.Z cfg.BatchLimit' then cfg.BatchLimit' else W64 10000

/-- The compaction batch limit `open` configures (`cfg.CompactionBatchLimit` if positive, else `0`:
mvcc's default). -/
def cblOf (cfg : Config) : w64 :=
  if 0 < sint.Z cfg.CompactionBatchLimit' then cfg.CompactionBatchLimit' else W64 0

/-- **A write transaction's sub-operations, as `genSubs` makes them** (the keys
`ks`, the live leases `L`): each put's key one of the keys, its lease `0` or live; a put's key is no earlier put's and in
no earlier delete's range, and no earlier put's key is in a delete's range (etcd's
`checkIntervals`). -/
def subsOk (ks : List GoString) (L : List w64) (subs : List SubM) : Prop :=
  (∀ x ∈ subs, x.kind = W64 0 → x.key ∈ ks ∧ (x.lease = W64 0 ∨ x.lease ∈ L)) ∧
  ∀ (i j : Nat) (a b : SubM), i < j → subs[i]? = some a → subs[j]? = some b →
    (a.kind = W64 0 → b.kind = W64 0 → a.key ≠ b.key) ∧
    (a.kind = W64 1 → b.kind = W64 0 → inRangeM a.endNil a.key a.e b.key = false) ∧
    (a.kind = W64 0 → b.kind = W64 1 → inRangeM b.endNil b.key b.e a.key = false)

/-- **An operation valid at the model `s`** (see the file header). -/
def opValid (ks : List GoString) (s : MSt) (o : OpM) : Prop :=
  sint.Z o.kind < 9 ∧ 0 ≤ sint.Z o.kind ∧
  (o.kind = kPut → o.key ∈ ks ∧ (o.lease = W64 0 ∨ o.lease ∈ s.leases)) ∧
  (o.kind = kTxn → o.write = true → subsOk ks s.leases o.subs) ∧
  (o.kind = kGrant → 0 < sint.Z o.id ∧ ∀ id ∈ s.granted, sint.Z id < sint.Z o.id) ∧
  (o.kind = kRevoke → o.id ∈ s.leases) ∧
  (o.kind = kCompact → 1 ≤ sint.Z o.rev)

/-- **The log is valid**: each operation at the model before it. -/
def logOk (ks : List GoString) (ops : List OpM) : Prop :=
  ∀ i (o : OpM), ops[i]? = some o → opValid ks (runM ks ops i) o

/-- **The lease bucket holds exactly the live leases' records**, in key order (`backend.bktEnts`):
each `Grant`'s record (`leaseRecEnc`: the id, a TTL of at least the requested `3600` (the
lessor's minimum may raise it), the remaining TTL). The tracked buckets `r`. -/
def leaseRecsOk (r : GMap GoString backend.BktData) (L : List w64) : Prop :=
  ∃ recs : List (w64 × w64 × w64),
    backend.bktEnts ((r.lookup leaseName).getD ∅) = recs.map lease.leaseRecEnc ∧
    recs.map (·.1) = L ∧ ∀ x ∈ recs, 3600 ≤ sint.Z x.2.1

/-! ### The model's facts (pure; proofs to come, marked) -/

theorem runM_zero (ks : List GoString) (ops : List OpM) : runM ks ops 0 = mStart := by
  simp [runM]

/-- The step to `n + 1`. (Pure; proved.) -/
theorem runM_succ (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM) (h : ops[n]? = some o) :
    runM ks ops (n + 1) = opStep ks (runM ks ops n) o := by
  unfold runM
  rw [List.take_add_one, h, List.foldl_append]
  rfl

/-- The model of a prefix of the log is the log's (the follower's and the builder's model is the
leader's at their counts). (Pure; proved.) -/
theorem runM_prefix (ks : List GoString) (ops ops' : List OpM) (n : Nat) (hp : ops <+: ops')
    (hn : n ≤ ops.length) : runM ks ops' n = runM ks ops n := by
  obtain ⟨t, rfl⟩ := hp
  unfold runM
  rw [List.take_append_of_le_length hn]

/-- **Every revision of a valid log changes each key at most once** (`genSubs`' rule, a put or a
delete of one key, a revoke's distinct keys). (Pure; proof `sorry`, Draft.) -/
theorem logOk_once (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (n : Nat) : onceUpToAll (σOf ks ops n).notifiedLog := by
  sorry

/-- **The store state of a member is reachable, and the history covers it** (`revOk` at every
revision: `histOkM` against the history at any later count). (Pure; proof `sorry`, Draft.) -/
theorem logOk_hist (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (n n' : Nat) (hn : n ≤ n') (hn' : n' ≤ ops.length) :
    histAt ks ops n <+: histAt ks ops n' ∧ histOkM ks (σOf ks ops n) (histAt ks ops n') ∧
      MvccReachable (σOf ks ops n) := by
  sorry

/-- **The model only grows along the log**: the revision, the compaction revision (both
monotone: `Restore`'s premise from the follower to the builder's later count) and the history as a
prefix. (Pure; proof `sorry`, Draft.) -/
theorem runM_mono (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    revAfter ks ops n ≤ revAfter ks ops n' ∧ cmpAfter ks ops n ≤ cmpAfter ks ops n' ∧
      (σOf ks ops n).log <+: (σOf ks ops n').log := by
  sorry

/-- **The live leases are granted, increasing, positive**, and every key of the state is on no
lease or a live one (`New.specR`'s and `Restore`'s item premise, the key short). (Pure; proof
`sorry`, Draft.) -/
theorem logOk_leases (ks : List GoString) (hks : ∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1)
    (ops : List OpM) (h : logOk ks ops) (n : Nat) :
    (leasesAfter ks ops n).Pairwise (fun a b => sint.Z a < sint.Z b) ∧
    (∀ id ∈ leasesAfter ks ops n, 0 < sint.Z id ∧ id ∈ grantedAfter ks ops n) ∧
    ∀ it lid, (pendItems (σOf ks ops n).log []).lookup it = some lid →
      lid ∈ leasesAfter ks ops n ∧ (it.Key'.length : Int) < 2 ^ 63 - 1 := by
  sorry

/-- **`Recover`'s premise on the ids** (the follower's lessor at its count `n`, recovering the
builder's records at the leader's count `n' ≥ n`): a lease live at `n'` that was granted by `n` is
live at `n` (an id is never granted twice, so it was not revoked in between). (Pure; proof
`sorry`, Draft.) -/
theorem logOk_recover (ks : List GoString) (ops : List OpM) (h : logOk ks ops) (n n' : Nat)
    (hn : n ≤ n') :
    ∀ id ∈ leasesAfter ks ops n', id ∈ grantedAfter ks ops n → id ∈ leasesAfter ks ops n := by
  sorry

end model

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
at the live leases `L` and the store state `σ`, the ids it ever had `U` (see the file header). -/
def lessorW (γk : MvccName) (bk : mvcc.KBReal) (f : GoFunc) (lp : Loc) (L U : List w64)
    (σ : MvccState) : IProp GF :=
  iprop(∃ (rd : GoFunc) (r : GMap GoString backend.BktData),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
    lease.lessorInv lp (mvccLeases γk) ∗ lease.lessorCfg lp ∗
    lease.lessorGuard (mvccLeases γk) (fun _ => iprop(True)) ∗ lease.lessorRevocable (mvccLeases γk) ∗
    lease.lessorBackend lp iprop(True) #f (backend.wbTok bk.γB) (lease.lessorBeOn lp bk.be)
      (apply.bkRT bk) (backend.rbPart bk.γB (· = leaseName)) ∗
    lease.lessorRd lp (mvccLeases γk) ∗
    lease.leaseOwn (mvccLeases γk) L (pendItems σ.log []) ∗ lease.leaseRevokers (mvccLeases γk) L ∗
    lease.leaseEver (mvccLeases γk) U ∗
    □ ([∗list] id ∈ U, lease.leaseReqIs (mvccLeases γk) id (W64 3600)) ∗
    lease.rdOwn (mvccLeases γk) rd ∗ mvccDeleter rd γk ∗ lease.lessorBeOn lp bk.be ∗
    backend.rbPart bk.γB (· = leaseName) r ∗ ⌜leaseRecsOk r L⌝ ∗ lease.lessorStopTok lp)

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
packages, the keys' lengths, the logger, the writer's weights, the report counters it adds to. -/
def writerCtx (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc)
    (γh : HistNames) : IProp GF :=
  iprop(rnCtx x ks cfg h γh ∗ runnerCfg x cfg wr ∗ ⌜readMixOk (wr.map sint.Z)⌝ ∗ rdShared x ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
    ⌜∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1⌝ ∗
    (∃ lg : Loc, rF go!"lg" x ↦□ lg ∗ ⌜lg ≠ null⌝) ∗
    (∃ wo : List w64, cfg.Mix'.Op' ↦*□ wo) ∗ (∃ wc : List w64, cfg.Mix'.CompactAt' ↦*□ wc) ∗
    (∃ ws : List w64, cfg.Mix'.Step' ↦*□ ws) ∗
    ctrInv (readersN .@ "revisions") (rF go!"revisions" x) ∗
    ctrInv (readersN .@ "compactions") (rF go!"compactions" x) ∗
    ctrInv (readersN .@ "restores") (rF go!"restores" x) ∗
    ctrInv (readersN .@ "restarts") (rF go!"restarts" x))

instance writerCtx_persistent (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64)
    (h : Loc) (γh : HistNames) : Persistent (writerCtx (GF := GF) x ks cfg wr h γh) := by
  unfold writerCtx rnCtx runnerKeys runnerH runnerCfg runnerRangeMix rdShared ctrInv
  infer_instance

/-- **The writer's own counters**: `nextLease` at the largest id granted (`0` before any), `vals`
at `nv`, `builds` at `nb`, each in range. -/
def writerCtrs (x : Loc) (ks : List GoString) (ops : List OpM) (nv nb : Nat) : IProp GF :=
  iprop(∃ nl : w64, rF go!"nextLease" x ↦ nl ∗ rF go!"vals" x ↦ (W64 (nv : Int)) ∗
    rF go!"builds" x ↦ (W64 (nb : Int)) ∗
    ⌜0 ≤ sint.Z nl ∧ ∀ id ∈ grantedAfter ks ops ops.length, sint.Z id ≤ sint.Z nl⌝)

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
(`memW`, each keeping a reader token of its own, `1 ≤ nw`) with their epoch's streams (`epochStream`, `m.streams`) and the readers' join (`startReaders`' post: the lent stock). The leader is at the log's
end, the follower behind. -/
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
    ⌜v0.ops = ops.length ∧ v1.ops ≤ v0.ops⌝ ∗
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
  iintro ⟨⟨#Hinv, -⟩, Hret⟩
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
  iunfold apply.bkRT at HRT
  icases HRT with ⟨-, Hor⟩
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
  ihave %Hag : ⌜(r.lookup leaseName) = (backend.rbData bk.P D).lookup leaseName⌝ $$ [Hsv Hrb]
  · iunfold backend.bStopView at Hsv
    icases Hsv with ⟨-, -, -, -, Hown, -⟩
    iunfold backend.rbOwn at Hown
    icases backend.rbPart_agree bk.γB (· = leaseName) (fun _ => True) r _ $$ [$Hrb $Hown]
      with ⟨-, -, %Ha⟩
    ipureintro; exact Ha leaseName rfl trivial
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
  sorry

/-- **Reopen, the incarnation** (step 3, after `mvcc.New`): a new incarnation's invariant (namespace
`memberN i`) at the new store `γk`, with the carried parts; the writer gets the whole retirement
token. (Proof to come: `sorry`; a fresh ghost variable, `inv_alloc` of the left disjunct.) -/
theorem inc_alloc (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (γk : MvccName) (kv : GoInterface) (σ : MvccState) (b : Bnd) (Hl : List HRev) :
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

end chain

end mvccfull
end EtcdGrove
end Perennial
