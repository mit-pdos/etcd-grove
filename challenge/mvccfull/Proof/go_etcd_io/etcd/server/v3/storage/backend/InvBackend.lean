/-
The backend's locks and what they hold (`batch_tx.go`, `read_tx.go`, `backend.go`). Lean-first
(no Rocq counterpart); see `Model2.lean` and `notes/decisions.md`, "The backend: the buffers,
bbolt as a key-value contract, the locks and the views".

**Ghost state.**
- `γ.view` (`ghostVar RView`): the readers' state, the committed data of the batch interval and
  the read buffer; half the clients' (`bView γ q rv`, at `q/2`), a quarter the batch lock's, a
  quarter `readTx.mu`'s (fractional). Readers agree with the clients' share; changing it needs
  all of it: an `Unlock` after a session that wrote takes the clients' whole half.
- `γ.rd` (`ghostVar RdSt`): the read side's physical layout, all of it `readTx.mu`'s (so that
  readers' fractions agree on it).
- `γ.hist` (a ghost map from `(version, index)` to `RView`, persistent elements): every state of
  the read side, recorded by the batch lock's holder when it changes it; `γ.cached` (persistent
  marks): the states a `ConcurrentReadTx` copied into the cache. `cacheInv` lets a reader mark
  only the current state, and only while no `Unlock` is in progress (the writer deposits the
  clients' half of the view there for the window): so the cache's copy at the current version
  reads as the current state off the hook's buckets (`rtRes`'s `cacheValid`).
- `γ.hook` (`dghostVar GoFunc`): the post-lock hook, half the client's (`plHook γ f`), half the
  batch lock's; the client may make its half read-only (`plHook_persist`: `plHookRO γ f`, persistent:
  the hook then never changes);
  `γ.opn`: the backend open, half the clients' (`bOpen γ q`), half the `run` goroutine's;
  `γ.wb`: the write-back budget (`wbTok γ`: an `Unlock` may increment the read buffer's version,
  a `uint64`, whose wrap-around would make a stale cache look current); `γ.rdt`: the readers'
  budget (`rdTok` holds one: `txWg`'s counter is an `int32`).

**The locks.**
- *The batch lock* (`batchTx.Mutex`, `batchFree`): the batch transaction's state for a `BSess`
  (`batchPhys`), the view's quarter at `(C, R)`, `freeOk`, the write-back budget's authority
  (the version plus the tokens left below `2^64`), and the clients' resources `W` (the lock
  holder's) and `Pk` (the hooks': the pre-commit and post-lock hooks run on it).
- *`readTx.mu`* (guarded `RWMutex`, `rtRes q`): the shared read transaction's fields at `q`, the
  view's and `γ.rd`'s shares, the history's authority at `q`, and, while a bbolt read
  transaction is open, its `txLive` share, the interval's invariants and `wgOpen` at `q`.
- *`txMu`* (one for the backend's life; `tmTok q`): two fractional tokens; each interval's
  `intvInv` exchanges its buckets map (at a fraction) for the same fraction of the first, and its
  `rtxStats` for the whole second. The commit that begins an interval allocates it, without
  `txMu`.
- *The interval's `WaitGroup`* (`wgInv`): a `ConcurrentReadTx` adds one and takes half of the
  pool of `txLive` (its `rdShare`, with a receipt); `Done` gives it back. The commit that ends the
  interval deposits `wgOpen 1` (no reader adds any more); the rollback goroutine's `Wait` then
  finds the counter 0 and takes the whole pool.
- *The cache* (`txReadBufferCache.mu`, `cacheRes`): the cached copy (persistent) at a version,
  marked.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Proof.TokSet
public import Perennial.Proof.sync
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Spec.go_uber_org.zap.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- The backend's ghost names. -/
structure BNames where
  db : DBNames
  view : GName
  rd : GName
  hist : GName
  cached : GName
  cur : GName
  hook : GName
  opn : GName
  wb : GName
  rdt : GName
  txa : GName
  txb : GName
  rvs : GName
  cvw : GName
  wbc : GName
  used : GName
  cls : GName
  sdn : GName
  stk : GName
  /-- `ghostVar`: the writer's contents on the hook's own keys (`hkData`), half the batch
  lock's, half the client's (`hkOwn`) -/
  hkd : GName
  /-- ghost map over the tracked buckets' names `rbD`: each bucket's contents in the writer's
  contents (`rbData`, D22, 2026-10-23) and whether a session's write to it is pending (decision 3,
  2026-11-01); half of each element the batch lock's (`rbSide`), half the client's (`rbPart`,
  `rbOwnIn`, `rbOwn`), the authority the batch lock's -/
  rbk : GName
  /-- `ghostVar Bool`: whether the read buffer is known clean off the hook's buckets (`rbClean`;
  the restore plan's R5a, 2026-10-23), half the clients' (inside `bView`), half `readTx.mu`'s
  (`RdSt.cln`) -/
  cln : GName
  /-- saved predicate: the deletable keys' registration (`DelKeys.lean`, `dlReg`; the
  backend-compaction stage, decision O1): allocated by the constructor at `False` (nothing
  deletable), its whole fraction to the creator (`dlInit`), who fixes the predicate once -/
  dlg : GName
  /-- `dghostVar Bool`: whether keys may be deletable at all (O1's fallback, decided by the agent
  while the user was away, 2026-10-29): allocated at `false`, its whole fraction to the creator
  (`dlInit`), who fixes it once, at `true` with the predicate (`dlReg`) or at `false` (`dlNoDel`):
  a discrete value, so "nothing deletable" needs no later -/
  dlb : GName
  /-- `monoNat`: the compaction keys' flag (`fkKey`; the backend-compaction stage, 2026-10-29):
  `0` while no state of the backend has one, `1` once one may. Half its authority the batch
  lock's (`fkHalf`), half the client's (`fkOwn`); the readers keep a lower bound (`fkRd`). -/
  fk : GName
  /-- `dghostVar FkG`, discarded at allocation: whether the compaction keys hold only
  well-formed values (`P.FV`) in every state of the backend (question 4, 2026-10-29: true when the
  data at creation does, `fkWInit`; a put of one needs a well-formed value, so it never changes),
  and (M2 storage plan, items 27/29, 2026-10-30) the flag's value and the keys' values at the open
  (`fkInit`, `fkVals`) -/
  fkv : GName
  /-- `dghostVar (Loc × GoString)`, discarded at allocation (2026-11-04, R2b-3c): bbolt's database
  and the file it is (`bDB`, `bFile`), so that the stop's escrow and `Close` agree on it -/
  dbf : GName
  /-- saved proposition (2026-11-04, the restart plan's R2b-3d stage 3): the result `Y` of the
  request `Close`'s caller makes of the stop's commit (`stopReq`): both halves in the stop
  invariant at `True` until `Close` sets them to `Y`; one its claim, one deposited with the request,
  which `run` carries to `donec`'s escrow with `Y` -/
  rq : GName
  /-- The tracked buckets' names (`rbData`'s at creation and the table's tracked buckets: every
  bucket a session can write), the keys of the ghost map `γ.rbk` (decision 3 of
  `notes/backend-auth-split-plan.md`): pure, fixed by the constructor -/
  rbD : GMap GoString Unit
  /-- `ghostVar FkVals`: the compaction keys' values in the writer's contents (`fkVals`; the
  user's decision, 2026-11-04, round 16's F1: a snapshot's observation sees them), half the batch
  lock's (`fkHalf`), half the client's (inside `fkOwn`), as the hook's own keys' `hkd` -/
  fkd : GName
  /-- `ghostVar` of the safe-range buckets' deleted entries (`dlR` of the session's `dl`; the
  user's decision, 2026-11-04, probe M2: a snapshot's observation knows the safe-range bucket
  exactly), half the batch lock's (`fkHalf`), half the client's (inside `fkOwn`): a delete from a
  safe-range bucket updates both -/
  dls : GName

section phys
variable [GooseExts]

/-- The read side's layout: the interval's bbolt read transaction (null once the backend
stopped) and `WaitGroup` (with the protocol's ghost names), the current state's index in the
history, whether an `Unlock`'s window is open (between its write-back and its commit) and
whether an interval is open (false once the backend stopped). (The read buffer's layout and the
buckets map are not recorded: a reader's call of `baseReadTx.UnsafeRange` gives them back
existentially; fractions agree on them, `rbAt_agree`.) -/
structure RdSt where
  rtx : Loc
  wg : Loc
  γw : GName
  γo : GName
  γt : GName
  idx : Nat
  win : Bool
  live : Bool
  /-- the read buffer known clean off the hook's buckets (`γ.cln`'s value) -/
  cln : Bool

instance rdSt_countable : Pos.Countable RdSt :=
  countableOfLeftInverse
    (fun x : RdSt => (x.rtx, x.wg, x.γw, x.γo, x.γt, x.idx, x.win, x.live, x.cln))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

end phys

/-- The invariants' namespace. -/
abbrev bN : Namespace := nroot.@"backend"

/-- The order of the read side's states: by version (as an unsigned number), then index. -/
def keyLe (k k' : w64 × Nat) : Prop :=
  uint.Z k.1 < uint.Z k'.1 ∨ (k.1 = k'.1 ∧ k.2 ≤ k'.2)

/-- The readers' budget (`txWg`'s counter is an `int32`: below `2^31 - 1`). -/
def rdMax : Nat := 2 ^ 31 - 2

/-- The sum of the receipts' fractions. -/
def qsum (outs : GMap Nat Qp) : Rat := (outs.toList.map (fun x => ((x.2 : Qp) : Rat))).sum

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

abbrev bF (f : GoString) (b : Loc) : Loc := structFieldRef backend f b
abbrev btOf (t : Loc) : Loc := structFieldRef batchTxBuffered go!"batchTx" t
abbrev muOf (t : Loc) : Loc := structFieldRef batchTx go!"Mutex" (btOf t)
abbrev txFOf (t : Loc) : Loc := structFieldRef batchTx go!"tx" (btOf t)
abbrev pendOf (t : Loc) : Loc := structFieldRef batchTx go!"pending" (btOf t)
abbrev beOf (t : Loc) : Loc := structFieldRef batchTx go!"backend" (btOf t)
abbrev wbOf (t : Loc) : Loc := structFieldRef batchTxBuffered go!"buf" t
abbrev delOf (t : Loc) : Loc := structFieldRef batchTxBuffered go!"pendingDeleteOperations" t
abbrev baseOf (rt : Loc) : Loc := structFieldRef readTx go!"baseReadTx" rt
abbrev rmuOf (base : Loc) : Loc := structFieldRef baseReadTx go!"mu" base
abbrev rbufOf (base : Loc) : Loc := structFieldRef baseReadTx go!"buf" base
abbrev rtxOf (base : Loc) : Loc := structFieldRef baseReadTx go!"tx" base
abbrev rbktOf (base : Loc) : Loc := structFieldRef baseReadTx go!"buckets" base
abbrev rwgOf (base : Loc) : Loc := structFieldRef baseReadTx go!"txWg" base
abbrev rtmuOf (base : Loc) : Loc := structFieldRef baseReadTx go!"txMu" base
abbrev cacheOf (b : Loc) : Loc := bF go!"txReadBufferCache" b
abbrev cmuOf (b : Loc) : Loc := structFieldRef txReadBufferCache go!"mu" (cacheOf b)
abbrev cbufOf (b : Loc) : Loc := structFieldRef txReadBufferCache go!"buf" (cacheOf b)
abbrev cverOf (b : Loc) : Loc := structFieldRef txReadBufferCache go!"bufVersion" (cacheOf b)

end addrs

/-! ## The logical view after a put session (question 2, option (a), 2026-10-29) -/

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-! ## The clients' tokens -/

/-- The readers' view off the hook's buckets (`vData`), as the clients see it. -/
abbrev VData := GMap (GoString × GoString) GoString

/-- The clients' share of the readers' view, and of the clients' token `γ.cvw` (whose other
half `cacheInv` keeps: so no client holds any share while an `Unlock`'s window has the clients'
whole share deposited in `cacheInv`). -/
def bViewC (γ : BNames) (q : Qp) (vd : VData) (c : Bool) : IProp GF :=
  iprop(ghostVar γ.view q.half vd ∗ ghostVar γ.cvw q.half () ∗ ghostVar γ.cln q.half c)

/-- The clients' share of the readers' view, with or without the read buffer known clean
(`bViewC`, the restore plan's R5a). -/
def bView (γ : BNames) (q : Qp) (vd : VData) : IProp GF :=
  iprop(∃ c : Bool, bViewC γ q vd c)

/-- The clients' share of the backend being open (`γ.opn`, a `dghostVar` of whether it
stopped: half of it the clients', a quarter the `run` goroutine's, a quarter the batch lock's;
the stop makes it `true` and persistent), and of the right to close it (`γ.cls`: `Close`, with all
of it, closes `stopc` once). -/
def bOpen (γ : BNames) (q : Qp) : IProp GF :=
  iprop(dghostVar γ.opn (DFrac.own q.half) false ∗ ghostVar γ.cls q ())

/-- The backend stopped (persistent). -/
def bStopped (γ : BNames) : IProp GF := dghostVar γ.opn DFrac.discard true

/-- (2026-11-04, R2b-3c) **The backend's bbolt database is `db`, the file at `path`** (persistent). -/
def bDBAt (γ : BNames) (db : Loc) (path : GoString) : IProp GF :=
  dghostVar γ.dbf DFrac.discard ((db, path) : Loc × GoString)

/-- (R2b-3c) The backend's bbolt database is `db` (persistent). -/
def bDB (γ : BNames) (db : Loc) : IProp GF := iprop(∃ path : GoString, bDBAt γ db path)

/-- The clients' share `dq` of the post-lock hook (a `dghostVar`; the batch lock holds an owned
half). -/
def plHookAt (γ : BNames) (dq : DFrac) (f : GoFunc) : IProp GF := dghostVar γ.hook dq f

/-- The post-lock hook is `f` for good (persistent: `plHook_persist`). -/
abbrev plHookRO (γ : BNames) (f : GoFunc) : IProp GF := plHookAt γ DFrac.discard f

/-- One write-back's budget (an `Unlock` costs one). -/
def wbTok (γ : BNames) : IProp GF := ownToks γ.wb 1

/-- One tracked bucket's ghost element (`γ.rbk`, a ghost map over the tracked buckets' names
`γ.rbD`), at fraction `q`: the bucket's contents in the writer's contents (absent if absent) and
whether a write of a session to it is pending since the last `Unlock` that was handed its part
(decision 3, option (b), `notes/backend-auth-split-plan.md`). -/
abbrev rbElem (γ : BNames) (n : GoString) (q : Qp) (v : Option BktData × Bool) : IProp GF :=
  ghostMapElem γ.rbk n (DFrac.own q) v

open Classical in
/-- The elements of the tracked buckets of `S`, at fraction `q` and values `v`. -/
def rbEls (γ : BNames) (S : GoString → Prop) (q : Qp) (v : GoString → Option BktData × Bool) :
    IProp GF :=
  [∗map] n ↦ _u ∈ γ.rbD, (if S n then rbElem γ n q (v n) else iprop(True))

/-- The client's part of the tracked buckets of `S` at contents `r` and pending flags `F` (the
names of `S` outside `γ.rbD`, the backend's tracked buckets, absent from `r`). -/
def rbPartF (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) (F : GoString → Bool) :
    IProp GF :=
  iprop(⌜∀ n, S n → γ.rbD.lookup n = none → r.lookup n = none⌝ ∗
    rbEls γ S (1 : Qp).half (fun n => (r.lookup n, F n)))

/-- **The client's part of the tracked buckets in `S`** (`P.RB`; D22's tracked-bucket token, split
by bucket set, decision 3): the **writer's contents** hold `r` at the tracked buckets of `S` (each
absent if `r` has it absent), and only the holder writes them (`UnsafePut`, `UnsafeDelete`,
`UnsafeCreateBucket`, `UnsafeDeleteBucket` on a bucket of `S` take its part: `rbPut`). A write of
the holder's own session to `S` may be pending. -/
def rbPart (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) : IProp GF :=
  iprop(∃ F : GoString → Bool, rbPartF γ S r F)

/-- **The client's idle part of the tracked buckets in `S`**: `rbPart`, and no write to a bucket of
`S` pending: no session has put in, deleted from, created or deleted one since the last
`Unlock` that was handed this part (which makes it idle; an `Unlock.bare` makes nothing idle: `batchTxBuffered.Unlock.spec`); a write needs the
holder's part, so no one else makes it pending. A ghost fact about the session's writes (option
(b) of the plan note), not about the readers: that a reader begun after it sees `r` on `S`, an
uncommitted bucket created in the session as empty (`bktOf`), is Go's
(`batchTxBuffered.Unlock` writes the session's puts back into the read buffer and commits when a
delete is pending, etcd-io/etcd#17119), argued in the docstring of each trusted reader that takes
it; the read model's version of it (`rtHeldF_rbOwnIn`) is option (a), a later stage. -/
def rbOwnIn (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) : IProp GF :=
  rbPartF γ S r (fun _ => false)

/-- **The client's half of the tracked buckets** (D22, 2026-10-23: the backend over every
bucket): the writer's contents hold `r` there (`rbData`: each tracked bucket's contents, absent
if absent). Only its holder can put in, delete from, create or delete a tracked bucket
(`UnsafePut`, `UnsafeDelete`, `UnsafeCreateBucket`, `UnsafeDeleteBucket`), and it agrees with
every state of the batch lock and with what a snapshot's commit leaves (`backend.Snapshot`). Since
decision 3: the part of every bucket (`rbPart γ ⊤ r`), its text and meaning kept; the batch lock
holds the same shape (`rbSide`), so a snapshot's observation is handed one. -/
def rbOwn (γ : BNames) (r : GMap GoString BktData) : IProp GF :=
  rbPart γ (fun _ => True) r

/-- **A half of the compaction keys' values** (`γ.fkd`; the user's decision, 2026-11-04, round
16's F1): the values `v` the writer's contents hold at the compaction keys (`fkVals`). One half is
the client's (inside `fkOwn`), the other the batch lock's (`fkHalf`), handed to a snapshot's
observation at a commit, where the writer's contents are the committed data
(`backend.Snapshot`). -/
def fkdOwn (γ : BNames) (v : FkVals) : IProp GF := ghostVar γ.fkd (1 : Qp).half v

/-- **A half of the safe-range buckets' deleted entries** (`γ.dls`; the user's decision,
2026-11-04, probe M2): the entries `X` deleted from the safe-range buckets since the open (`dlR` of
the session's `dl`). One half is the client's (inside `fkOwn`: the compacting store's), the other
the batch lock's (`fkHalf`), handed to a snapshot's observation at a commit, where the logical
view but `X` is the committed data's safe-range part (`dlVd`, `backend.Snapshot`). -/
def dlsOwn (γ : BNames) (X : GMap (GoString × GoString) GoString) : IProp GF :=
  ghostVar γ.dls (1 : Qp).half X

/-- **The client's half of the compaction keys' flag alone** (mvcc's M3, 2026-11-06): what a reader
of the compaction keys needs (`fkRd_absF`, `fkRd_openF`), without the values' halves `fkOwn` also
holds, which a store keeps elsewhere (its tracked compaction). -/
def fkFlag (γ : BNames) (n : Nat) : IProp GF := monoNatAuthOwn γ.fk (1 : Qp).half n

/-- **The compaction keys' ghost value** (persistent; the M2 storage plan's merged ghost, items
27/29, 2026-10-30): the bit `g.1` (`fkV`) and, at the open, the flag's value `g.2.1` and the keys'
values `g.2.2` (`fkOpen`). -/
def fkVR (γ : BNames) (g : FkG) : IProp GF := dghostVar γ.fkv DFrac.discard g

/-- The batch lock's half of the flag, with what it and the ghost value say of its state
(`fkOkG`), and (2026-11-04) its half of the compaction keys' values at the writer's contents'. -/
def fkHalf (γ : BNames) (P : BParams) (st : BSess) : IProp GF :=
  iprop((∃ (f : Nat) (g : FkG), monoNatAuthOwn γ.fk (1 : Qp).half f ∗ fkVR γ g ∗ ⌜fkOkG P f g st⌝) ∗
    fkdOwn γ (fkVals st.S) ∗ dlsOwn γ (dlR P st.dl))

/-- A reader's lower bound of the flag, taken when its state `rv` was set, with the ghost value
(persistent). -/
def fkRd (γ : BNames) (P : BParams) (rv : RView) : IProp GF :=
  iprop(∃ (f : Nat) (g : FkG), monoNatLbOwn γ.fk f ∗ fkVR γ g ∗ ⌜fkOkRvG P f g rv⌝)

/-- **The batch lock's side of the tracked buckets** at contents `r`: the ghost map's authority,
the other halves of its elements (the shape of the client's `rbOwn`, so that a snapshot's
observation is handed one), and every tracked bucket of the table among its names (a session's
write goes to one). Sealed (`@[no_expose]`): its authority is what clears the pending flags, which
only `Unlock`'s proof may do (`rbSide_idle`, private to `TrackedLemmas.lean`, which
`batchTxBuffered__Unlock.lean` imports with `import all`); `TrackedLemmas.lean` and `NewAlloc.lean`
`import all` this module. By convention only: no gate checks the `import all`s yet. -/
@[no_expose] def rbSide (γ : BNames) (P : BParams) (r : GMap GoString BktData) : IProp GF :=
  iprop((∃ M : GMap GoString (Option BktData × Bool), ghostMapAuth γ.rbk 1 M) ∗ rbOwn γ r ∗
    ⌜∀ n i, P.BT.lookup n = some i → P.RB n = true → γ.rbD.lookup n ≠ none⌝)

/-- The batch lock's halves of what it tracks of the writer's contents `S`: the hook's own keys
(`γ.hkd`) and the tracked buckets (`rbSide`). -/
def trkHalf (γ : BNames) (P : BParams) (S : Data) : IProp GF :=
  iprop(ghostVar γ.hkd (1 : Qp).half (hkData P S) ∗ rbSide γ P (rbData P S))

/-! ## The history of the read side, and the cache's marks -/

/-- The read side's `i`-th state at version `ver` was `rv` (persistent). -/
def histAt (γ : BNames) (ver : w64) (i : Nat) (rv : RView) : IProp GF :=
  ghostMapElem γ.hist (ver, i) DFrac.discard rv

/-- The state `(ver, i)` was copied into the cache (persistent). -/
def cachedAt (γ : BNames) (ver : w64) (i : Nat) : IProp GF :=
  ghostMapElem γ.cached (ver, i) DFrac.discard true

/-- The state `(ver, i)` is an `Unlock`'s window: never copied into the cache (persistent). -/
def poisonAt (γ : BNames) (ver : w64) (i : Nat) : IProp GF :=
  ghostMapElem γ.cached (ver, i) DFrac.discard false

/-- The cache's marks (`true`: copied; `false`: a window, never copied): all at states up to
the current one `k` (`γ.cur`, its other half `readTx.mu`'s), the current one not a window's
unless the window is open (`win`); while it is, the clients' whole share of the view is here.
The clients' token's other half is always here. -/
def cacheInv (γ : BNames) : IProp GF :=
  iprop(inv (bN.@"cached") iprop(∃ (Cs : GMap (w64 × Nat) Bool) (k : w64 × Nat) (win : Bool),
    ghostMapAuth γ.cached 1 Cs ∗
    □ ([∗map] k' ↦ b ∈ Cs, ghostMapElem γ.cached k' DFrac.discard b) ∗
    ghostVar γ.cur (1 : Qp).half (k, win) ∗
    ghostVar γ.cvw (1 : Qp).half () ∗
    ⌜(∀ k' b, Cs.lookup k' = some b → keyLe k' k) ∧ (win = false → Cs.lookup k ≠ some false)⌝ ∗
    (⌜win = false⌝ ∨ ∃ vd, bView γ 1 vd)))

/-! ## `txMu` and the intervals -/

/-- `txMu`'s resource: the two exchange tokens at `q`. -/
def tmTok (γ : BNames) (q : Qp) : IProp GF := iprop(ghostVar γ.txa q () ∗ ghostVar γ.txb q ())

/-- What the buckets cache of an interval over `D` holds, by the table's ids: handles of `D`'s
buckets, or nil for a bucket `D` does not have. -/
def cmFacts (P : BParams) (rtx : Loc) (D : Data) (M : GMap w64 Loc) : IProp GF :=
  iprop([∗map] i ↦ bk ∈ M, ∃ n : GoString, ⌜P.BT.lookup n = some i⌝ ∗
    (⌜D.lookup n = none ∧ bk = Loc.null⌝ ∨
     ∃ m : BktData, ⌜D.lookup n = some m ∧ bk ≠ Loc.null⌝ ∗ rBkt rtx bk (bktEnts m)))

/-- A fraction `q` (a rational, `0` for none) of the buckets map `cm` holding `M`. -/
def mapPart (cm : GoMap) (q : Rat) (M : GMap w64 Loc) : IProp GF :=
  if h : 0 < q then iprop(cm ↦${DFrac.own ⟨q, h⟩} M) else iprop(True)

/-- A fraction `q` (a rational, `0` for none) of `txMu`'s first token. -/
def tokPart (γ : BNames) (q : Rat) : IProp GF :=
  if h : 0 < q then ghostVar γ.txa ⟨q, h⟩ () else iprop(True)

/-- An interval's buckets cache, exchanged against `txMu`'s first token (a fraction of the map
for the same fraction of the token: the invariant holds the map at `qm` and the token at
`1 - qm`), and its transaction's statistics against the whole second token. -/
def intvInv (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) : IProp GF :=
  iprop(inv (bN.@"intv") iprop(∃ (M : GMap w64 Loc) (qm : Rat), □ cmFacts P rtx D M ∗
      ⌜0 ≤ qm ∧ qm ≤ 1⌝ ∗ mapPart cm qm M ∗ tokPart γ (1 - qm)) ∗
    inv (bN.@"stats") iprop(rtxStats rtx ∨ ghostVar γ.txb 1 ()))

/-! ## The interval's `WaitGroup` -/

/-- The interval's `WaitGroup` is open to readers (fractional: `readTx.mu`'s resource holds it;
the commit that ends the interval deposits it whole). -/
def wgOpen (γw : GName) (q : Qp) : IProp GF := ghostVar γw q ()

/-- The interval's `WaitGroup` protocol (the invariant's body). Active: the counter is the
number of outstanding receipts (each reader also brought a budget token); the pool and the
receipts sum to half the transaction (the other half is `readTx.mu`'s while the interval is
current); open to readers, or closed (`wgOpen 1` inside: no reader adds any more; the commit
then holds the waiters' authority). Finished: the rollback goroutine's `Wait` found the counter
0 and took the pool, leaving its token `γt`. -/
def wgBody (γ : BNames) (rtx : Loc) (γwg : sync.WaitGroupNames) (γw γo γt : GName) : IProp GF :=
  iprop((∃ (n : w32) (outs : GMap Nat Qp) (pool : Qp),
      sync.ownWaitGroup γwg n ∗ ghostMapAuth γo 1 outs ∗ txLive rtx pool ∗
      ownToks γ.rdt (sint.nat n) ∗
      ⌜sint.Z n = (GMap.size outs : Int) ∧ (pool : Rat) + qsum outs = 1 / 2⌝ ∗
      (sync.ownWaitGroupWaiters γwg 0 ∨ wgOpen γw 1)) ∨
    (ghostMapAuth γo 1 (∅ : GMap Nat Qp) ∗ wgOpen γw 1 ∗ ghostVar γt 1 ()))

/-- The interval's `WaitGroup` and its protocol, with the readers' budget's authority. -/
def wgInv (γ : BNames) (rtx wg : Loc) (γw γo γt : GName) : IProp GF :=
  iprop(∃ γwg : sync.WaitGroupNames, sync.isWaitGroup wg γwg (bN.@"wg") ∗
    inv (bN.@"wgi") (wgBody γ rtx γwg γw γo γt) ∗ ownTokAuthDfrac γ.rdt DFrac.discard rdMax)

/-! ## `readTx.mu` -/

/-- **The deletable keys' registration** (persistent): the saved predicate `Φ` of
(bucket, key) pairs at the backend's name `γ.dlg`, fixed by the backend's creator, with the flag
`γ.dlb` at `true` (keys may be deletable). -/
def dlReg (γ : BNames) (Φ : GoString × GoString → IProp GF) : IProp GF :=
  iprop(savedPredOwn γ.dlg DFrac.discard Φ ∗ dghostVar γ.dlb DFrac.discard true)

/-- **Nothing is deletable** (persistent; O1's fallback): the creator fixed the backend's
deletable-keys flag at `false` (a backend whose creator registered nothing as deletable: the old
bridge's, D22's restore over a new backend). Not `mvcc.bkNoCmp`, which says the backend's data
records no compaction (no compaction keys in `meta`): a fact about the data at opening, for
`restore`. Rules out every deletable key with no later (`dlNoDel_noDel`). -/
def dlNoDel (γ : BNames) : IProp GF := dghostVar γ.dlb DFrac.discard false

/-- **The key `nk` (bucket, key) is deletable** (persistent): the registered predicate holds of it. -/
def dlIs (γ : BNames) (nk : GoString × GoString) : IProp GF :=
  iprop(∃ Φ : GoString × GoString → IProp GF, dlReg γ Φ ∗ □ Φ nk)

/-- **A physical view thin of the logical view `L`** (persistent): every entry of the physical
view `vd` is `L`'s, and an entry of `L` missing from `vd` is a deletable key. -/
def thinV (γ : BNames) (vd L : VData) : IProp GF :=
  iprop(⌜∀ nk v, vd.lookup nk = some v → L.lookup nk = some v⌝ ∗
    □ ∀ nk, ⌜L.lookup nk ≠ none ∧ vd.lookup nk = none⌝ -∗ dlIs γ nk)

/-- **A cached read buffer reads thin of the logical view** (3.2; Draft): the cached copies of the states up to `idx` at the current version read thin of the
logical view `L` (until the stage: "exactly as the current state"; now (a tombstone put and compacted within one commit interval: a
reader of the cached buffer may still see the deleted key, which it never looks up). -/
def cacheValid (γ : BNames) (P : BParams) (rv : RView) (idx : Nat) (L : VData) :
    IProp GF :=
  iprop(□ ∀ (i : Nat) (rv' : RView), ⌜i ≤ idx⌝ -∗ histAt γ rv.2.ver i rv' -∗
    cachedAt γ rv.2.ver i -∗ thinV γ (vData P (rv.1, rv'.2)) L)

/-- **A quarter of the readers' view, over the logical view** (the thin-view Draft round): the
ghost share at the logical view `L` the clients hold, and the physical view `phys` thin of it
(`thinV`). Until the stage the share held the physical view itself; an exact holder is the instance
`L = phys` (`viewQ_exact`). -/
def viewQ (γ : BNames) (q : Qp) (phys L : VData) : IProp GF :=
  iprop(ghostVar γ.view q L ∗ thinV γ phys L)

/-- The read buffer's buffers are writable (a free slot each). -/
def bksOk (Pb : BksPhys) (B : GMap w64 (List Ent)) : Prop :=
  ∀ id x es, Pb.lookup id = some x → B.lookup id = some es → bbOk x.2 es

/-- The interval's resources at `q`: open (a bbolt read transaction over `D`, its invariants,
`wgOpen` at `q`), or the backend stopped. -/
def rtIntv (γ : BNames) (P : BParams) (q : Qp) (rd : RdSt) (cm : GoMap) (D : Data)
    (p : Qp := q.half) : IProp GF :=
  if rd.live then
    iprop(txLive rd.rtx p ∗ rtxSnap rd.rtx D ∗ □ intvInv γ P rd.rtx cm D ∗
      □ wgInv γ rd.rtx rd.wg rd.γw rd.γo rd.γt ∗ wgOpen rd.γw q ∗ ghostVar rd.γt q ())
  else iprop(⌜rd.rtx = Loc.null⌝ ∗ bStopped γ)

/-- `readTx.mu`'s share `q` of the read buffer's clean flag (`γ.cln`, at the layout's `rd.cln`),
and what the flag promises: the read buffer clean off the hook's buckets (the restore plan's
R5a). -/
def clnPart (γ : BNames) (P : BParams) (q : Qp) (rd : RdSt) (rv : RView) : IProp GF :=
  iprop(ghostVar γ.cln q.half rd.cln ∗ ⌜rd.cln = true → rbClean P rv.2⌝)

/-- `readTx.mu`'s resource at `q` but the read buffer, the buckets map's field and the view's
quarter, in the layout `rd`, the readers' state `rv`, the buckets map `cm` and the history `H`:
the ghost variables' shares (the layout, the state
and window agreed with the batch lock (`γ.rvs`), the current state's key and window agreed with
`cacheInv` (`γ.cur`)), the history's authority, the shared transaction's fields, the facts (the
read buffer canonical, of the table's buckets and writable; the current state the latest of
the history; a window only at a version's first state), the cache's validity, the window's
poison mark, the readers' budget's authority, the interval, and a lower bound of the compaction
keys' flag taken when `rv` was set (`fkRd`: set wherever `rv` changes, at the constructor, the
`Unlock`'s write-back (`wb_core`) and the commit (`rtRes_cm_close`); `CommitAndStop` commits
through `batchTxBuffered.commit` and `unsafeCommit`, so its stop branch of `rtRes_cm_close` sets it
too; the backend-compaction stage, 2026-10-29). -/
def rtCore (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) (rd : RdSt) (rv : RView)
    (cm : GoMap) (H : GMap (w64 × Nat) RView) (p : Qp := q.half) (L : VData := vData P rv) :
    IProp GF :=
  iprop(ghostVar γ.rd q rd ∗
    ghostVar γ.rvs q.half (rv, rd.win) ∗ ghostVar γ.cur q.half ((rv.2.ver, rd.idx), rd.win) ∗
    clnPart γ P q rd rv ∗
    ghostMapAuth γ.hist q H ∗
    rtxOf (baseOf rt) ↦{DFrac.own q} rd.rtx ∗ rwgOf (baseOf rt) ↦{DFrac.own q} rd.wg ∗
    ⌜rv.2.Wf ∧ idsOk P rv.2.bks ∧ H.lookup (rv.2.ver, rd.idx) = some rv ∧
      (∀ k rv', H.lookup k = some rv' → keyLe k (rv.2.ver, rd.idx)) ∧
      (rd.win = true → rd.idx = 0) ∧ safeRv P rv⌝ ∗
    histAt γ rv.2.ver rd.idx rv ∗ cacheValid γ P rv rd.idx L ∗
    (if rd.win then poisonAt γ rv.2.ver rd.idx else iprop(True)) ∗
    ownTokAuthDfrac γ.rdt DFrac.discard rdMax ∗ rtIntv γ P q rd cm rv.1 p ∗ fkRd γ P rv)

/-- `rtCore` with the view's quarter (at `q`), over the logical view `L` (the physical state's
view `vData P rv` thin of it: `viewQ`; exact by default). -/
def rtRest (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) (rd : RdSt) (rv : RView)
    (cm : GoMap) (H : GMap (w64 × Nat) RView) (p : Qp := q.half) (L : VData := vData P rv) :
    IProp GF :=
  iprop(viewQ γ q.half.half (vData P rv) L ∗ rtCore γ P rt q rd rv cm H p L)

/-- `readTx.mu`'s resource at `q`, in the layout `rd`, the readers' state `rv` and the history
`H`: the read buffer at `q` (writable buffers), the buckets map's field, and the rest. -/
def rtResAt (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) (rd : RdSt) (rv : RView)
    (H : GMap (w64 × Nat) RView) (p : Qp := q.half) (L : VData := vData P rv) : IProp GF :=
  iprop(∃ (m : GoMap) (Pb : BksPhys) (cm : GoMap),
    rbAt (rbufOf (baseOf rt)) (DFrac.own q) m Pb rv.2 ∗ ⌜bksOk Pb rv.2.bks⌝ ∗
    rbktOf (baseOf rt) ↦{DFrac.own q} cm ∗ rtRest γ P rt q rd rv cm H p L)

/-- `readTx.mu`'s resource at `q`. -/
def rtRes (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (rd : RdSt) (rv : RView) (H : GMap (w64 × Nat) RView) (L : VData),
    rtResAt γ P rt q rd rv H q.half L)

/-! ## The cache -/

/-- A cached copy at `bp` (persistent: readers share it; its version field 0, as `unsafeCopy`
makes it), marked as the state `(ver, i)` it copied. -/
def cacheEnt (γ : BNames) (P : BParams) (bp : Loc) (ver : w64) : IProp GF :=
  iprop(∃ (c : txReadBuffer) (Pc : BksPhys) (i : Nat) (rv : RView),
    bp ↦□ c ∗ bksAt c.txBuffer'.buckets' DFrac.discard Pc rv.2.bks ∗
    histAt γ ver i rv ∗ cachedAt γ ver i ∗ ⌜rv.2.Wf ∧ idsOk P rv.2.bks ∧ c.bufVersion' = W64 0⌝)

/-- `txReadBufferCache.mu`'s resource: the cache's fields, its copy if any. -/
def cacheRes (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ (bp : Loc) (ver : w64), cbufOf b ↦ bp ∗ cverOf b ↦ ver ∗
    (⌜bp = Loc.null⌝ ∨ cacheEnt γ P bp ver))

/-! ## The stopped batch transaction -/

/-! ## The batch transaction -/

/-- The batch transaction's physical state for `st`: its fields, the write buffer, the
post-lock hook's field, bbolt's database and its write transaction `st.tx`, and a reader's slot
of `b.mu` (`begin` reads `b.db` under it). -/
def batchPhys (γ : BNames) (b t db : Loc) (st : BSess) : IProp GF :=
  iprop(∃ hk : GoFunc,
    txFOf t ↦ st.tx ∗ pendOf t ↦ st.pend ∗ delOf t ↦ st.ndel ∗ ownWB (wbOf t) st.W ∗
    bF go!"txPostLockInsideApplyHook" b ↦ hk ∗ dghostVar γ.hook (DFrac.own (1 : Qp).half) hk ∗
    ownDB db γ.db st.C ∗ ownWTx st.tx γ.db st.C st.S ∗ txDB st.tx db ∗
    sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
    -- (2026-11-04, R2b-3c) the database the backend's (its stop gives it to `Close`)
    bDB γ db)

/-- **The batch lock's quarter of the readers' view, over the logical view** (question 2, option (a),
2026-10-29; until then the quarter at the physical view `vData P (st.C, st.R)` itself): some logical
view `L`, the physical view thin of it (`viewQ`). Exact is the instance `L = vData P (st.C, st.R)`
(`batchViewQ_of_exact`). -/
def batchViewQ (γ : BNames) (P : BParams) (st : BSess) : IProp GF :=
  iprop(∃ L : VData, viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) L ∗ ⌜dlsW P st L⌝)

/-- The batch lock's share of the ghost state for `st`: the view's quarter over the logical view,
the physical view `(C, R)` thin of it (`batchViewQ`), half of
the readers' state `γ.rvs` at `(C, R)` (so the batch side's `C` and `R` are the read side's),
with no `Unlock` window open (an `Unlock`'s commit closes it for its hook's run), the write-back budget's authority (`n` tokens out), the count of write-backs
`w` (monotone) and half of `γ.used` (the `run` goroutine has the other half), a quarter of the
open token (the `run` goroutine has another quarter, the clients' `bOpen` the half: so the
batch lock is never held in a stopped backend), half of the hook's own keys `γ.hkd` and of the
tracked buckets `γ.rbk` at the writer's contents (`trkHalf`), half the compaction keys' flag, at
`0` only while the state has none (`fkHalf`, the backend-compaction stage, 2026-10-29), with the
bounds of `bgOk` over the state's counters (`free`: the lock is free). -/
def batchGhostAt (γ : BNames) (P : BParams) (st : BSess) (free : Bool) : IProp GF :=
  iprop(batchViewQ γ P st ∗
    ∃ (n w u : Nat), ghostVar γ.rvs (1 : Qp).half (((st.C, st.R) : RView), false) ∗
      ownTokAuth γ.wb n ∗
      monoNatAuthOwn γ.wbc 1 w ∗ ghostVar γ.used (1 : Qp).half u ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      trkHalf γ P st.S ∗ fkHalf γ P st ∗ ⌜bgOk P st free n w u⌝)

/-- The batch lock's ghost share, held. -/
abbrev batchGhost (γ : BNames) (P : BParams) (st : BSess) : IProp GF := batchGhostAt γ P st false

/-- The batch lock's resource, free: a state with `freeOk` and the client's resources `W` (the
lock holder's: an `Unlock` that changes the view gets it back with the new view) and `Pk` (the
hooks': the pre-commit hook and the post-lock hook run with it); or the backend stopped (the `run`
goroutine's `CommitAndStop`: the open token whole inside). -/
def batchFree (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) : IProp GF :=
  iprop((∃ (st : BSess) (db : Loc), batchPhys γ b t db st ∗ batchGhostAt γ P st true ∗ ⌜freeOk P st⌝ ∗
    W ∗ Pk) ∨
    bStopped γ)

/-- The batch lock held, in state `st` (its transaction `t`, its database `db`). -/
def batchLockedAt (γ : BNames) (P : BParams) (b t db : Loc) (st : BSess) : IProp GF :=
  iprop(sync.ownMutex (muOf t) ∗ batchPhys γ b t db st ∗ batchGhost γ P st ∗ ⌜sessWf P st⌝)

/-- The batch lock held by the client, in state `st`. -/
def batchLocked (γ : BNames) (P : BParams) (b : Loc) (st : BSess) : IProp GF :=
  iprop(∃ (t db : Loc), bF go!"batchTx" b ↦□ t ∗ batchLockedAt γ P b t db st)

/-- What a commit (`unsafeCommit`) needs besides the batch lock: at a stop, the rest of the open
token (the clients' half, which `run` got from `Close`, and the `run` goroutine's quarter); otherwise a payment for the hook's
leftovers it keeps in the write buffer: a write-back's token (`m = 0`: `Commit`), the `run`
goroutine's unpaid commit (`m = 1`: its half of `γ.used` at `u`, and a write-back since: `u + 1`
of them), or none right after a write-back (`m ≥ 2`: `c = 0`, `Unlock`; D22 receiver epochs, S8a,
2026-10-24: with the write-back's lower bound). The hooks see it (`hooksSpec`): every commit that
runs them is paid by something a fresh backend's creator holds (`hook_fresh_false`). -/
def payIn (γ : BNames) (st : BSess) (stop : Bool) (m u : Nat) : IProp GF :=
  if stop then iprop(dghostVar γ.opn (DFrac.own (1 : Qp).half) false ∗
    dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false)
  else if m = 0 then wbTok γ
  else if m = 1 then iprop(ghostVar γ.used (1 : Qp).half u ∗ monoNatLbOwn γ.wbc (u + 1))
  else iprop(⌜st.cnt.c = 0⌝ ∗ monoNatLbOwn γ.wbc 1)

/-- A `Hooks` value: nil, or one whose `OnPreCommitUnsafe(tx)`, on the batch transaction `t`
held in a state `st` in the hook's window (`hookPre`: room for its operations), with the hooks'
resource `Pk`, makes a hook step (`hookStep`). (D22 receiver epochs, S8a, 2026-10-24) The hook
sees the commit's payment (`payIn`, given back): every commit that runs the hooks is paid by a
write-back token, the `run` goroutine's write-back, or the open token at a stop, so a hook can
rule out running on a backend whose creator still holds them all (`hook_fresh_false`). -/
def hooksSpec (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc) (h : GoInterface) :
    IProp GF :=
  iprop(⌜h = GoInterface.nil⌝ ∨ ∃ ho : GoInterfaceOk, ⌜h = GoInterface.ok ho⌝ ∗
    □ ∀ (st : BSess) (stop : Bool) (m u : Nat),
      {{ batchLocked γ P b st ∗ Pk ∗ ⌜hookPre P st⌝ ∗ payIn γ st stop m u }}
        (App (Val #(methods ho.ty go!"OnPreCommitUnsafe" ho.v))
          (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
      {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ payIn γ st stop m u ∗
          ⌜hookStep P st st'⌝ }})

/-- **A committer's request served by the hooks** (D22 the stored-index window, 2026-10-23;
`notes/decisions.md`, "D22 the stored-index window carried out"): the hooks `h`' contract
(`hooksSpec`) with a frame the hook transforms: given the committer's `X` besides the hooks'
resource, `OnPreCommitUnsafe(t)` makes a hook step and gives back `Y`. For the server's hooks,
the apply thread's state traded for the stored index's window at the consistent index's save. -/
def hooksReq (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc) (h : GoInterface)
    (X Y : IProp GF) : IProp GF :=
  iprop(∃ ho : GoInterfaceOk, ⌜h = GoInterface.ok ho⌝ ∗
    □ ∀ (st : BSess) (stop : Bool) (m u : Nat),
      {{ batchLocked γ P b st ∗ Pk ∗ X ∗ ⌜hookPre P st⌝ ∗ payIn γ st stop m u }}
        (App (Val #(methods ho.ty go!"OnPreCommitUnsafe" ho.v))
          (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
      {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ Y ∗ payIn γ st stop m u ∗
          ⌜hookStep P st st'⌝ }})

/-- **A commit's request** `X ⇒ Y` (D22 the stored-index window, 2026-10-23): a plain wand (the
commit only passes `X` along), or a request the backend's hooks serve (`hooksReq`; a commit runs
its hook exactly once, `batchTxBuffered.unsafeCommit`). -/
def commitReq (γ : BNames) (P : BParams) (Pk : IProp GF) (b : Loc) (X Y : IProp GF) :
    IProp GF :=
  iprop(□ (X -∗ Y) ∨ ∃ (t : Loc) (h : GoInterface), bF go!"batchTx" b ↦□ t ∗
    bF go!"hooks" b ↦□ h ∗ hooksReq γ P Pk b t h X Y)

/-- The backend's metrics fields (atomics). -/
def metricsInv (b : Loc) : IProp GF :=
  iprop(inv (bN.@"metrics") iprop(∃ (a c d e : w64), bF go!"size" b ↦ a ∗
    bF go!"sizeInUse" b ↦ c ∗ bF go!"commits" b ↦ d ∗ bF go!"openReadTxN" b ↦ e))

/-- `b` is a backend with parameters `P`, ghost names `γ`, the client's batch-lock resources
`W` (the lock holder's) and `Pk` (the hooks') (persistent). (Sweep repairs 1, B4, 2026-11-07) With
`ETCD_VERIFY` off (`envVerifyOff`): what its batch transaction's lock checks
(`ValidateCalledInsideApply` and the others) take; from the opener's precondition. -/
def isBackend (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) : IProp GF :=
  iprop(□ ∃ (t rt tm db lg : Loc) (h : GoInterface),
    bF go!"batchTx" b ↦□ t ∗ bF go!"readTx" b ↦□ rt ∗ bF go!"batchLimit" b ↦□ P.limit ∗
    bF go!"lg" b ↦□ lg ∗ zapLoggerOk lg ∗ bF go!"hooks" b ↦□ h ∗ beOf t ↦□ b ∗
    rtmuOf (baseOf rt) ↦□ tm ∗ hooksSpec γ P Pk b t h ∗
    sync.isMutex (muOf t) (batchFree γ P W Pk b t) ∗
    sync.isRWMutexGuard (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    sync.isRWMutexGuard tm (fun q => tmTok γ q) ∗
    sync.isMutex (cmuOf b) (cacheRes γ P b) ∗ cacheInv γ ∗ metricsInv b ∗
    sync.isRWMutexGuard (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
    isDB db ∗ ⌜P.Wf⌝ ∗
    -- (2026-11-04, R2b-3c) the database and its file
    (∃ path : GoString, bDBAt γ db path ∗ dbFile db path) ∗
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off
    envVerifyOff)

/-! ## Readers -/

/-- A reader's tokens, beside `readTx.mu`'s slot: a slot of `txMu` and a reader's budget
token (a `ConcurrentReadTx` keeps them until its `RUnlock`). -/
def crTok (γ : BNames) (b : Loc) : IProp GF :=
  iprop(∃ (rt tm : Loc), bF go!"readTx" b ↦□ rt ∗ rtmuOf (baseOf rt) ↦□ tm ∗
    sync.ownRWMutex tm (fun q => tmTok γ q) ∗ ownToks γ.rdt 1)

/-- A reader's token: a slot of `readTx.mu`, and `crTok`. -/
def rdTok (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ rt : Loc, bF go!"readTx" b ↦□ rt ∗ sync.ownRWMutex (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    crTok γ b)

end preds

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The open share a reader's token carries** (D22 receiver epochs, S8d, W7, 2026-10-25; the
orchestrator's decision: the shares counted): half of the open token divided among the backend's
`nReaders` reader slots (`newPost`'s `rdTok`s), the other half the constructors' remainder. With
every reader's token and the remainder back, the whole open token is reassembled
(`bOpen_one_shares`), which the old backend's `Close` needs (`applySnapshot`). -/
def rdOpen : Qp :=
  Qp.divide_even (1 : Qp).half (Int.toNat sync.rwmutex.actualMaxReaders)
    (by have := sync.actualMaxReaders_ge_2; omega)

end shares

end backend
end EtcdGrove
end Perennial
