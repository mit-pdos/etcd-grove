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
- `γ.hook`: the post-lock hook, half the client's (`plHook γ f`), half the batch lock's;
  `γ.opn`: the backend open, half the clients' (`bOpen γ q`), half the `run` goroutine's;
  `γ.wb`: the write-back budget (`wbTok γ`: an `Unlock` may increment the read buffer's version,
  a `uint64`, whose wrap-around would make a stale cache look current); `γ.rdt`: the readers'
  budget (`rdTok` holds one: `txWg`'s counter is an `int32`).

**The locks.**
- *The batch lock* (`batchTx.Mutex`, `batchFree`): the batch transaction's state for a `BSess`
  (`batchPhys`), the view's quarter at `(C, R)`, `freeOk`, and the write-back budget's authority
  (the version plus the tokens left below `2^64`).
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
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Proof.TokSet
public import Perennial.Proof.sync

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

section phys
variable [FfiSyntax]

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

instance kv_countable : Pos.Countable kv :=
  countableOfLeftInverse (fun x : kv => (x.key', x.val')) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance bbPhys_countable : Pos.Countable BBPhys :=
  countableOfLeftInverse (fun x : BBPhys => (x.buf, x.kvs)) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance rdSt_countable : Pos.Countable RdSt :=
  countableOfLeftInverse
    (fun x : RdSt => (x.rtx, x.wg, x.γw, x.γo, x.γt, x.idx, x.win, x.live))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩)
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
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev bF (f : GoString) (b : Loc) : Loc := structFieldRef backend f b
abbrev btOf (t : Loc) : Loc := structFieldRef batchTxBuffered go!"batchTx" t
abbrev muOf (t : Loc) : Loc := structFieldRef batchTx go!"Mutex" (btOf t)
abbrev txFOf (t : Loc) : Loc := structFieldRef batchTx go!"tx" (btOf t)
abbrev pendOf (t : Loc) : Loc := structFieldRef batchTx go!"pending" (btOf t)
abbrev beOf (t : Loc) : Loc := structFieldRef batchTx go!"backend" (btOf t)
abbrev wbOf (t : Loc) : Loc := structFieldRef batchTxBuffered go!"buf" t
abbrev delOf (t : Loc) : Loc := structFieldRef batchTxBuffered go!"pendingDeleteOperations" t
abbrev baseOf (rt : Loc) : Loc := structFieldRef readTx go!"baseReadTx" rt
abbrev cbaseOf (rt : Loc) : Loc := structFieldRef concurrentReadTx go!"baseReadTx" rt
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

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
def bView (γ : BNames) (q : Qp) (vd : VData) : IProp GF :=
  iprop(ghostVar γ.view q.half vd ∗ ghostVar γ.cvw q.half ())

instance bView_timeless (γ : BNames) (q : Qp) (vd : VData) : Timeless (bView (GF := GF) γ q vd) := by
  unfold bView; infer_instance

/-- The clients' share of the backend being open (`γ.opn`, a `dghostVar` of whether it
stopped: half of it the clients', a quarter the `run` goroutine's, a quarter the batch lock's;
the stop makes it `true` and persistent), and of the right to close it (`γ.cls`: `Close`, with all
of it, closes `stopc` once). -/
def bOpen (γ : BNames) (q : Qp) : IProp GF :=
  iprop(dghostVar γ.opn (DFrac.own q.half) false ∗ ghostVar γ.cls q ())

/-- The backend stopped (persistent). -/
def bStopped (γ : BNames) : IProp GF := dghostVar γ.opn DFrac.discard true

instance bStopped_persistent (γ : BNames) : Persistent (bStopped (GF := GF) γ) := by
  unfold bStopped; infer_instance

/-- The clients' half of the post-lock hook (`SetTxPostLockInsideApplyHook` changes it). -/
def plHook (γ : BNames) (f : GoFunc) : IProp GF := ghostVar γ.hook (1 : Qp).half f

/-- One write-back's budget (an `Unlock` costs one). -/
def wbTok (γ : BNames) : IProp GF := ownToks γ.wb 1

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

instance histAt_persistent (γ : BNames) (ver : w64) (i : Nat) (rv : RView) :
    Persistent (histAt (GF := GF) γ ver i rv) := by
  unfold histAt; infer_instance

instance cachedAt_persistent (γ : BNames) (ver : w64) (i : Nat) :
    Persistent (cachedAt (GF := GF) γ ver i) := by
  unfold cachedAt; infer_instance

instance poisonAt_persistent (γ : BNames) (ver : w64) (i : Nat) :
    Persistent (poisonAt (GF := GF) γ ver i) := by
  unfold poisonAt; infer_instance

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

instance cacheInv_persistent (γ : BNames) : Persistent (cacheInv (GF := GF) γ) := by
  unfold cacheInv; infer_instance

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

instance cmFacts_timeless (P : BParams) (rtx : Loc) (D : Data) (M : GMap w64 Loc) :
    Timeless (cmFacts (GF := GF) P rtx D M) := by
  unfold cmFacts; infer_instance

instance cmFacts_persistent (P : BParams) (rtx : Loc) (D : Data) (M : GMap w64 Loc) :
    Persistent (cmFacts (GF := GF) P rtx D M) := by
  unfold cmFacts; infer_instance

instance mapPart_timeless (cm : GoMap) (q : Rat) (M : GMap w64 Loc) :
    Timeless (mapPart (GF := GF) cm q M) := by
  unfold mapPart; split <;> infer_instance

instance tokPart_timeless (γ : BNames) (q : Rat) : Timeless (tokPart (GF := GF) γ q) := by
  unfold tokPart; split <;> infer_instance

/-- An interval's buckets cache, exchanged against `txMu`'s first token (a fraction of the map
for the same fraction of the token: the invariant holds the map at `qm` and the token at
`1 - qm`), and its transaction's statistics against the whole second token. -/
def intvInv (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) : IProp GF :=
  iprop(inv (bN.@"intv") iprop(∃ (M : GMap w64 Loc) (qm : Rat), □ cmFacts P rtx D M ∗
      ⌜0 ≤ qm ∧ qm ≤ 1⌝ ∗ mapPart cm qm M ∗ tokPart γ (1 - qm)) ∗
    inv (bN.@"stats") iprop(rtxStats rtx ∨ ghostVar γ.txb 1 ()))

instance intvInv_persistent (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) :
    Persistent (intvInv (GF := GF) γ P rtx cm D) := by
  unfold intvInv; infer_instance

/-! ## The interval's `WaitGroup` -/

/-- The interval's `WaitGroup` is open to readers (fractional: `readTx.mu`'s resource holds it;
the commit that ends the interval deposits it whole). -/
def wgOpen (γw : GName) (q : Qp) : IProp GF := ghostVar γw q ()

/-- A reader's share of the interval: its fraction of the transaction's `txLive`, and its
receipt. -/
def rdShare (rtx : Loc) (γo : GName) (k : Nat) (q : Qp) : IProp GF :=
  iprop(txLive rtx q ∗ ghostMapElem γo k (DFrac.own 1) q)

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

instance wgBody_timeless (γ : BNames) (rtx : Loc) (γwg : sync.WaitGroupNames)
    (γw γo γt : GName) : Timeless (wgBody (GF := GF) γ rtx γwg γw γo γt) := by
  unfold wgBody wgOpen; infer_instance

/-- The interval's `WaitGroup` and its protocol, with the readers' budget's authority. -/
def wgInv (γ : BNames) (rtx wg : Loc) (γw γo γt : GName) : IProp GF :=
  iprop(∃ γwg : sync.WaitGroupNames, sync.isWaitGroup wg γwg (bN.@"wg") ∗
    inv (bN.@"wgi") (wgBody γ rtx γwg γw γo γt) ∗ ownTokAuthDfrac γ.rdt DFrac.discard rdMax)

instance wgInv_persistent (γ : BNames) (rtx wg : Loc) (γw γo γt : GName) :
    Persistent (wgInv (GF := GF) γ rtx wg γw γo γt) := by
  unfold wgInv; infer_instance

/-! ## `readTx.mu` -/

/-- The cached copies of the states up to `idx` at the current version read as the current
state, off the hook's buckets, over the current committed data. -/
def cacheValid (γ : BNames) (P : BParams) (rv : RView) (idx : Nat) : IProp GF :=
  iprop(□ ∀ (i : Nat) (rv' : RView), ⌜i ≤ idx⌝ -∗ histAt γ rv.2.ver i rv' -∗
    cachedAt γ rv.2.ver i -∗ ⌜vData P (rv.1, rv'.2) = vData P rv⌝)

instance cacheValid_persistent (γ : BNames) (P : BParams) (rv : RView) (idx : Nat) :
    Persistent (cacheValid (GF := GF) γ P rv idx) := by
  unfold cacheValid; infer_instance

/-- The read buffer's buffers are writable (a free slot each). -/
def bksOk (Pb : BksPhys) (B : GMap w64 (List Ent)) : Prop :=
  ∀ id x es, Pb.lookup id = some x → B.lookup id = some es → bbOk x.2 es

/-- The interval's resources at `q`: open (a bbolt read transaction over `D`, its invariants,
`wgOpen` at `q`), or the backend stopped. -/
def rtIntv (γ : BNames) (P : BParams) (q : Qp) (rd : RdSt) (cm : GoMap) (D : Data) : IProp GF :=
  if rd.live then
    iprop(txLive rd.rtx q.half ∗ rtxSnap rd.rtx D ∗ □ intvInv γ P rd.rtx cm D ∗
      □ wgInv γ rd.rtx rd.wg rd.γw rd.γo rd.γt ∗ wgOpen rd.γw q ∗ ghostVar rd.γt q ())
  else iprop(⌜rd.rtx = Loc.null⌝ ∗ bStopped γ)

/-- `readTx.mu`'s resource at `q` but the read buffer, the buckets map's field and the view's
quarter, in the layout `rd`, the readers' state `rv`, the buckets map `cm` and the history `H`:
the ghost variables' shares (the layout, the state
and window agreed with the batch lock (`γ.rvs`), the current state's key and window agreed with
`cacheInv` (`γ.cur`)), the history's authority, the shared transaction's fields, the facts (the
read buffer canonical, of the table's buckets and writable; the current state the latest of
the history; a window only at a version's first state), the cache's validity, the window's
poison mark, the readers' budget's authority, and the interval. -/
def rtCore (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) (rd : RdSt) (rv : RView)
    (cm : GoMap) (H : GMap (w64 × Nat) RView) : IProp GF :=
  iprop(ghostVar γ.rd q rd ∗
    ghostVar γ.rvs q.half (rv, rd.win) ∗ ghostVar γ.cur q.half ((rv.2.ver, rd.idx), rd.win) ∗
    ghostMapAuth γ.hist q H ∗
    rtxOf (baseOf rt) ↦{DFrac.own q} rd.rtx ∗ rwgOf (baseOf rt) ↦{DFrac.own q} rd.wg ∗
    ⌜rv.2.Wf ∧ idsOk P rv.2.bks ∧ H.lookup (rv.2.ver, rd.idx) = some rv ∧
      (∀ k rv', H.lookup k = some rv' → keyLe k (rv.2.ver, rd.idx)) ∧
      (rd.win = true → rd.idx = 0)⌝ ∗
    histAt γ rv.2.ver rd.idx rv ∗ cacheValid γ P rv rd.idx ∗
    (if rd.win then poisonAt γ rv.2.ver rd.idx else iprop(True)) ∗
    ownTokAuthDfrac γ.rdt DFrac.discard rdMax ∗ rtIntv γ P q rd cm rv.1)

/-- `rtCore` with the view's quarter (at `q`). -/
def rtRest (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) (rd : RdSt) (rv : RView)
    (cm : GoMap) (H : GMap (w64 × Nat) RView) : IProp GF :=
  iprop(ghostVar γ.view q.half.half (vData P rv) ∗ rtCore γ P rt q rd rv cm H)

/-- `readTx.mu`'s resource at `q`, in the layout `rd`, the readers' state `rv` and the history
`H`: the read buffer at `q` (writable buffers), the buckets map's field, and the rest. -/
def rtResAt (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) (rd : RdSt) (rv : RView)
    (H : GMap (w64 × Nat) RView) : IProp GF :=
  iprop(∃ (m : GoMap) (Pb : BksPhys) (cm : GoMap),
    rbAt (rbufOf (baseOf rt)) (DFrac.own q) m Pb rv.2 ∗ ⌜bksOk Pb rv.2.bks⌝ ∗
    rbktOf (baseOf rt) ↦{DFrac.own q} cm ∗ rtRest γ P rt q rd rv cm H)

/-- `readTx.mu`'s resource at `q`. -/
def rtRes (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (rd : RdSt) (rv : RView) (H : GMap (w64 × Nat) RView), rtResAt γ P rt q rd rv H)


/-! ## The cache -/

/-- A cached copy at `bp` (persistent: readers share it; its version field 0, as `unsafeCopy`
makes it), marked as the state `(ver, i)` it copied. -/
def cacheEnt (γ : BNames) (P : BParams) (bp : Loc) (ver : w64) : IProp GF :=
  iprop(∃ (c : txReadBuffer) (Pc : BksPhys) (i : Nat) (rv : RView),
    bp ↦□ c ∗ bksAt c.txBuffer'.buckets' DFrac.discard Pc rv.2.bks ∗
    histAt γ ver i rv ∗ cachedAt γ ver i ∗ ⌜rv.2.Wf ∧ idsOk P rv.2.bks ∧ c.bufVersion' = W64 0⌝)

instance bbAt_discard_persistent (bb : Loc) (p : BBPhys) (es : List Ent) :
    Persistent (bbAt (GF := GF) bb DFrac.discard p es) := by
  unfold bbAt; infer_instance

instance bksAt_discard_persistent (m : GoMap) (Pb : BksPhys) (B : GMap w64 (List Ent)) :
    Persistent (bksAt (GF := GF) m DFrac.discard Pb B) := by
  unfold bksAt; infer_instance

instance cacheEnt_persistent (γ : BNames) (P : BParams) (bp : Loc) (ver : w64) :
    Persistent (cacheEnt (GF := GF) γ P bp ver) := by
  unfold cacheEnt; infer_instance

/-- `txReadBufferCache.mu`'s resource: the cache's fields, its copy if any. -/
def cacheRes (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ (bp : Loc) (ver : w64), cbufOf b ↦ bp ∗ cverOf b ↦ ver ∗
    (⌜bp = Loc.null⌝ ∨ cacheEnt γ P bp ver))

/-! ## The batch transaction -/

/-- The batch transaction's physical state for `st`: its fields, the write buffer, the
post-lock hook's field, bbolt's database and its write transaction `st.tx`, and a reader's slot
of `b.mu` (`begin` reads `b.db` under it). -/
def batchPhys (γ : BNames) (b t db : Loc) (st : BSess) : IProp GF :=
  iprop(∃ hk : GoFunc,
    txFOf t ↦ st.tx ∗ pendOf t ↦ st.pend ∗ delOf t ↦ st.ndel ∗ ownWB (wbOf t) st.W ∗
    bF go!"txPostLockInsideApplyHook" b ↦ hk ∗ ghostVar γ.hook (1 : Qp).half hk ∗
    ownDB db γ.db st.C ∗ ownWTx st.tx γ.db st.C st.S ∗ txDB st.tx db ∗
    sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db))

/-- The batch lock's share of the ghost state for `st`: the view's quarter at `(C, R)`, half of
the readers' state `γ.rvs` at `(C, R)` (so the batch side's `C` and `R` are the read side's),
with no `Unlock` window open (an `Unlock`'s commit closes it for its hook's run), the write-back budget's authority (`n` tokens out), the count of write-backs
`w` (monotone) and half of `γ.used` (the `run` goroutine has the other half), a quarter of the
open token (the `run` goroutine has another quarter, the clients' `bOpen` the half: so the
batch lock is never held in a stopped backend), with the bounds of `bgOk` over the state's
counters (`free`: the lock is free). -/
def batchGhostAt (γ : BNames) (P : BParams) (st : BSess) (free : Bool) : IProp GF :=
  iprop(ghostVar γ.view (1 : Qp).half.half (vData P (st.C, st.R)) ∗
    ∃ (n w u : Nat), ghostVar γ.rvs (1 : Qp).half (((st.C, st.R) : RView), false) ∗
      ownTokAuth γ.wb n ∗
      monoNatAuthOwn γ.wbc 1 w ∗ ghostVar γ.used (1 : Qp).half u ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ ⌜bgOk P st free n w u⌝)

/-- The batch lock's ghost share, held. -/
abbrev batchGhost (γ : BNames) (P : BParams) (st : BSess) : IProp GF := batchGhostAt γ P st false

/-- The batch lock's resource, free: a state with `freeOk` and the client's resource `WR`; or
the backend stopped (the `run` goroutine's `CommitAndStop`: the open token whole inside). -/
def batchFree (γ : BNames) (P : BParams) (WR : IProp GF) (b t : Loc) : IProp GF :=
  iprop((∃ (st : BSess) (db : Loc), batchPhys γ b t db st ∗ batchGhostAt γ P st true ∗ ⌜freeOk P st⌝ ∗
    WR) ∨
    bStopped γ)

/-- The batch lock held, in state `st` (its transaction `t`, its database `db`). -/
def batchLockedAt (γ : BNames) (P : BParams) (b t db : Loc) (st : BSess) : IProp GF :=
  iprop(sync.ownMutex (muOf t) ∗ batchPhys γ b t db st ∗ batchGhost γ P st ∗ ⌜sessWf P st⌝)

/-- The batch lock held by the client, in state `st`. -/
def batchLocked (γ : BNames) (P : BParams) (b : Loc) (st : BSess) : IProp GF :=
  iprop(∃ (t db : Loc), bF go!"batchTx" b ↦□ t ∗ batchLockedAt γ P b t db st)

/-- A `Hooks` value: nil, or one whose `OnPreCommitUnsafe(tx)`, on the batch transaction `t`
held in a state `st`, with the client's resource `WR`, makes a hook step (`hookStep`). -/
def hooksSpec (γ : BNames) (P : BParams) (WR : IProp GF) (b t : Loc) (h : GoInterface) :
    IProp GF :=
  iprop(⌜h = GoInterface.nil⌝ ∨ ∃ ho : GoInterfaceOk, ⌜h = GoInterface.ok ho⌝ ∗
    □ ∀ st : BSess,
      {{ batchLocked γ P b st ∗ WR }}
        (App (Val #(methods ho.ty go!"OnPreCommitUnsafe" ho.v))
          (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
      {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ WR ∗ ⌜hookStep P st st'⌝ }})

/-- A `HookFunc` with the same contract (what `NewHooks` wraps). -/
def hookFnSpec (γ : BNames) (P : BParams) (WR : IProp GF) (b t : Loc) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ st : BSess,
    {{ batchLocked γ P b st ∗ WR }}
      (App (Val #f) (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
    {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ WR ∗ ⌜hookStep P st st'⌝ }})

instance hooksSpec_persistent (γ : BNames) (P : BParams) (WR : IProp GF) (b t : Loc)
    (h : GoInterface) : Persistent (hooksSpec γ P WR b t h) := by
  unfold hooksSpec; infer_instance

instance hookFnSpec_persistent (γ : BNames) (P : BParams) (WR : IProp GF) (b t : Loc)
    (f : GoFunc) : Persistent (hookFnSpec γ P WR b t f) := by
  unfold hookFnSpec; infer_instance

/-- The backend's metrics fields (atomics). -/
def metricsInv (b : Loc) : IProp GF :=
  iprop(inv (bN.@"metrics") iprop(∃ (a c d e : w64), bF go!"size" b ↦ a ∗
    bF go!"sizeInUse" b ↦ c ∗ bF go!"commits" b ↦ d ∗ bF go!"openReadTxN" b ↦ e))

instance metricsInv_persistent (b : Loc) : Persistent (metricsInv (GF := GF) b) := by
  unfold metricsInv; infer_instance

/-- `b` is a backend with parameters `P`, ghost names `γ`, the client's batch-lock resource
`WR` (persistent). -/
def isBackend (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) : IProp GF :=
  iprop(□ ∃ (t rt tm db lg : Loc) (h : GoInterface),
    bF go!"batchTx" b ↦□ t ∗ bF go!"readTx" b ↦□ rt ∗ bF go!"batchLimit" b ↦□ P.limit ∗
    bF go!"lg" b ↦□ lg ∗ ⌜lg ≠ Loc.null⌝ ∗ bF go!"hooks" b ↦□ h ∗ beOf t ↦□ b ∗
    rtmuOf (baseOf rt) ↦□ tm ∗ hooksSpec γ P WR b t h ∗
    sync.isMutex (muOf t) (batchFree γ P WR b t) ∗
    sync.isRWMutexGuard (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    sync.isRWMutexGuard tm (fun q => tmTok γ q) ∗
    sync.isMutex (cmuOf b) (cacheRes γ P b) ∗ cacheInv γ ∗ metricsInv b ∗
    sync.isRWMutexGuard (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
    isDB db ∗ ⌜P.Wf⌝)

instance isBackend_persistent (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) :
    Persistent (isBackend γ P WR b) := by
  unfold isBackend; infer_instance

/-! ## Readers -/

/-- The bytes a read returns: from the read buffer (read-only for good), or from bbolt's read
transaction `rtx` (valid while it is open). -/
def rdB (rtx : Loc) (s : GoSlice) (b : GoString) : IProp GF :=
  iprop(s ↦*□ b ∨ txBytes rtx s b)

instance rdB_persistent (rtx : Loc) (s : GoSlice) (b : GoString) :
    Persistent (rdB (GF := GF) rtx s b) := by
  unfold rdB; infer_instance

/-- The slices a read returns are `rdB`. -/
def rdSlices (rtx : Loc) (ss : List GoSlice) (bs : List GoString) : IProp GF :=
  iprop(⌜ss.length = bs.length⌝ ∗ [∗list] x ∈ ss.zip bs, rdB rtx x.1 x.2)

/-- The two slices a read returns, owned, of the entries' keys and values. -/
def kvsOutRd (rtx : Loc) (keys vals : GoSlice) (res : List Ent) : IProp GF :=
  iprop(∃ (ks vs : List GoSlice), keys ↦* ks ∗ ownSliceCap GoSlice keys (DFrac.own 1) ∗
    vals ↦* vs ∗ ownSliceCap GoSlice vals (DFrac.own 1) ∗
    rdSlices rtx ks (res.map Prod.fst) ∗ rdSlices rtx vs (res.map Prod.snd))

/-- A reader's tokens, beside `readTx.mu`'s slot: a slot of `txMu` and a reader's budget
token (a `ConcurrentReadTx` keeps them until its `RUnlock`). -/
def crTok (γ : BNames) (b : Loc) : IProp GF :=
  iprop(∃ (rt tm : Loc), bF go!"readTx" b ↦□ rt ∗ rtmuOf (baseOf rt) ↦□ tm ∗
    sync.ownRWMutex tm (fun q => tmTok γ q) ∗ ownToks γ.rdt 1)

/-- A reader's token: a slot of `readTx.mu`, and `crTok`. -/
def rdTok (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ rt : Loc, bF go!"readTx" b ↦□ rt ∗ sync.ownRWMutex (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    crTok γ b)

/-- What `baseReadTx.UnsafeRange` needs of its receiver `base` (a shared or a concurrent read
transaction): its read buffer at `dq` (writable buffers unless read-only for good, a
concurrent one's copy), its bbolt transaction `rtx` (open: `txLive` at `q`) over
the readers' state `rv`, its buckets map with the interval's invariant, `txMu` and a slot of it.
-/
def baseRd (γ : BNames) (P : BParams) (base : Loc) (dq : DFrac) (rtx : Loc) (rv : RView) (q : Qp) :
    IProp GF :=
  iprop(∃ (m : GoMap) (Pb : BksPhys) (cm : GoMap) (tm : Loc),
    rbAt (rbufOf base) dq m Pb rv.2 ∗ rtxOf base ↦{dq} rtx ∗ rbktOf base ↦{dq} cm ∗
    rtmuOf base ↦□ tm ∗ sync.ownRWMutex tm (fun q => tmTok γ q) ∗
    sync.isRWMutexGuard tm (fun q => tmTok γ q) ∗
    txLive rtx q ∗ rtxSnap rtx rv.1 ∗ □ intvInv γ P rtx cm rv.1 ∗
    ⌜rv.2.Wf ∧ idsOk P rv.2.bks ∧ P.Wf ∧ (dq = DFrac.discard ∨ bksOk Pb rv.2.bks)⌝)

/-- A `ConcurrentReadTx` at `crt` (until its `RUnlock`): its fields (its copy of the read
buffer read-only for good), its share of the interval, its slot of `txMu`, over the readers' state
`rv` (the interval's committed data and the copy) and bbolt's transaction `rtx`. -/
def crtSnap (γ : BNames) (P : BParams) (b crt : Loc) (rtx : Loc) (rv : RView) : IProp GF :=
  iprop(∃ (m : GoMap) (Pb : BksPhys) (cm : GoMap) (tm wg : Loc) (γw γo γt : GName) (k : Nat)
      (q : Qp) (rt : Loc),
    bF go!"readTx" b ↦□ rt ∗ rtmuOf (baseOf rt) ↦□ tm ∗
    rbAt (rbufOf (cbaseOf crt)) DFrac.discard m Pb rv.2 ∗ rtxOf (cbaseOf crt) ↦□ rtx ∗
    rbktOf (cbaseOf crt) ↦□ cm ∗ rtmuOf (cbaseOf crt) ↦□ tm ∗ rwgOf (cbaseOf crt) ↦□ wg ∗
    sync.ownRWMutex tm (fun q => tmTok γ q) ∗ sync.isRWMutexGuard tm (fun q => tmTok γ q) ∗
    rdShare rtx γo k q ∗ rtxSnap rtx rv.1 ∗ □ intvInv γ P rtx cm rv.1 ∗
    □ wgInv γ rtx wg γw γo γt ∗ ⌜rv.2.Wf ∧ idsOk P rv.2.bks ∧ P.Wf⌝)

/-- The shared read transaction held (`ReadTx().RLock()`), over the readers' state `rv` and
bbolt's transaction `rtx`. -/
def rtHeld (γ : BNames) (P : BParams) (b : Loc) (rtx : Loc) (rv : RView) : IProp GF :=
  iprop(∃ (rt : Loc) (rd : RdSt) (H : GMap (w64 × Nat) RView), bF go!"readTx" b ↦□ rt ∗
    sync.ownRWMutexRLocked (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    rtResAt γ P rt sync.rfrac rd rv H ∗ ⌜rd.rtx = rtx⌝ ∗ crTok γ b)

end preds

end backend
end EtcdGrove
end Perennial
