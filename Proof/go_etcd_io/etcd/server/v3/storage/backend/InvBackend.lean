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
public import Perennial.Proof.TokSet
public import Perennial.Proof.sync_proof.rwmutex_guard
public import Perennial.Proof.sync_proof.waitgroup
public import Perennial.Proof.sync_proof.mutex

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

section phys
variable [FfiSyntax]

/-- The read side's physical layout: the interval's bbolt read transaction (null once the
backend stopped), its buckets map and `WaitGroup` (with the protocol's ghost names), the read
buffer's map and buffers, and the current state's index in the history. -/
structure RdSt where
  rtx : Loc
  cm : GoMap
  wg : Loc
  γw : GName
  γo : GName
  m : GoMap
  P : BksPhys
  idx : Nat

instance kv_countable : Pos.Countable kv :=
  countableOfLeftInverse (fun x : kv => (x.key', x.val')) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance bbPhys_countable : Pos.Countable BBPhys :=
  countableOfLeftInverse (fun x : BBPhys => (x.buf, x.kvs)) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance rdSt_countable : Pos.Countable RdSt :=
  countableOfLeftInverse
    (fun x : RdSt => (x.rtx, x.cm, x.wg, x.γw, x.γo, x.m, x.P, x.idx))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

end phys

/-- The invariants' namespace. -/
abbrev bN : Namespace := nroot.@"backend"

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

/-- The clients' share of the readers' state. -/
def bView (γ : BNames) (q : Qp) (rv : RView) : IProp GF := ghostVar γ.view q.half rv

/-- The clients' share of the backend being open. -/
def bOpen (γ : BNames) (q : Qp) : IProp GF := ghostVar γ.opn q.half ()

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
  ghostMapElem γ.cached (ver, i) DFrac.discard ()

/-- The cache's marks: a reader marks only the current state (`cur`), and none while an `Unlock`
is in progress (the writer then keeps the clients' half of the view here). -/
def cacheInv (γ : BNames) : IProp GF :=
  iprop(inv (bN.@"cached") iprop(∃ (Cs : GMap (w64 × Nat) Unit) (cur : Option (w64 × Nat)),
    ghostMapAuth γ.cached 1 Cs ∗
    (⌜cur.isSome⌝ ∨ ∃ rv, bView γ 1 rv) ∗ ghostVar γ.cur (1 : Qp).half cur))

/-! ## `txMu` and the intervals -/

/-- `txMu`'s resource: the two exchange tokens at `q`. -/
def tmTok (γ : BNames) (q : Qp) : IProp GF := iprop(ghostVar γ.txa q () ∗ ghostVar γ.txb q ())

/-- What the buckets cache of an interval over `D` holds: handles of `D`'s buckets, by the
table's ids. -/
def cmFacts (P : BParams) (rtx : Loc) (D : Data) (M : GMap w64 Loc) : IProp GF :=
  iprop([∗map] i ↦ bk ∈ M, ∃ (n : GoString) (m : BktData),
    ⌜P.BT.lookup n = some i ∧ D.lookup n = some m ∧ bk ≠ Loc.null⌝ ∗ rBkt rtx bk (bktEnts m))

/-- An interval's buckets cache, exchanged against `txMu`'s first token (a fraction of the map
for the same fraction of the token), and its transaction's statistics against the whole second
token. -/
def intvInv (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) : IProp GF :=
  iprop(inv (bN.@"intv") iprop(∃ (M : GMap w64 Loc) (q : Qp), □ cmFacts P rtx D M ∗
      cm ↦${DFrac.own q} M ∗ (⌜q = 1⌝ ∨ ∃ q', ⌜q + q' = 1⌝ ∗ ghostVar γ.txa q' ())) ∗
    inv (bN.@"stats") iprop(rtxStats rtx ∨ ghostVar γ.txb 1 ()))

/-! ## The interval's `WaitGroup` -/

/-- The interval's `WaitGroup` is open to readers (fractional: `readTx.mu`'s resource holds it;
the commit that ends the interval deposits it whole). -/
def wgOpen (γw : GName) (q : Qp) : IProp GF := ghostVar γw q ()

/-- A reader's share of the interval: its fraction of the transaction's `txLive`, its receipt,
and a reader's budget token, which `Done` returns to the protocol. -/
def rdShare (rtx : Loc) (γo : GName) (k : Nat) (q : Qp) : IProp GF :=
  iprop(txLive rtx q ∗ ghostMapElem γo k (DFrac.own 1) q)

/-- The interval's `WaitGroup` protocol: the counter is the number of outstanding receipts (each
reader also brought a budget token); the pool and the receipts sum to half the transaction (the
other half is `readTx.mu`'s while the interval is current). Open, or closed: `wgOpen 1` inside,
no reader adds any more. -/
def wgInv (γ : BNames) (rtx wg : Loc) (γw γo : GName) : IProp GF :=
  iprop(∃ γwg : sync.WaitGroupNames, sync.isWaitGroup wg γwg (bN.@"wg") ∗
    inv (bN.@"wgi") iprop(∃ (n : w32) (outs : GMap Nat Qp) (pool : Qp),
      sync.ownWaitGroup γwg n ∗ ghostMapAuth γo 1 outs ∗ txLive rtx pool ∗
      ownToks γ.rdt (sint.nat n) ∗
      ⌜sint.Z n = (GMap.size outs : Int) ∧
        ((pool : Qp) : Rat) + (outs.toList.map (fun x => ((x.2 : Qp) : Rat))).sum = 1 / 2⌝ ∗
      (sync.ownWaitGroupWaiters γwg 0 ∨ wgOpen γw 1)))

/-! ## `readTx.mu` -/

/-- The cached copies at the current version read as the current state, off the hook's
buckets: every marked state at `ver` with the current committed data. -/
def cacheValid (γ : BNames) (P : BParams) (rv : RView) : IProp GF :=
  iprop(□ ∀ (i : Nat) (rv' : RView), histAt γ rv.2.ver i rv' -∗ cachedAt γ rv.2.ver i -∗
    ⌜agreeOff P.HB (vOf P (rv.1, rv'.2)) (vOf P rv)⌝)

/-- `readTx.mu`'s resource at `q`. -/
def rtRes (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (rd : RdSt) (rv : RView) (H : GMap (w64 × Nat) RView),
    ghostVar γ.rd q rd ∗ ghostVar γ.view q.half.half rv ∗ ghostMapAuth γ.hist q H ∗
    rbAt (rbufOf (baseOf rt)) (DFrac.own q) rd.m rd.P rv.2 ∗
    rtxOf (baseOf rt) ↦{DFrac.own q} rd.rtx ∗ rbktOf (baseOf rt) ↦{DFrac.own q} rd.cm ∗
    rwgOf (baseOf rt) ↦{DFrac.own q} rd.wg ∗
    ⌜rv.2.Wf ∧ idsOk P rv.2.bks ∧ H.lookup (rv.2.ver, rd.idx) = some rv ∧
      ∀ k rv', H.lookup k = some rv' → k.1 = rv.2.ver → k.2 ≤ rd.idx⌝ ∗
    histAt γ rv.2.ver rd.idx rv ∗ cacheValid γ P rv ∗
    (⌜rd.rtx = Loc.null⌝ ∨
      (txLive rd.rtx q.half ∗ rtxSnap rd.rtx rv.1 ∗ □ intvInv γ P rd.rtx rd.cm rv.1 ∗
        □ wgInv γ rd.rtx rd.wg rd.γw rd.γo ∗ wgOpen rd.γw q)))

/-- A reader's token: a reader slot of `readTx.mu` and a reader's budget token. -/
def rdTok (γ : BNames) (P : BParams) (rt : Loc) : IProp GF :=
  iprop(sync.ownRWMutex (rmuOf (baseOf rt)) (rtRes γ P rt) ∗ ownToks γ.rdt 1)

/-! ## The cache -/

/-- `txReadBufferCache.mu`'s resource: the cached copy (persistent: readers share it) at its
version, marked as the state it copied. -/
def cacheRes (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ (bp : Loc) (ver : w64), cbufOf b ↦ bp ∗ cverOf b ↦ ver ∗
    (⌜bp = Loc.null⌝ ∨
      ∃ (c : txReadBuffer) (Pc : BksPhys) (i : Nat) (rv : RView),
        bp ↦□ c ∗ bksAt c.txBuffer'.buckets' DFrac.discard Pc rv.2.bks ∗
        histAt γ ver i rv ∗ cachedAt γ ver i ∗ ⌜rv.2.Wf⌝))

/-! ## The batch transaction -/

/-- The batch transaction's physical state for `st`: its fields, the write buffer, the
post-lock hook's field, bbolt's database and its write transaction. -/
def batchPhys (γ : BNames) (b t db : Loc) (st : BSess) : IProp GF :=
  iprop(∃ (wtx : Loc) (hk : GoFunc),
    txFOf t ↦ wtx ∗ pendOf t ↦ st.pend ∗ delOf t ↦ st.ndel ∗ ownWB (wbOf t) st.W ∗
    bF go!"txPostLockInsideApplyHook" b ↦ hk ∗ ghostVar γ.hook (1 : Qp).half hk ∗
    ownDB db γ.db st.C ∗ ownWTx wtx γ.db st.C st.S ∗ txDB wtx db)

/-- The batch lock's share of the ghost state for `st`: the view's quarter at `(C, R)` and the
write-back budget's authority (the version and the tokens left fit in a `uint64`). -/
def batchGhost (γ : BNames) (st : BSess) : IProp GF :=
  iprop(ghostVar γ.view (1 : Qp).half.half (st.C, st.R) ∗
    ∃ n : Nat, ownTokAuth γ.wb n ∗ ⌜uint.Z st.R.ver + n < 2 ^ 64⌝)

/-- The batch lock's resource, free: a state with `freeOk`; or the backend stopped (the `run`
goroutine's `CommitAndStop`: the open token whole inside). -/
def batchFree (γ : BNames) (P : BParams) (b t db : Loc) : IProp GF :=
  iprop((∃ st : BSess, batchPhys γ b t db st ∗ batchGhost γ st ∗ ⌜freeOk P st⌝) ∨
    ghostVar γ.opn 1 ())

/-- The batch lock held, in state `st`. -/
def batchLocked (γ : BNames) (P : BParams) (b t db : Loc) (st : BSess) : IProp GF :=
  iprop(sync.ownMutex (muOf t) ∗ batchPhys γ b t db st ∗ batchGhost γ st ∗ ⌜sessWf P st⌝)

end preds

end backend
end EtcdGrove
end Perennial
