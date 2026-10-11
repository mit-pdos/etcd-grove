/-
`client/v3/leasing`'s leasing KV (`kv.go`, `txn.go`): the vocabulary of their specs. Lean-first
(no Rocq counterpart). See `decisions.md`, "Leasing: nested transactions, owned responses,
`isLeasingKV`".

**The leasing KV** (`isLeasingKV lkv γ pfx`, persistent): its immutable fields (`cl`, `kv`,
`pfx`, `ctx`, `cancel`, `sessionOpts`), the client contracts on `lkv.kv` at the whole keyspace
(prefix `[]`: the leasing KV's data keys and lease keys are anywhere): gets (`isEtcdKV`), `Do` of
a get (`isEtcdDoKV`), transactions with nested operations and owned responses (`isEtcdTxnKVO`);
what the monitors (unit 5) use of the client (`isLeasingClient`: its range watcher, its leases, a
session client); its context (a `*cancelCtx`); the lease cache `lkv.leases` (`isLeaseCache`) with
the KV's part of the cache's lock invariant (`leasingX`); and the wait group `lkv.wg`
(`leasingWgInv`). `pfx` is not empty (a lease key `pfx ++ k` is never its data key `k`).

**The KV's part of the cache's lock** (`leasingX lkv γ st q`, fractional, under `lkv.leases.mu`):
the fields `session` and `sessionc`; the **log of the cache's states** (`γ.log`, a monotone list
whose last element is the current state `st`: every writer appends its new state, so a spec can say
"the cache went from `st` to `f st`", `leasingStep`); the session's readiness (a monotone counter,
`1` once `session` was set: it is never nil again, `sessionReady`); the session, if set, is a
session (`isSession`) and the entries map was made (`leaseCacheReady`); `sessionc` is a broadcast
channel whose close announces both. *Not* in it: "every entry's lease is the current session's" —
false of the code (`get` adds the entry of an acquisition after a session reset may have replaced
the session, see `notes/STATUS.md`); the entries' facts (`entryFacts`) are the cache's.

**The wait group** (`leasingWgInv`, an invariant): as the cache's (`InvCache.lean`, `cacheWgInv`):
the counter is the running goroutines, `k` of them with their thread token deposited
(`leasingWgRunning`: `get`'s lease monitors), `d ≤ 2` keeping their own (`NewKV`'s session monitor
and `clearOldRevokes`), with at most one waiter (`Close`), which holds the whole "open" token
(`leasingOpen`): `get` adds to the wait group with a fraction of it.

**A transaction being built** (`ownTxnLeasing`): a `*txnLeasing`'s fields: the inner client builder
(`txn.Txn`, the builder state `B b`), its KV, context, and the comparisons and operations so far
(owned slices of comparisons with their operands set, `cmpSetAt`, and of plain operations a
transaction can run, `txnOpOf`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseEval
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSession
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxnOwn
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## Ghost names -/

/-- The ghost names of a leasing KV: its cache's, the session's readiness, the log of the cache's
states, and the wait group's. -/
structure LeasingNames where
  lc : LeaseCacheNames
  sess : GName
  log : GName
  wg : sync.WaitGroupNames
  wr : GName
  wo : GName
  wc : GName
  op : GName

/-- The number of goroutines `NewKV` starts on the wait group keeping their own thread token (the
session monitor and `clearOldRevokes`). -/
def leasingWgOwedMax : Nat := 2

/-- The namespace of the leasing KV's `sync.WaitGroup`. -/
def leasingWgWGN : Namespace := nroot.@"leasingWaitGroup"

/-- The namespace of the wait-group counter invariant (`leasingWgInv`). -/
def leasingWgN : Namespace := nroot.@"leasingWgCounter"

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&lkv.leases` -/
abbrev lkvLeases (lkv : Loc) : Loc := structFieldRef leasingKV go!"leases" lkv
/-- `&lkv.wg` -/
abbrev lkvWg (lkv : Loc) : Loc := structFieldRef leasingKV go!"wg" lkv

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-! ## The session and the log of the cache's states -/

/-- A session was set (persistent): `lkv.session` is not nil, for good. -/
def sessionReady (γ : LeasingNames) : IProp GF := monoNatLbOwn γ.sess 1

instance sessionReady_persistent (γ : LeasingNames) : Persistent (sessionReady (GF := GF) γ) := by
  unfold sessionReady; infer_instance

/-- The session's readiness counter for the `session` field `s`. -/
def sessN (s : Loc) : Nat := if s = null then 0 else 1

/-- What a set session gives (persistent): a session (`isSession`), and the entries map made. -/
def sessionOk (γ : LeasingNames) (s : Loc) : IProp GF :=
  if s = null then iprop(True)
  else iprop(∃ (γs : concurrency.SessionNames) (cl : Loc) (id : w64),
    concurrency.isSession s γs cl id ∗ leaseCacheReady γ.lc)

instance sessionOk_persistent (γ : LeasingNames) (s : Loc) : Persistent (sessionOk (GF := GF) γ s) := by
  unfold sessionOk; split <;> infer_instance

/-- What the close of `sessionc` announces: a session was set, and the entries map made. -/
def sessionReadyQ (γ : LeasingNames) : IProp GF := iprop(sessionReady γ ∗ leaseCacheReady γ.lc)

instance sessionReadyQ_persistent (γ : LeasingNames) : Persistent (sessionReadyQ (GF := GF) γ) := by
  unfold sessionReadyQ; infer_instance

/-- The `sessionc` channel: a broadcast channel (anyone may receive) announcing `sessionReadyQ`. -/
def sessioncOk (γ : LeasingNames) (sc : GoChan) : IProp GF :=
  iprop(∃ γch : ChanNames, ownBroadcastChan sc γch (sessionReadyQ γ) .Unknown)

instance sessioncOk_persistent (γ : LeasingNames) (sc : GoChan) :
    Persistent (sessioncOk (GF := GF) γ sc) := by
  unfold sessioncOk; infer_instance

/-- The body of `leasingX` for the fields' values: **half** of the `session` and `sessionc` fields
(`q.half`), the other half being the session monitor's (`sessionMonitor`), which reads `session`
without the lock (it is the only writer of both fields). -/
def leasingXBody (lkv : Loc) (γ : LeasingNames) (st : LeaseCacheSt)
    (x : Loc × GoChan × List LeaseCacheSt) (q : Qp) : IProp GF :=
  iprop(structFieldRef leasingKV go!"session" lkv ↦{DFrac.own q.half} x.1 ∗
    structFieldRef leasingKV go!"sessionc" lkv ↦{DFrac.own q.half} x.2.1 ∗
    monoListAuthOwn γ.log q x.2.2 ∗ ⌜x.2.2.getLast? = some st⌝ ∗
    monoNatAuthOwn γ.sess q (sessN x.1) ∗ □ sessionOk γ x.1 ∗ □ sessioncOk γ x.2.1)

/-- **The KV's part of the cache's lock invariant** (fraction `q`; see the module docstring). -/
def leasingX (lkv : Loc) (γ : LeasingNames) (st : LeaseCacheSt) (q : Qp) : IProp GF :=
  iprop(∃ x : Loc × GoChan × List LeaseCacheSt, leasingXBody lkv γ st x q)

/-- Halving distributes over a sum of fractions. -/
theorem Qp_half_add (p q : Qp) : (p + q).half = p.half + q.half := Subtype.ext (by simp; grind)

/-- A points-to at half the fraction is fractional. -/
theorem half_pointsto_fractional_loc (l : Loc) (v : Loc) :
    Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q.half)) where
  fractional p q := by
    have h := (fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
      p.half q.half
    rw [Qp_half_add]
    exact h

theorem half_pointsto_fractional_chan (l : Loc) (v : GoChan) :
    Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q.half)) where
  fractional p q := by
    have h := (fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
      p.half q.half
    rw [Qp_half_add]
    exact h

theorem leasingXBody_fractional (lkv : Loc) (γ : LeasingNames) (st : LeaseCacheSt)
    (x : Loc × GoChan × List LeaseCacheSt) :
    Fractional (leasingXBody (GF := GF) lkv γ st x) := by
  unfold leasingXBody
  haveI := half_pointsto_fractional_loc (GF := GF) (structFieldRef leasingKV go!"session" lkv) x.1
  haveI := half_pointsto_fractional_chan (GF := GF) (structFieldRef leasingKV go!"sessionc" lkv) x.2.1
  infer_instance

instance leasingX_fractional (lkv : Loc) (γ : LeasingNames) (st : LeaseCacheSt) :
    Fractional (leasingX (GF := GF) lkv γ st) := by
  unfold leasingX
  exact lc_fractional_exists_agree (leasingXBody lkv γ st) (leasingXBody_fractional lkv γ st)
    (fun x y q1 q2 => by
      obtain ⟨a, b, c⟩ := x
      obtain ⟨a', b', c'⟩ := y
      unfold leasingXBody
      simp only
      iintro ⟨⟨H1, H2, H3, -⟩, ⟨H1', H2', H3', -⟩⟩
      icombine H1 H1' gives % ⟨-, h1⟩
      icombine H2 H2' gives % ⟨-, h2⟩
      ihave %h3 := monoListAuthOwn_agree γ.log q1 q2 c c' $$ H3 H3'
      ipureintro
      rw [h3.2])

/-- What a reader of the cache learns of the state it read: it is in the log. -/
def leasingSeen (γ : LeasingNames) (st : LeaseCacheSt) : IProp GF :=
  iprop(∃ i : Nat, monoListIdxOwn γ.log i st)

instance leasingSeen_persistent (γ : LeasingNames) (st : LeaseCacheSt) :
    Persistent (leasingSeen (GF := GF) γ st) := by
  unfold leasingSeen; infer_instance

/-- **A step of the cache** from `st` to `st'` (persistent): consecutive states of the log. -/
def leasingStep (γ : LeasingNames) (st st' : LeaseCacheSt) : IProp GF :=
  iprop(∃ i : Nat, monoListIdxOwn γ.log i st ∗ monoListIdxOwn γ.log (i + 1) st')

instance leasingStep_persistent (γ : LeasingNames) (st st' : LeaseCacheSt) :
    Persistent (leasingStep (GF := GF) γ st st') := by
  unfold leasingStep; infer_instance

/-! ## The wait group -/

/-- The "open" token, a fraction `q` of it: `get` (which may `Add(1)` to the wait group from zero)
needs a fraction, `Close` (which waits on it) all of it. -/
def leasingOpen (γ : LeasingNames) (q : Qp) : IProp GF := ghostVar γ.op q ()

/-- **The wait group's counter** (an invariant; see the module docstring and `cacheWgInv`). -/
def leasingWgInv (γ : LeasingNames) : IProp GF :=
  iprop(∃ (ctr : w32) (w k d : Nat), sync.ownWaitGroup γ.wg ctr ∗ sync.ownWaitGroupWaiters γ.wg w ∗
    ownTokAuth γ.wr k ∗ threadToks k ∗
    ownTokAuth γ.wo d ∗ ownToks γ.wc d ∗ ownTokAuth γ.wc leasingWgOwedMax ∗
    ⌜0 ≤ sint.Z ctr⌝ ∗ ⌜sint.nat ctr = k + d⌝ ∗
    (⌜w = 0⌝ ∨ (⌜w = 1⌝ ∗ leasingOpen γ 1)))

instance leasingWgInv_timeless (γ : LeasingNames) : Timeless (leasingWgInv (GF := GF) γ) := by
  unfold leasingWgInv leasingOpen; infer_instance

/-- A goroutine started on the wait group whose thread token is deposited in `leasingWgInv` (a
lease monitor of `get`): its `Done` returns the token. -/
def leasingWgRunning (γ : LeasingNames) : IProp GF := ownToks γ.wr 1

/-- A goroutine started on the wait group keeping its own thread token (`NewKV`'s two). -/
def leasingWgRunningOwed (γ : LeasingNames) : IProp GF := ownToks γ.wo 1

/-! ## The client and the leasing KV -/

/-- **What the monitors (unit 5) use of the client** `cl` (persistent): its `KV` field is `kv`, its
`Watcher` a range watcher of the whole keyspace, its `Lease` a lease client, and it is a session
client whose session options (`sessionOpts` `osl`) give a cancelable context. -/
def isLeasingClient (cl : Loc) (kv : GoInterfaceOk) (osl : GoSlice) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□ GoInterface.ok kv ∗
    (∃ w : GoInterfaceOk, structFieldRef go_etcd_io.etcd.client.v3.Client go!"Watcher" cl ↦□
      GoInterface.ok w ∗ isEtcdRangeWatcher w []) ∗
    isEtcdLeaseClient cl ∗
    ∃ (cctx : GoInterface) (gs : List (concurrency.SessionOpts → concurrency.SessionOpts))
      (pctx : GoInterfaceOk) (pcs : context.ContextDesc (IProp GF)),
      concurrency.isEtcdSessionClient cl cctx ∗ concurrency.sessOptsAt osl gs ∗
      ⌜(concurrency.sessOptsFold gs (concurrency.SessionOpts.init cctx)).ctx = GoInterface.ok pctx⌝ ∗
      context.isContext pctx pcs ∗ context.isCancelCtxCtx pctx pcs)

instance isLeasingClient_persistent (cl : Loc) (kv : GoInterfaceOk) (osl : GoSlice) :
    Persistent (isLeasingClient (GF := GF) cl kv osl) := by
  unfold isLeasingClient; infer_instance

/-- The lease cache of `lkv`, with the KV's part of the lock invariant (persistent). -/
abbrev lkvCache (lkv : Loc) (γ : LeasingNames) (pfx : GoString) : IProp GF :=
  isLeaseCache (lkvLeases lkv) γ.lc pfx (leasingX lkv γ)

/-- A reader slot of `lkv`'s cache (`RLock`). -/
abbrev lkvReader (lkv : Loc) (γ : LeasingNames) (pfx : GoString) : IProp GF :=
  leaseCacheReader (lkvLeases lkv) γ.lc pfx (leasingX lkv γ)

/-- **The leasing KV** `lkv` of the lease prefix `pfx` (persistent; see the module docstring). -/
def isLeasingKV (lkv : Loc) (γ : LeasingNames) (pfx : GoString) : IProp GF :=
  iprop(∃ (cl : Loc) (kv : GoInterfaceOk) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF))
      (cancel : GoFunc) (osl : GoSlice),
    ⌜pfx ≠ []⌝ ∗
    structFieldRef leasingKV go!"cl" lkv ↦□ cl ∗
    structFieldRef leasingKV go!"kv" lkv ↦□ GoInterface.ok kv ∗
    structFieldRef leasingKV go!"pfx" lkv ↦□ pfx ∗
    structFieldRef leasingKV go!"ctx" lkv ↦□ GoInterface.ok ctx ∗
    structFieldRef leasingKV go!"cancel" lkv ↦□ cancel ∗
    structFieldRef leasingKV go!"sessionOpts" lkv ↦□ osl ∗
    isEtcdKV kv [] ∗ isEtcdDoKV kv [] ∗ isEtcdTxnKVO kv [] ∗ isLeasingClient cl kv osl ∗
    context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
    lkvCache lkv γ pfx ∗
    sync.isWaitGroup (lkvWg lkv) γ.wg leasingWgWGN ∗ inv leasingWgN (leasingWgInv γ) ∗
    ⌜threadBound GF + leasingWgOwedMax ≤ 2 ^ 31⌝)

instance isLeasingKV_persistent (lkv : Loc) (γ : LeasingNames) (pfx : GoString) :
    Persistent (isLeasingKV (GF := GF) lkv γ pfx) := by
  unfold isLeasingKV; infer_instance

/-! ## The monitors and `NewKV` (unit 5) -/

/-- **The session monitor's resources** (`monitorSession`, the only writer of `session` and
`sessionc`): the other halves of the two fields (`leasingXBody` has one half under the lock), what
the session it set gives (`sessionOk`), and the current `sessionc`'s close right (`.Pending`) or
the fact that it closed it (`.Done`). -/
def sessionMonitor (lkv : Loc) (γ : LeasingNames) : IProp GF :=
  iprop(∃ (s : Loc) (sc : GoChan) (γch : ChanNames) (closed : Bool),
    structFieldRef leasingKV go!"session" lkv ↦{DFrac.own (1 : Qp).half} s ∗ □ sessionOk γ s ∗
    structFieldRef leasingKV go!"sessionc" lkv ↦{DFrac.own (1 : Qp).half} sc ∗
    ownBroadcastChan sc γch (sessionReadyQ γ) (if closed then .Done else .Pending))

/-- The leasing KV's `cancel` field holds a cancel function that may be called any number of
times (persistent; `Close` calls it). -/
def isLeasingCancel (lkv : Loc) : IProp GF :=
  iprop(∃ cancel : GoFunc, structFieldRef leasingKV go!"cancel" lkv ↦□ cancel ∗
    concurrency.cancelSpec cancel)

instance isLeasingCancel_persistent (lkv : Loc) : Persistent (isLeasingCancel (GF := GF) lkv) := by
  unfold isLeasingCancel; infer_instance

/-- **What `NewKV` assumes of the client** `cl` and the session options `osl` (persistent; the
trust boundary about the client, as the cache's `isEtcdClient`): its `KV` field's gets, `Do`s of a
get and transactions over the whole keyspace, what the monitors use (`isLeasingClient`: the
watcher, the leases, a session client whose options give a cancelable context), and its context
(the `ctx` field `cl.Ctx()` returns) a cancelable one (`newClient` makes it with `WithCancel`). -/
def isLeasingEtcdClient (cl : Loc) (osl : GoSlice) : IProp GF :=
  iprop(∃ (kv : GoInterfaceOk) (cctx : GoInterfaceOk) (ccs : context.ContextDesc (IProp GF)),
    isEtcdKV kv [] ∗ isEtcdDoKV kv [] ∗ isEtcdTxnKVO kv [] ∗ isLeasingClient cl kv osl ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦□ GoInterface.ok cctx ∗
    context.isContext cctx ccs ∗ context.isCancelCtxCtx cctx ccs)

instance isLeasingEtcdClient_persistent (cl : Loc) (osl : GoSlice) :
    Persistent (isLeasingEtcdClient (GF := GF) cl osl) := by
  unfold isLeasingEtcdClient; infer_instance

/-- The `v3.KV` interface value of a `*leasingKV`. -/
abbrev lkvIface (lkv : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType leasingKV.ty) #lkv

/-- **The close function** `cf` `NewKV` returns (`lkv.Close`), for the leasing KV with ghost names
`γ` (persistent): called with the whole "open" token (no `get` running), it returns. -/
def leasingCloseFn (cf : GoFunc) (γ : LeasingNames) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, leasingOpen γ 1 -∗ ▷ Φ #() -∗ WP (App (Val #cf) (Val #())) {{ Φ }})

instance leasingCloseFn_persistent (cf : GoFunc) (γ : LeasingNames) :
    Persistent (leasingCloseFn (GF := GF) cf γ) := by
  unfold leasingCloseFn; infer_instance

/-- The number of the reader slots of the lease cache's `RWMutex` (`sync.rwmutex.actualMaxReaders`,
`2^30 - 1`), all of which `NewKV` hands out. -/
abbrev leasingMaxReaders : Nat := Int.toNat sync.rwmutex.actualMaxReaders

/-- **What `NewKV` returns** for the prefix `pfx`: the `KV` interface value of a leasing KV `lkv`
(`isLeasingKV`) with its handles (every reader slot of the cache, `lkvReader`, and the whole
"open" token), the close function's spec, and the error of `waitSession` (`nil`: a session was
set). -/
def newKVResult (pfx : GoString) (kv : GoInterface) (cf : GoFunc) (err : GoInterface) : IProp GF :=
  iprop(∃ (lkv : Loc) (γ : LeasingNames), ⌜kv = GoInterface.ok (lkvIface lkv)⌝ ∗
    isLeasingKV lkv γ pfx ∗ ([∗list] _x ∈ List.replicate leasingMaxReaders (), lkvReader lkv γ pfx) ∗
    leasingOpen γ 1 ∗ leasingCloseFn cf γ ∗
    (⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ sessionReadyQ γ)))

/-- **A lease key deleted** after `rev` (what `waitRescind` waits for): etcd's whole keyspace at a
revision `r > rev` (reached) has no key `pfx ++ key`. -/
def leaseKeyDeleted (pfx key : GoString) (rev : w64) : IProp GF :=
  iprop(∃ r : w64, etcdReached r ∗ etcdAbsent [] (pfx ++ key) r ∗ ⌜sint.Z rev < sint.Z r⌝)

instance leaseKeyDeleted_persistent (pfx key : GoString) (rev : w64) :
    Persistent (leaseKeyDeleted (GF := GF) pfx key rev) := by
  unfold leaseKeyDeleted; infer_instance

/-! ## A transaction being built -/

/-- What the leasing `Txn`'s methods have been given: the comparisons, the then- and
else-operations (plain operations), and which of `If`, `Then`, `Else` were called. -/
structure LTxnBuild where
  cmps : List CmpModel
  thenOs : List OpFull
  elseOs : List OpFull
  cif : Bool
  cthen : Bool
  celse : Bool

/-- What `lkv.Txn(ctx)` starts from. -/
def LTxnBuild.empty : LTxnBuild :=
  { cmps := [], thenOs := [], elseOs := [], cif := false, cthen := false, celse := false }

/-- The transaction's operations as `TxnOp`s (`txnOpOf` of each; `none` if one is not). -/
def LTxnBuild.thenOps (b : LTxnBuild) : Option (List TxnOp) := b.thenOs.mapM txnOpOf
def LTxnBuild.elseOps (b : LTxnBuild) : Option (List TxnOp) := b.elseOs.mapM txnOpOf

/-- The client's builder state the leasing `Txn` keeps in step with `b`. -/
def LTxnBuild.inner (b : LTxnBuild) (tops eops : List TxnOp) : TxnBuild :=
  { model := { cmps := b.cmps, thenOps := tops, elseOps := eops },
    cif := b.cif, cthen := b.cthen, celse := b.celse }

/-- The slice `sl` of `Cmp`s modelled by `ms`, their operands set (`cmpSetAt`): its elements
read-only (`cmpsSetAt`), its spare capacity owned (`append` may write it). -/
def cmpsOwn (sl : GoSlice) (ms : List CmpModel) : IProp GF :=
  iprop(∃ cs : List go_etcd_io.etcd.client.v3.Cmp, sl ↦*□ cs ∗
    ownSliceCap go_etcd_io.etcd.client.v3.Cmp sl (DFrac.own 1) ∗ ⌜cs.length = ms.length⌝ ∗
    □ ∀ (i : Nat) (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel), ⌜cs[i]? = some c⌝ -∗
      ⌜ms[i]? = some m⌝ -∗ cmpSetAt c m)

/-- The slice `sl` of `Op`s modelled by `os` (plain operations): its elements read-only
(`opsAt`), its spare capacity owned. -/
def opsOwn (sl : GoSlice) (os : List OpFull) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.Op, sl ↦*□ vs ∗
    ownSliceCap go_etcd_io.etcd.client.v3.Op sl (DFrac.own 1) ∗ ⌜vs.length = os.length⌝ ∗
    □ ∀ (i : Nat) (v : go_etcd_io.etcd.client.v3.Op) (o : OpFull), ⌜vs[i]? = some v⌝ -∗
      ⌜os[i]? = some o⌝ -∗ opFullAt v o)

/-- **A `*txnLeasing` being built** (see the module docstring): `txn` of the leasing KV `lkv`,
with the context `ctx`, has been given `b`; its inner client builder `t` (state `B`) has the same
comparisons and the operations' `TxnOp`s. -/
def ownTxnLeasing (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild) : IProp GF :=
  iprop(∃ (t : GoInterfaceOk) (B : TxnBuild → IProp GF) (csl tsl esl : GoSlice)
      (tops eops : List TxnOp),
    structFieldRef txnLeasing go!"Txn" txn ↦ GoInterface.ok t ∗ B (b.inner tops eops) ∗
    txnBuilderSpecO t [] B ∗
    structFieldRef txnLeasing go!"lkv" txn ↦ lkv ∗ isLeasingKV lkv γ pfx ∗
    structFieldRef txnLeasing go!"ctx" txn ↦ GoInterface.ok ctx ∗ context.isContext ctx cs ∗
    structFieldRef txnLeasing go!"cs" txn ↦ csl ∗ cmpsOwn csl b.cmps ∗
    structFieldRef txnLeasing go!"opst" txn ↦ tsl ∗ opsOwn tsl b.thenOs ∗
    structFieldRef txnLeasing go!"opse" txn ↦ esl ∗ opsOwn esl b.elseOs ∗
    ⌜b.thenOps = some tops ∧ b.elseOps = some eops⌝)


/-! ## What the operations return -/

/-- **A get served from the cache**: the entry `e` of `key` in a state `st` of the cache's log
(still in the map, or evicted while the get waited), with its facts (`entryFacts`: etcd's record
of `key` at `e.rev` is `e.acq`, the lease key present with `e.lease`), and a fresh response with
the cached get's answer to `o` (`getResult o e`: of `e`'s cached key-value, which is `e.acq` unless
this client's own writes changed it since, `LeaseEntry.update`/`del`). -/
def getCached (γ : LeasingNames) (pfx key : GoString) (o : OpFull) (ret : Loc) : IProp GF :=
  iprop(∃ (st : LeaseCacheSt) (e : LeaseEntry), leasingSeen γ st ∗
    ⌜st.entries !! key = some e ∨ (key, e) ∈ st.frozen⌝ ∗ entryFacts pfx key e ∗
    freshGetResp ret e.hm e.more e.count (getResult o e))

/-- **A get that acquired the key's lease**: the new entry `e`, its record etcd's at its revision
(`e.kv = e.acq`), which is at least `lo` and reached, and a fresh response with the cached get's
answer to `o`. -/
def getAcquired (pfx key : GoString) (lo : w64) (o : OpFull) (ret : Loc) : IProp GF :=
  iprop(∃ e : LeaseEntry, entryFacts pfx key e ∗ etcdReached e.rev ∗
    ⌜e.kv = e.acq ∧ e.rev = e.hm.revision ∧ sint.Z lo ≤ sint.Z e.rev⌝ ∗
    freshGetResp ret e.hm e.more e.count (getResult o e))

/-- **A get answered by an acquisition that failed** (another client holds the key's lease): etcd's
answer at a revision `r ≥ lo` (reached) to `OpGet(key)` — **not** to the get `o`: its options
(`WithKeysOnly`, `WithCountOnly`, the revision filters) are ignored (a finding, `STATUS.md`). The
response `ret` (a `*pb.RangeResponse`) is owned, its header the transaction's. -/
def getNotAcquired (key : GoString) (lo : w64) (ret : Loc) : IProp GF :=
  iprop(∃ (r : w64) (s : List EtcdKv) (hdr : Loc) (hm : HdrM) (n : Nat),
    ⌜ret ≠ null ∧ hm.revision = r ∧ sint.Z lo ≤ sint.Z r ∧ EtcdStateWf [] s⌝ ∗ etcdReached r ∗
    □ etcdState r [] s ∗
    structFieldRef etcdserverpb.RangeResponse go!"Header" ret ↦ hdr ∗ hdrFull hdr hm ∗
    rangeBodyOwn ret (OpFull.getInit key) (rangeSel s (OpFull.getInit key)) n)

/-- **What `get` returns** for the get `o` (called knowing that etcd reached `lo`), and the monitor
slot `slot` back unless a lease monitor was started: the client's answer (`kvGetResult`: the
session is not ready, the cache does not serve `o`, `o` is serializable, or the key was revoked
recently), the cache's (`getCached`), an acquisition's (`getAcquired`: the slot goes to the
monitor), a failed acquisition's (`getNotAcquired`), or the acquisition's error. -/
def getOutcome (γ : LeasingNames) (pfx : GoString) (lo : w64) (o : OpFull) (ret : Loc)
    (err : GoInterface) (slot : IProp GF) : IProp GF :=
  iprop((kvGetResult [] lo o ret err ∗ slot) ∨
    (⌜err = GoInterface.nil⌝ ∗ getCached γ pfx o.key o ret ∗ slot) ∨
    (⌜err = GoInterface.nil⌝ ∗ getAcquired pfx o.key lo o ret) ∨
    (⌜err = GoInterface.nil⌝ ∗ getNotAcquired o.key lo ret ∗ slot) ∨
    (⌜err ≠ GoInterface.nil ∧ ret = null⌝ ∗ slot))

/-- **A transaction committed with its then-branch the single operation `top`**, as the leasing
KV's writes are (`tryModifyOp`'s and `revoke`'s guarded transactions, when they succeed): at a
revision `r ≥ lo` (reached), on the state `s` (etcd's at `r - 1` if it wrote, at `r` otherwise),
`top` ran (`applyTxnOp`); the response owned (`txnRespOwn`, `Succeeded` true). -/
def opCommitted (lo : w64) (top : TxnOp) (resp : Loc) : IProp GF :=
  iprop(∃ (r : w64) (s : List EtcdKv) (hm : HdrM), ⌜hm.revision = r⌝ ∗
    txnRespOwn resp hm true [top] [(applyTxnOp r s top).2] ∗ etcdReached r ∗
    ⌜sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧ EtcdStateWf [] s⌝ ∗
    txnStates [] r s (applyTxnOp r s top).1 (applyTxnOp r s top).2.wrote)

/-- **A guarded transaction that did not succeed**: its `Succeeded` field, owned, is false. -/
def notCommitted (resp : Loc) : IProp GF :=
  iprop(structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦ false)

/-- **A put committed** (what `put` returns on success): the put `top` (of the `Op` modelled by
`o`) ran at a revision `r ≥ lo` (reached) on the state `s` (etcd's at `r - 1`), the response's
header has revision `r`; and **the cache took the step** from a state `st` to `st` with `o.key`'s
entry, if any, updated by the put (`LeaseEntry.update`: `Update(key, val, hdr)` with the `Op`'s key
and value slices `ksl`, `vsl`, which caches `o.val` whatever the put's options, and keeps the
cached lease). -/
def putCommitted (γ : LeasingNames) (lo : w64) (o : OpFull) (top : TxnOp) (pr : Loc) : IProp GF :=
  iprop(∃ (r : w64) (s : List EtcdKv) (hdr : Loc) (hm : HdrM), ⌜pr ≠ null ∧ hm.revision = r⌝ ∗
    structFieldRef etcdserverpb.PutResponse go!"Header" pr ↦ hdr ∗ hdrFull hdr hm ∗
    etcdReached r ∗
    ⌜sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧ EtcdStateWf [] s⌝ ∗
    txnStates [] r s (applyTxnOp r s top).1 true ∗
    ∃ (st : LeaseCacheSt) (p : Loc) (sl' ksl vsl : GoSlice), leasingStep γ st
      (st.modify o.key (fun e => e.update (freshKv p ksl o.key r) sl' hdr hm vsl o.val)))

/-- **A delete committed** (what `delete` returns on success): the keys of `o`'s range were
deleted at a revision `r ≥ lo` (reached) from the state `s` (etcd's at `r - 1` if some key was,
at `r` otherwise), `n` of them, the response's `Deleted`; its header has revision `r`. -/
def deleteCommitted (lo : w64) (o : OpFull) (dr : Loc) : IProp GF :=
  iprop(∃ (r : w64) (s : List EtcdKv) (hdr : Loc) (hm : HdrM) (n : Nat),
    ⌜dr ≠ null ∧ hm.revision = r ∧ n = (rangeIn s o).length⌝ ∗
    structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" dr ↦ hdr ∗ hdrFull hdr hm ∗
    structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" dr ↦□ W64 (n : Int) ∗
    etcdReached r ∗
    ⌜sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧ EtcdStateWf [] s⌝ ∗
    txnStates [] r s (s.filter (fun v => !inRange o.key o.base.rangeEnd v.key)) (n != 0))

/-- **A transaction evaluated in the cache** (`eval`): in a state `st` of the cache's log whose
latest header is set, the comparisons of `b` evaluate to `ok` (`leaseEvalCmps`, which is not
etcd's comparison: `evalCmpM_agrees`), and every operation of the chosen branch is a cached get
(`leaseEvalOk`); the fresh response: a copy of `st`'s latest header, `Succeeded` `ok`, each
operation's cached answer (`respOpFresh`). -/
def evalResult (γ : LeasingNames) (b : LTxnBuild) (resp : Loc) : IProp GF :=
  iprop(∃ (st : LeaseCacheSt) (ok : Bool) (hdr : Loc) (rsl : GoSlice) (ps : List Loc),
    leasingSeen γ st ∗
    ⌜leaseEvalCmps st b.cmps = (ok, true) ∧ st.header ≠ null ∧
      leaseEvalOk st (if ok then b.thenOs else b.elseOs) = true ∧
      ps.length = (if ok then b.thenOs else b.elseOs).length⌝ ∗
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦ hdr ∗ hdrFull hdr st.hm ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦ ok ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦ rsl ∗ rsl ↦* ps ∗
    [∗list] i ↦ p ∈ ps, ∃ (o : OpFull) (e : LeaseEntry),
      ⌜(if ok then b.thenOs else b.elseOs)[i]? = some o ∧ st.entries !! o.key = some e⌝ ∗
      respOpFresh p o e)

/-- The transaction `b` describes, if its operations are ones a transaction can run. -/
def LTxnBuild.model (b : LTxnBuild) (tops eops : List TxnOp) : TxnModel :=
  { cmps := b.cmps, thenOps := tops, elseOps := eops }

/-- **What `Commit` returns** for the transaction `b` (called knowing that etcd reached `lo`): the
cache's evaluation (`evalResult`), or what the client's `Commit` would return for the
transaction (`txnCommitResult`: an error, or the transaction at a revision `r ≥ lo` on etcd's
state). -/
def commitOutcome (γ : LeasingNames) (lo : w64) (b : LTxnBuild) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ evalResult γ b resp) ∨
    (∃ tops eops : List TxnOp, ⌜b.thenOps = some tops ∧ b.elseOps = some eops⌝ ∗
      txnCommitResult [] lo (b.model tops eops) resp err))

/-- The `v3.Txn` interface value of a `*txnLeasing`. -/
abbrev txnIface (txn : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType txnLeasing.ty) #txn

end defs

end EtcdGrove
end Perennial
