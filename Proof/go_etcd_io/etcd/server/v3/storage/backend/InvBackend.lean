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
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.FkLemmas
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
  /-- `ghostVar`: the writer's contents on the hook's own keys (`hkData`), half the batch
  lock's, half the client's (`hkOwn`) -/
  hkd : GName
  /-- `ghostVar`: the writer's contents on the tracked buckets (`rbData`, D22, 2026-10-23), half
  the batch lock's, half the client's (`rbOwn`) -/
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
  /-- `dghostVar Bool`, discarded at allocation: whether the compaction keys hold only
  well-formed values (`P.FV`) in every state of the backend (question 4, 2026-10-29: true when the
  data at creation does, `fkWInit`; a put of one needs a well-formed value, so it never changes) -/
  fkv : GName

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

/-! ## The logical view after a put session (question 2, option (a), 2026-10-29) -/

/-- **The logical view after a put session's `Unlock`**: the writer's contents over `L`, `L`'s
entries kept only where the readers' physical view before the session already lacked them (keys
compaction deleted earlier, still in mvcc's logical bucket: R5-1). A key the session itself deleted
leaves the logical view if the readers could see it; a key already compacted stays in it (R11-6).
(Question 2's Draft had the extra condition "in a safe-range bucket" (`P.SB`), redundant: review
round 11, R11-5.) -/
def relog (P : BParams) (L : GMap (GoString × GoString) GoString) (st : BSess) : GMap (GoString × GoString) GoString :=
  sData P st.S ∪ GMap.filter (fun nk _ => decide ((vData P (st.C, st.R)).lookup nk = none)) L

theorem relog_lookup (P : BParams) (L : GMap (GoString × GoString) GoString) (st : BSess) (nk : GoString × GoString) :
    (relog P L st).lookup nk =
      ((sData P st.S).lookup nk).or
        (if (vData P (st.C, st.R)).lookup nk = none then L.lookup nk else none) := by
  unfold relog
  show ((sData P st.S).lookup nk).or ((L.lookup nk).filter _) = _
  congr 1
  cases hL : L.lookup nk <;>
    by_cases h : (vData P (st.C, st.R)).lookup nk = none <;>
    simp_all [Option.filter]

/-- **With an exact logical view, `relog` is the writer's contents.** -/
theorem relog_exact (P : BParams) (st : BSess) :
    relog P (vData P (st.C, st.R)) st = sData P st.S := by
  apply GMap.ext
  intro nk
  rw [relog_lookup]
  by_cases h : (vData P (st.C, st.R)).lookup nk = none
  · simp only [h, ↓reduceIte]; cases (sData P st.S).lookup nk <;> rfl
  · simp only [h, ↓reduceIte]; cases (sData P st.S).lookup nk <;> rfl

/-- **A session that changed nothing the readers see keeps the logical view**: if the writer's
contents are the physical view and the physical view is included in `L`, `relog` is `L`. -/
theorem relog_same (P : BParams) (L : GMap (GoString × GoString) GoString) (st : BSess)
    (hs : sData P st.S = vData P (st.C, st.R))
    (hsub : ∀ nk v, (vData P (st.C, st.R)).lookup nk = some v → L.lookup nk = some v) :
    relog P L st = L := by
  apply GMap.ext
  intro nk
  rw [relog_lookup, hs]
  cases h : (vData P (st.C, st.R)).lookup nk with
  | none => simp
  | some v => simp [hsub nk v h]


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

instance bViewC_timeless (γ : BNames) (q : Qp) (vd : VData) (c : Bool) :
    Timeless (bViewC (GF := GF) γ q vd c) := by
  unfold bViewC; infer_instance

/-- The clients' share of the readers' view, with or without the read buffer known clean
(`bViewC`, the restore plan's R5a). -/
def bView (γ : BNames) (q : Qp) (vd : VData) : IProp GF :=
  iprop(∃ c : Bool, bViewC γ q vd c)

instance bView_timeless (γ : BNames) (q : Qp) (vd : VData) : Timeless (bView (GF := GF) γ q vd) := by
  unfold bView; infer_instance

theorem bViewC_bView (γ : BNames) (q : Qp) (vd : VData) (c : Bool) :
    bViewC (GF := GF) γ q vd c ⊢ bView γ q vd := by
  unfold bView; iintro H; iexists c; iexact H

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

/-- The clients' share `dq` of the post-lock hook (a `dghostVar`; the batch lock holds an owned
half). -/
def plHookAt (γ : BNames) (dq : DFrac) (f : GoFunc) : IProp GF := dghostVar γ.hook dq f

/-- The clients' owned half of the post-lock hook (`SetTxPostLockInsideApplyHook` changes it). -/
abbrev plHook (γ : BNames) (f : GoFunc) : IProp GF := plHookAt γ (DFrac.own (1 : Qp).half) f

/-- The post-lock hook is `f` for good (persistent: `plHook_persist`). -/
abbrev plHookRO (γ : BNames) (f : GoFunc) : IProp GF := plHookAt γ DFrac.discard f

instance plHookRO_persistent (γ : BNames) (f : GoFunc) : Persistent (plHookRO (GF := GF) γ f) := by
  unfold plHookRO plHookAt; infer_instance

/-- The clients' half of the post-lock hook made read-only: the hook is `f` for good. -/
theorem plHook_persist (γ : BNames) (f : GoFunc) : plHook (GF := GF) γ f ⊢ |==> plHookRO γ f := by
  unfold plHookRO plHook plHookAt
  iintro H
  iapply dghostVar_persist $$ H

/-- One write-back's budget (an `Unlock` costs one). -/
def wbTok (γ : BNames) : IProp GF := ownToks γ.wb 1

/-- The client's half of the hook's own keys: the writer's contents hold `d` there
(`hkData`). Only its holder can put a hook's own key (`UnsafePut`), and it agrees with every
state of the batch lock. -/
def hkOwn (γ : BNames) (d : GMap (GoString × GoString) GoString) : IProp GF :=
  ghostVar γ.hkd (1 : Qp).half d

/-- What a put of key `k` in bucket `n` needs and gives of the hook's own keys, the writer's
contents being `S`: the client's half if `k` is a hook's own key, else nothing. -/
def hkPut (γ : BNames) (P : BParams) (n k : GoString) (S : Data) : IProp GF :=
  if P.hk n k then hkOwn γ (hkData P S) else iprop(True)

/-- **The client's half of the tracked buckets** (D22, 2026-10-23: the backend over every
bucket): the writer's contents hold `r` there (`rbData`: each tracked bucket's contents, absent
if absent). Only its holder can put in, delete from, create or delete a tracked bucket
(`UnsafePut`, `UnsafeDelete`, `UnsafeCreateBucket`, `UnsafeDeleteBucket`), and it agrees with
every state of the batch lock and with what a snapshot's commit leaves (`backend.Snapshot`). -/
def rbOwn (γ : BNames) (r : GMap GoString BktData) : IProp GF :=
  ghostVar γ.rbk (1 : Qp).half r

instance rbOwn_timeless (γ : BNames) (r : GMap GoString BktData) :
    Timeless (rbOwn (GF := GF) γ r) := by
  unfold rbOwn; infer_instance

/-- What an operation on bucket `n` needs and gives of the tracked buckets, the writer's contents
being `S`: the client's half if `n` is tracked, else nothing. -/
def rbPut (γ : BNames) (P : BParams) (n : GoString) (S : Data) : IProp GF :=
  if P.RB n then rbOwn γ (rbData P S) else iprop(True)

/-- An untracked bucket's operation needs nothing of the tracked buckets. -/
theorem rbPut_other (γ : BNames) (P : BParams) (n : GoString) (S : Data) (h : P.RB n = false) :
    ⊢ rbPut (GF := GF) γ P n S := by
  unfold rbPut; rw [h]; simp only [Bool.false_eq_true, ↓reduceIte]; iintro; itrivial

/-- **The client's half of the compaction keys' flag** (`γ.fk`, the backend-compaction stage,
2026-10-29): at `0`, no state of the backend has a compaction key (`fkKey`), not the batch
lock's (`fkHalf`) and not any reader's (`fkRd`, `rtHeldF_fk`); a put of a compaction key needs it
and gives it back raised (`fkPut`). The constructor gives it (`fkInit`). -/
def fkOwn (γ : BNames) (n : Nat) : IProp GF := monoNatAuthOwn γ.fk (1 : Qp).half n

instance fkOwn_timeless (γ : BNames) (n : Nat) : Timeless (fkOwn (GF := GF) γ n) := by
  unfold fkOwn; infer_instance

/-- **The compaction keys' well-formedness bit** (persistent; question 4, 2026-10-29): at `true`,
every state of the backend holds only well-formed values (`P.FV`) at the compaction keys. The
constructor gives it (`fkWInit`); it never changes. With the flag it is the three levels of the
user's question 4: `fkOwn γ 0` (no compaction key), `fkV γ true` (only well-formed ones), else
nothing known. -/
def fkV (γ : BNames) (w : Bool) : IProp GF := dghostVar γ.fkv DFrac.discard w

instance fkV_persistent (γ : BNames) (w : Bool) : Persistent (fkV (GF := GF) γ w) := by
  unfold fkV; infer_instance

/-- **What the constructor gives the client of the compaction keys** over bbolt's data `D`: the
client's half of their flag, at `0` if `D` has none (`fkInit`), and the bit, `true` if `D`'s are
well formed (`fkWInit`). -/
def fkCl (γ : BNames) (P : BParams) (D : Data) : IProp GF :=
  iprop(fkOwn γ (fkInit D) ∗ fkV γ (fkWInit P D))

/-- The batch lock's half of the flag, with what it and the bit say of its state (`fkOk`). -/
def fkHalf (γ : BNames) (P : BParams) (st : BSess) : IProp GF :=
  iprop(∃ (f : Nat) (w : Bool), monoNatAuthOwn γ.fk (1 : Qp).half f ∗ fkV γ w ∗ ⌜fkOk P f w st⌝)

/-- A reader's lower bound of the flag, taken when its state `rv` was set, with the bit
(persistent). -/
def fkRd (γ : BNames) (P : BParams) (rv : RView) : IProp GF :=
  iprop(∃ (f : Nat) (w : Bool), monoNatLbOwn γ.fk f ∗ fkV γ w ∗ ⌜fkOkRv P f w rv⌝)

instance fkRd_persistent (γ : BNames) (P : BParams) (rv : RView) :
    Persistent (fkRd (GF := GF) γ P rv) := by
  unfold fkRd; infer_instance

/-- What a put of key `k` in bucket `n` needs and gives back of the flag: the client's half, at
some value, if `k` is a compaction key, else nothing. (The put raises the flag to at least `1`;
the post does not say so, no caller needing it.) -/
def fkPut (γ : BNames) (n k : GoString) : IProp GF :=
  if fkKey n k then iprop(∃ f : Nat, fkOwn γ f) else iprop(True)

/-- A put of a key that is not a compaction key needs nothing of the flag. -/
theorem fkPut_other (γ : BNames) (n k : GoString) (h : ¬ fkKey n k) : ⊢ fkPut (GF := GF) γ n k := by
  unfold fkPut; rw [if_neg h]; iintro; itrivial

/-- The same, as an equation. -/
theorem fkPut_eq (γ : BNames) (n k : GoString) (h : ¬ fkKey n k) :
    fkPut (GF := GF) γ n k = iprop(True) := by
  unfold fkPut; exact if_neg h

/-- The batch lock's halves of what it tracks of the writer's contents `S`: the hook's own keys
(`γ.hkd`) and the tracked buckets (`γ.rbk`). -/
def trkHalf (γ : BNames) (P : BParams) (S : Data) : IProp GF :=
  iprop(ghostVar γ.hkd (1 : Qp).half (hkData P S) ∗ ghostVar γ.rbk (1 : Qp).half (rbData P S))

/-- Two contents with the same tracked data have the same halves. -/
theorem trkHalf_eq (γ : BNames) (P : BParams) {S S' : Data} (h1 : hkData P S' = hkData P S)
    (h2 : rbData P S' = rbData P S) : trkHalf (GF := GF) γ P S = trkHalf γ P S' := by
  unfold trkHalf; rw [h1, h2]

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

instance dlNoDel_persistent (γ : BNames) : Persistent (dlNoDel (GF := GF) γ) := by
  unfold dlNoDel; infer_instance

instance dlReg_persistent (γ : BNames) (Φ : GoString × GoString → IProp GF) :
    Persistent (dlReg (GF := GF) γ Φ) := by
  unfold dlReg; infer_instance

/-- **The key `nk` (bucket, key) is deletable** (persistent): the registered predicate holds of it. -/
def dlIs (γ : BNames) (nk : GoString × GoString) : IProp GF :=
  iprop(∃ Φ : GoString × GoString → IProp GF, dlReg γ Φ ∗ □ Φ nk)

instance dlIs_persistent (γ : BNames) (nk : GoString × GoString) :
    Persistent (dlIs (GF := GF) γ nk) := by
  unfold dlIs; infer_instance

/-- **A physical view thin of the logical view `L`** (persistent): every entry of the physical
view `vd` is `L`'s, and an entry of `L` missing from `vd` is a deletable key. -/
def thinV (γ : BNames) (vd L : VData) : IProp GF :=
  iprop(⌜∀ nk v, vd.lookup nk = some v → L.lookup nk = some v⌝ ∗
    □ ∀ nk, ⌜L.lookup nk ≠ none ∧ vd.lookup nk = none⌝ -∗ dlIs γ nk)

instance thinV_persistent (γ : BNames) (vd L : VData) : Persistent (thinV (GF := GF) γ vd L) := by
  unfold thinV; infer_instance

/-- An exact view is thin. -/
theorem thinV_refl (γ : BNames) (vd : VData) : ⊢ thinV (GF := GF) γ vd vd := by
  iunfold thinV
  isplitr
  · ipureintro; intro nk v h; exact h
  · iintro !> %nk %h
    exact absurd h.2 h.1

/-- **A cached read buffer reads thin of the logical view** (3.2; Draft): the cached copies of the states up to `idx` at the current version read thin of the
logical view `L` (until the stage: "exactly as the current state"; now (a tombstone put and compacted within one commit interval: a
reader of the cached buffer may still see the deleted key, which it never looks up). -/
def cacheValid (γ : BNames) (P : BParams) (rv : RView) (idx : Nat) (L : VData) :
    IProp GF :=
  iprop(□ ∀ (i : Nat) (rv' : RView), ⌜i ≤ idx⌝ -∗ histAt γ rv.2.ver i rv' -∗
    cachedAt γ rv.2.ver i -∗ thinV γ (vData P (rv.1, rv'.2)) L)

instance cacheValid_persistent (γ : BNames) (P : BParams) (rv : RView) (idx : Nat) (L : VData) :
    Persistent (cacheValid (GF := GF) γ P rv idx L) := by
  unfold cacheValid; infer_instance

/-- **A quarter of the readers' view, over the logical view** (the thin-view Draft round): the
ghost share at the logical view `L` the clients hold, and the physical view `phys` thin of it
(`thinV`). Until the stage the share held the physical view itself; an exact holder is the instance
`L = phys` (`viewQ_exact`). -/
def viewQ (γ : BNames) (q : Qp) (phys L : VData) : IProp GF :=
  iprop(ghostVar γ.view q L ∗ thinV γ phys L)

/-- The view's quarters split and combine (`thinV` persistent). -/
theorem viewQ_split (γ : BNames) (a b : Qp) (phys L : VData) :
    viewQ (GF := GF) γ (a + b) phys L ⊣⊢ viewQ γ a phys L ∗ viewQ γ b phys L := by
  unfold viewQ
  constructor
  · iintro ⟨Hv, #Ht⟩
    icases ghostVar_split γ.view L a b $$ Hv with ⟨H1, H2⟩
    iframe H1 H2
    iframe #
  · iintro ⟨⟨H1, #Ht⟩, ⟨H2, -⟩⟩
    icombine H1 H2 as Hv
    iframe Hv
    iframe #

/-- A quarter at an exact view. -/
theorem viewQ_exact (γ : BNames) (q : Qp) (vd : VData) :
    ghostVar (GF := GF) γ.view q vd ⊢ viewQ γ q vd vd := by
  iintro H
  iunfold viewQ
  iframe H
  iapply thinV_refl

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

instance clnPart_timeless (γ : BNames) (P : BParams) (q : Qp) (rd : RdSt) (rv : RView) :
    Timeless (clnPart (GF := GF) γ P q rd rv) := by
  unfold clnPart; infer_instance

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
    bF go!"txPostLockInsideApplyHook" b ↦ hk ∗ dghostVar γ.hook (DFrac.own (1 : Qp).half) hk ∗
    ownDB db γ.db st.C ∗ ownWTx st.tx γ.db st.C st.S ∗ txDB st.tx db ∗
    sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db))

/-- **The batch lock's quarter of the readers' view, over the logical view** (question 2, option (a),
2026-10-29; until then the quarter at the physical view `vData P (st.C, st.R)` itself): some logical
view `L`, the physical view thin of it (`viewQ`). Exact is the instance `L = vData P (st.C, st.R)`
(`batchViewQ_of_exact`). -/
def batchViewQ (γ : BNames) (P : BParams) (st : BSess) : IProp GF :=
  iprop(∃ L : VData, viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) L)

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

/-- **Thinness composes**: a view thin of one thin of `L` is thin of `L` (a deleting session's
commit: the new physical view thin of the old, the old thin of the logical). -/
theorem thinV_trans (γ : BNames) (a b c : VData) :
    thinV (GF := GF) γ a b ∗ thinV γ b c ⊢ thinV γ a c := by
  iunfold thinV
  iintro ⟨⟨%H1, #D1⟩, ⟨%H2, #D2⟩⟩
  isplitr
  · ipureintro; intro nk v h; exact H2 nk v (H1 nk v h)
  · iintro !> %nk %h
    cases hb : b.lookup nk with
    | none => iapply D2; ipureintro; exact ⟨h.1, hb⟩
    | some v => iapply D1; ipureintro; exact ⟨by simp [hb], h.2⟩

/-- **A put session keeps the physical view thin of the logical one**: the new physical view
`sData P st.S` is thin of `relog P L st` whenever the old physical view was thin of `L`. -/
theorem thinV_relog (γ : BNames) (P : BParams) (L : VData) (st : BSess) :
    thinV (GF := GF) γ (vData P (st.C, st.R)) L ⊢ thinV γ (sData P st.S) (relog P L st) := by
  iunfold thinV
  iintro ⟨-, #D⟩
  isplitr
  · ipureintro; intro nk v h; rw [relog_lookup, h]; rfl
  · iintro !> %nk %h
    obtain ⟨h1, h2⟩ := h
    rw [relog_lookup, h2] at h1
    by_cases hc : (vData P (st.C, st.R)).lookup nk = none
    · simp only [hc, ↓reduceIte] at h1
      iapply D
      ipureintro
      exact ⟨by simpa using h1, hc⟩
    · simp only [hc, ↓reduceIte] at h1; exact absurd rfl h1

/-- Today's exact quarter is an instance of the batch lock's logical quarter. -/
theorem batchViewQ_of_exact (γ : BNames) (P : BParams) (st : BSess) :
    ghostVar (GF := GF) γ.view (1 : Qp).half.half (vData P (st.C, st.R)) ⊢ batchViewQ γ P st := by
  unfold batchViewQ
  iintro H
  iexists vData P (st.C, st.R)
  iapply viewQ_exact $$ H

/-- **The clients' view is the logical one** (agreement of the shares of `γ.view`): the batch
lock's physical view is thin of what a client holds. -/
theorem batchViewQ_bView (γ : BNames) (P : BParams) (st : BSess) (q : Qp) (vd : VData) :
    batchViewQ (GF := GF) γ P st ∗ bView γ q vd ⊢
      batchViewQ γ P st ∗ bView γ q vd ∗ thinV γ (vData P (st.C, st.R)) vd := by
  unfold batchViewQ bView bViewC viewQ
  iintro ⟨⟨%L, Hq, #Ht⟩, ⟨%c, Hv, Hc, Hl⟩⟩
  icombine Hq Hv gives %Heq
  obtain ⟨-, rfl⟩ := Heq
  iframe Hc Hl Hq Hv
  iframe #

/-- **What a client reads of the batch lock: the physical view is thin of the clients' view.** -/
theorem batchLocked_thin (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (q : Qp) (vd : VData) :
    batchLocked (GF := GF) γ P b st ∗ bView γ q vd ⊢
      batchLocked γ P b st ∗ bView γ q vd ∗ thinV γ (vData P (st.C, st.R)) vd := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, Hrest⟩, %Hwf⟩, Hc⟩
  ihave ⟨Hv, Hc, #Hth⟩ := batchViewQ_bView γ P st q vd $$ [$Hv $Hc]
  iframe Hc
  isplitl
  · iexists t, db
    iframe
    iframe #
    ipureintro; exact Hwf
  iexact Hth

/-- **A no-change session is a deleting session with nothing deleted** (`viewSame`: the writer's
contents are the physical view, no puts to the non-hook buckets). -/
theorem viewSame_thin (γ : BNames) (P : BParams) (st : BSess) (h : viewSame P st) :
    ⊢ thinV (GF := GF) γ (sData P st.S) (vData P (st.C, st.R)) ∗
      ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ := by
  rw [← h.1]
  isplitl
  · iapply thinV_refl
  · ipureintro; exact h.2

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

/-- A `HookFunc` with the same contract (what `NewHooks` wraps). -/
def hookFnSpec (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (st : BSess) (stop : Bool) (m u : Nat),
    {{ batchLocked γ P b st ∗ Pk ∗ ⌜hookPre P st⌝ ∗ payIn γ st stop m u }}
      (App (Val #f) (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
    {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ payIn γ st stop m u ∗
        ⌜hookStep P st st'⌝ }})

instance hooksSpec_persistent (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc)
    (h : GoInterface) : Persistent (hooksSpec γ P Pk b t h) := by
  unfold hooksSpec; infer_instance

instance hookFnSpec_persistent (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc)
    (f : GoFunc) : Persistent (hookFnSpec γ P Pk b t f) := by
  unfold hookFnSpec; infer_instance

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

instance hooksReq_persistent (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc)
    (h : GoInterface) (X Y : IProp GF) : Persistent (hooksReq γ P Pk b t h X Y) := by
  unfold hooksReq; infer_instance

/-- **A commit's request** `X ⇒ Y` (D22 the stored-index window, 2026-10-23): a plain wand (the
commit only passes `X` along), or a request the backend's hooks serve (`hooksReq`; a commit runs
its hook exactly once, `batchTxBuffered.unsafeCommit`). -/
def commitReq (γ : BNames) (P : BParams) (Pk : IProp GF) (b : Loc) (X Y : IProp GF) :
    IProp GF :=
  iprop(□ (X -∗ Y) ∨ ∃ (t : Loc) (h : GoInterface), bF go!"batchTx" b ↦□ t ∗
    bF go!"hooks" b ↦□ h ∗ hooksReq γ P Pk b t h X Y)

instance commitReq_persistent (γ : BNames) (P : BParams) (Pk : IProp GF) (b : Loc)
    (X Y : IProp GF) : Persistent (commitReq γ P Pk b X Y) := by
  unfold commitReq; infer_instance

/-- No request. -/
theorem commitReq_true (γ : BNames) (P : BParams) (Pk : IProp GF) (b : Loc) :
    ⊢ commitReq (GF := GF) γ P Pk b iprop(True) iprop(True) := by
  unfold commitReq
  ileft
  iintro !> -
  itrivial

/-- The backend's metrics fields (atomics). -/
def metricsInv (b : Loc) : IProp GF :=
  iprop(inv (bN.@"metrics") iprop(∃ (a c d e : w64), bF go!"size" b ↦ a ∗
    bF go!"sizeInUse" b ↦ c ∗ bF go!"commits" b ↦ d ∗ bF go!"openReadTxN" b ↦ e))

instance metricsInv_persistent (b : Loc) : Persistent (metricsInv (GF := GF) b) := by
  unfold metricsInv; infer_instance

/-- `b` is a backend with parameters `P`, ghost names `γ`, the client's batch-lock resources
`W` (the lock holder's) and `Pk` (the hooks') (persistent). -/
def isBackend (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) : IProp GF :=
  iprop(□ ∃ (t rt tm db lg : Loc) (h : GoInterface),
    bF go!"batchTx" b ↦□ t ∗ bF go!"readTx" b ↦□ rt ∗ bF go!"batchLimit" b ↦□ P.limit ∗
    bF go!"lg" b ↦□ lg ∗ ⌜lg ≠ Loc.null⌝ ∗ bF go!"hooks" b ↦□ h ∗ beOf t ↦□ b ∗
    rtmuOf (baseOf rt) ↦□ tm ∗ hooksSpec γ P Pk b t h ∗
    sync.isMutex (muOf t) (batchFree γ P W Pk b t) ∗
    sync.isRWMutexGuard (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    sync.isRWMutexGuard tm (fun q => tmTok γ q) ∗
    sync.isMutex (cmuOf b) (cacheRes γ P b) ∗ cacheInv γ ∗ metricsInv b ∗
    sync.isRWMutexGuard (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
    isDB db ∗ ⌜P.Wf⌝)

instance isBackend_persistent (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    Persistent (isBackend γ P W Pk b) := by
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
  iprop(∃ (rt : Loc) (rd : RdSt) (H : GMap (w64 × Nat) RView) (L : VData), bF go!"readTx" b ↦□ rt ∗
    sync.ownRWMutexRLocked (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    rtResAt γ P rt sync.rfrac rd rv H (L := L) ∗ ⌜rd.rtx = rtx⌝ ∗ crTok γ b)

/-- The shared read transaction held with the share `p` of bbolt's transaction (`rtHeld` holds
`sync.rfrac.half`; a part lent to another reader of the same snapshot, `rtHeld_lend`: the restore
plan's R5b). -/
def rtHeldF (γ : BNames) (P : BParams) (b : Loc) (rtx : Loc) (rv : RView) (p : Qp) : IProp GF :=
  iprop(∃ (rt : Loc) (rd : RdSt) (H : GMap (w64 × Nat) RView) (L : VData), bF go!"readTx" b ↦□ rt ∗
    sync.ownRWMutexRLocked (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    rtResAt γ P rt sync.rfrac rd rv H p L ∗ ⌜rd.rtx = rtx⌝ ∗ crTok γ b)

theorem rtHeld_eq (γ : BNames) (P : BParams) (b : Loc) (rtx : Loc) (rv : RView) :
    rtHeld (GF := GF) γ P b rtx rv = rtHeldF γ P b rtx rv sync.rfrac.half := rfl

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

/-- `q` plus `n` shares `s`. -/
def qpRep (q s : Qp) : Nat → Qp
  | 0 => q
  | n + 1 => qpRep q s n + s

theorem qpRep_val (q s : Qp) : ∀ n : Nat, (qpRep q s n).val = q.val + n * s.val
  | 0 => by simp [qpRep]; grind
  | n + 1 => by
    simp only [qpRep, Qp.val_add, qpRep_val q s n]
    have : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by norm_cast
    rw [this]
    grind

/-- The open token at a sum is its parts. -/
theorem bOpen_add (γ : BNames) (p q : Qp) :
    bOpen (GF := GF) γ (p + q) ⊣⊢ bOpen γ p ∗ bOpen γ q := by
  unfold bOpen
  rw [Qp_half_add]
  have ho := (dghostVar_fractional (GF := GF) γ.opn false).fractional p.half q.half
  have hc := (ghostVar_fractional (GF := GF) γ.cls ()).fractional p q
  constructor
  · iintro ⟨Ho, Hc⟩
    icases ho.1 $$ Ho with ⟨Ho1, Ho2⟩
    icases hc.1 $$ Hc with ⟨Hc1, Hc2⟩
    iframe
  · iintro ⟨⟨Ho1, Hc1⟩, Ho2, Hc2⟩
    isplitl [Ho1 Ho2]
    · iapply ho.2; iframe
    · iapply hc.2; iframe

/-- `q` and `n` shares `s` of the open token, as one share. -/
theorem bOpen_rep (γ : BNames) (q s : Qp) : ∀ n : Nat,
    bOpen (GF := GF) γ (qpRep q s n) ⊣⊢ bOpen γ q ∗ [∗list] _x ∈ List.replicate n (), bOpen γ s
  | 0 => by
    simp only [qpRep, List.replicate]
    constructor
    · iintro H; iframe H; iapply BigSepL.bigSepL_nil.2; itrivial
    · iintro ⟨H, -⟩; iexact H
  | n + 1 => by
    simp only [qpRep, List.replicate]
    refine (bOpen_add (GF := GF) (hG := hG) γ _ s).trans ?_
    constructor
    · iintro ⟨H, Hs⟩
      icases (bOpen_rep γ q s n).1 $$ H with ⟨Hq, Hr⟩
      iframe Hq
      iapply BigSepL.bigSepL_cons.2
      iframe Hs Hr
    · iintro ⟨Hq, Hr⟩
      icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hs, Hr⟩
      iframe Hs
      iapply (bOpen_rep γ q s n).2
      iframe Hq Hr

/-- **The whole open token is the constructors' half and every reader's share** (W7). -/
theorem bOpen_one_shares (γ : BNames) :
    bOpen (GF := GF) γ 1 ⊣⊢ bOpen γ (1 : Qp).half ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), bOpen γ rdOpen := by
  have h : qpRep (1 : Qp).half rdOpen (Int.toNat sync.rwmutex.actualMaxReaders) = 1 := by
    apply Subtype.ext
    rw [qpRep_val]
    have := sync.actualMaxReaders_ge_2
    have hN : ((Int.toNat sync.rwmutex.actualMaxReaders : Nat) : Rat) ≠ 0 := by
      exact_mod_cast (show Int.toNat sync.rwmutex.actualMaxReaders ≠ 0 by omega)
    simp only [rdOpen, Qp.val_divide_even, Qp.val_half, Qp.val_one]
    grind
  have hr := bOpen_rep (GF := GF) (hG := hG) γ (1 : Qp).half rdOpen
    (Int.toNat sync.rwmutex.actualMaxReaders)
  rw [h] at hr
  exact hr

end shares

end backend
end EtcdGrove
end Perennial
