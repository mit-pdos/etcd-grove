/-
The key index (`index.go`): a `treeIndex` is a btree of `*keyIndex` (the verified k8s btree,
`cache/v3/InvBtree.lean`) under a `sync.RWMutex`. Lean-first (no Rocq counterpart).

**Representation.** The btree's items are the `*keyIndex` pointers, modelled with their keys
(`kiItemIs p (p, k)`: `kiKey`, persistent) and ordered by key (`kiItemLess`); the mutable part
of each key index (`ownKi`) is held beside the tree. `ownTree t L q` holds both at fraction `q`
for the entries `L` (pointer, key, model). It is `Fractional` (through the btree's
`ownBTree_combine`), so it can be the resource of the `RWMutex`.

**The lock invariant** (`idxLockInv`) ties the tree to the index's *history* (`Hist.lean`): the
tree holds `indexOf` of the events of `ilog ++ [pend]`, where `ilog` is the log the writer had
committed and `pend` the pending revision's changes it had put, at the last write; a lower bound
of the history ghost (`monoListLbOwn γ.hist (histShape ilog pend)`) and the number of events
(`monoNatAuthOwn γ.nev`, at the lock's fraction) record it. The **writer** (`idxWriter γ ilog
pend`, held by the store's write transaction: the batch lock serializes writers) owns the
history's authority and a lower bound of the count. Committing a revision is a ghost step
(`idxWriter_commit`, outside the index lock: `storeTxnWrite.End` does not take it), which yields
the **certificate** `idxCert γ log` of the committed log: its history is a prefix of the index's.
A **reader** (`idxReader`: one of the `RWMutex`'s reader tokens) with the certificate of `log₀`
reads at a revision below `log₀.length` what `log₀` determines (`reader_answer`): the index's
history is comparable with `histOf log₀`, and either `log₀`'s events are a prefix (later events
have higher mains: `kiGet_reader`) or the index has exactly `log₀`'s events (the count).
-/
module

public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.cache.v3.InvBtree
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.GhostVar
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexCut
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ### Countability (for the history ghost) -/

def Rev.enc (r : Rev) : w64 × w64 := (r.main, r.sub)

theorem Rev.enc_inj : Function.Injective Rev.enc :=
  sorry

instance Rev.countable : Pos.Countable Rev :=
  .ofInjective (fun r => Pos.Countable.encode r.enc) (fun _ _ h => Rev.enc_inj (Pos.encode_inj h))

def Change.enc : Change → Bool × GoString × GoString × w64
  | .put k v l => (false, k, v, l)
  | .del k => (true, k, [], W64 0)

theorem Change.enc_inj : Function.Injective Change.enc :=
  sorry

instance Change.countable : Pos.Countable Change :=
  .ofInjective (fun c => Pos.Countable.encode c.enc) (fun _ _ h => Change.enc_inj (Pos.encode_inj h))

def Ev.enc (e : Ev) : Rev × (Bool × GoString × GoString × w64) := (e.rev, e.change.enc)

theorem Ev.enc_inj : Function.Injective Ev.enc :=
  sorry

instance Ev.countable : Pos.Countable Ev :=
  .ofInjective (fun e => Pos.Countable.encode e.enc) (fun _ _ h => Ev.enc_inj (Pos.encode_inj h))

def HistItem.enc : HistItem → Option Ev
  | .ev e => some e
  | .commit => none

theorem HistItem.enc_inj : Function.Injective HistItem.enc :=
  sorry

instance HistItem.countable : Pos.Countable HistItem :=
  .ofInjective (fun x => Pos.Countable.encode x.enc)
    (fun _ _ h => HistItem.enc_inj (Pos.encode_inj h))

section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ### The btree's items: `*keyIndex` pointers, by key -/

/-- The btree's item type: `*keyIndex`. -/
abbrev kiPtrT : go.GoType := go.GoType.PointerType keyIndex.ty

/-- The model of an item: the pointer and its key. -/
abbrev KiItem := Loc × GoString

/-- `p` is the item `(p, k)`: a `*keyIndex` with key `k`. -/
def kiItemIs (p : Loc) (v : KiItem) : IProp GF := iprop(⌜p = v.1⌝ ∗ kiKey p v.2)

instance kiItemIs_persistent (p : Loc) (v : KiItem) : Persistent (kiItemIs (GF := GF) p v) :=
  sorry

/-! ### The tree's fractions: `ownBTree` split, `ownKi` split and combine -/

/-! ### The tree with its key indexes -/

/-- An entry's key index: its pointer (not `nil`) and its mutable part, at fraction `q`. -/
def ownEntry (z : IdxEntry) (q : Qp) : IProp GF :=
  iprop(⌜z.1 ≠ null⌝ ∗ ∃ gs : GoSlice, ownKi z.1 gs z.2.2 (DFrac.own q))

/-- The tree at `t` and its key indexes hold the entries `L` (keys strictly increasing), at
fraction `q`. -/
def ownTree (t : Loc) (L : List IdxEntry) (q : Qp) : IProp GF :=
  iprop(⌜(itemsOfEntries L).Pairwise kiItemLess⌝ ∗
    ownBTree kiPtrT t kiItemIs kiItemLess (itemsOfEntries L) (DFrac.own q) ∗
    [∗list] z ∈ L, ownEntry z q)

/-! ### The lock invariant, the writer and the certificate -/

/-- The ghost names of a tree index: its history, its number of events, and the committed log
(a monotone list of the revisions' changes: the history records the events, not the values, so
the certificate carries the log itself through this one); and the store's compaction revision
(`crev`, a monotone counter of `crevN c`: its authority is split between the store's two locks
and the compaction right, `InvStore.lean`; the index's lock keeps a lower bound of every key's
compaction level, `idxLockInv`). -/
structure IdxNames where
  hist : GName
  nev : GName
  log : GName
  crev : GName
  /-- the compactor's state (`ghostVar (Int × List Loc)`: the revision of the last compaction and
  the key indexes a compaction in progress has yet to visit), half in the lock's resource
  (`idxCmpOwn`), half the compactor's (`idxCompactor`) -/
  cmp : GName

/-- The writer's log, well formed and bounded: `ilog` committed, `pend` pending. -/
def IdxWf (ilog : Log) (pend : List Change) : Prop :=
  LogWf' (ilog ++ [pend]) ∧ ilog.length + 1 < 2 ^ 63 ∧ pend.length < 2 ^ 63 ∧
    ∀ cs ∈ ilog, cs.length < 2 ^ 63

/-- Part `q` of the compaction revision's authority, at `c` (`-1`: none): whoever holds a part
knows the compaction revision is `c` (the store's locks and the compaction right hold the
parts). -/
def crevUB (γ : IdxNames) (q : Qp) (c : Int) : IProp GF := monoNatAuthOwn γ.crev q (crevN c)

/-- A lower bound `c` of the compaction revision (persistent). -/
def crevLb (γ : IdxNames) (c : Int) : IProp GF := monoNatLbOwn γ.crev (crevN c)

/-- **The compactor's state in the lock's resource** (at the lock's fraction `q`, half of it):
the revision `cc` of the last compaction, at or above every key's level (`cmax`), and the key
indexes `P` a compaction in progress has yet to visit, all in the tree (no one but the compactor
removes them: replacing a key index, `Insert`, needs no compaction, `cmax < 0`). -/
def idxCmpOwn (γ : IdxNames) (q : Qp) (L : List IdxEntry) (cmax : Int) : IProp GF :=
  iprop(∃ (cc : Int) (P : List Loc), ghostVar γ.cmp q.half (cc, P) ∗
    ⌜cmax ≤ cc ∧ (∀ p ∈ P, p ∈ L.map Prod.fst) ∧ (P ≠ [] → 0 ≤ cmax)⌝)

/-- The `RWMutex`'s resource at fraction `q` (see the module docstring): the tree holds the
events of `ilog ++ [pend]`, each key's index cut at a full revision of its own, at or before what
compaction at a level at most `cmax` keeps, up to the unread header of a tombstone-only generation
(`IdxCRepN`, `InvIndexCut.lean`: the compaction job compacts key by key under the lock, and
`restore()` over a bucket a job thinned rebuilds each key from its first surviving revision), `cmax` a
lower bound of the compaction revision, below the length of a lower bound of the committed log (so below
every writer's next revision). -/
def idxLockInv (t : Loc) (γ : IdxNames) (q : Qp) : IProp GF :=
  iprop(∃ (ilog : Log) (pend : List Change) (L : List IdxEntry) (cmax : Int),
    "#Hhist" ∷ monoListLbOwn γ.hist (histShape ilog pend) ∗
    "Hnev" ∷ monoNatAuthOwn γ.nev q (evsOf (ilog ++ [pend])).length ∗
    "Htree" ∷ ownTree t L q ∗
    "#Hcrev" ∷ crevLb γ cmax ∗
    "#Hcl" ∷ (∃ log₀ : Log, monoListLbOwn γ.log log₀ ∗ ⌜cmax < log₀.length⌝) ∗
    "%HL" ∷ ⌜IdxCRepN cmax (evsOf (ilog ++ [pend])) (idxOfEntries L) ∧ -1 ≤ cmax⌝ ∗
    "%Hwf" ∷ ⌜IdxWf ilog pend⌝ ∗
    "Hcmp" ∷ idxCmpOwn γ q L cmax)

end reprs

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of the embedded `RWMutex`. -/
abbrev idxMuAddr (ti : Loc) : Loc := structFieldRef treeIndex go!"RWMutex" ti

end addrs

section reprs2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A tree index (persistent): its tree and logger (a zap logger: `Compact` logs; premise fixes 6), and the lock's guard (writers lock through
it). -/
def isTreeIndex (ti : Loc) (γ : IdxNames) : IProp GF :=
  iprop(∃ (t lg : Loc),
    "#Htree" ∷ ti.[treeIndex, go!"tree"] ↦□ t ∗
    "#Hlg" ∷ ti.[treeIndex, go!"lg"] ↦□ lg ∗
    "#Hlgnn" ∷ zapLoggerOk lg ∗
    "#Hmu" ∷ sync.isRWMutexGuard (idxMuAddr ti) (idxLockInv t γ))

/-- A reader's token: one of the `RWMutex`'s bounded reader slots (`RLock` needs one). -/
def idxReader (ti : Loc) (γ : IdxNames) : IProp GF :=
  iprop(∃ t : Loc, ti.[treeIndex, go!"tree"] ↦□ t ∗ sync.ownRWMutex (idxMuAddr ti) (idxLockInv t γ))

/-- The committed log's authority at fraction `q`: half is the writer's (`idxWriter`), half
is kept elsewhere (the store's `s.revMu`), so that a reader of the committed log there finds
every certificate below it (`idxLogAuth_cert_prefix`). -/
abbrev idxLogAuth (γ : IdxNames) (q : Qp) (log : Log) : IProp GF := monoListAuthOwn γ.log q log

/-- The number of changes of a log (`txn.logChanges`). -/
def logCh (log : Log) : Nat := (log.map List.length).sum

/-- **The index had all the events of `log`** (persistent; a lower bound of the index's event
count, a physical name: D22 receiver epochs, S1): what a certificate no longer says. The store's
`s.revMu` keeps it of the committed log, and a read transaction of the log it read. -/
def idxNevLb (γ : IdxNames) (log : Log) : IProp GF := monoNatLbOwn γ.nev (evsOf log).length

/-- The writer's handle: the history's authority (`ilog` committed, `pend` put so far), a
lower bound of the event count at its last write, and half the committed log's authority; and
(D19b, 2026-10-18) a time receipt per change of the log and the pending revision, so that a sealed
log has fewer changes than the receipts' bound: since M2's B2 (2026-11-01) a **persistent** one
(`⧖`, a lower bound of the one global step counter), which each change raises by a Go step of the
call that puts it (`treeIndex.Put`/`Tombstone`, `wp_raise_receipt`). Persistent, so that it can
travel with a snapshot image to the member that restores it (`notes/m2-storage-plan.md`, "B2 by
sealed logs"): an exclusive one cannot. -/
def idxWriter (γ : IdxNames) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop(monoListAuthOwn γ.hist 1 (histShape ilog pend) ∗
    monoNatLbOwn γ.nev (evsOf (ilog ++ [pend])).length ∗ ⌜IdxWf ilog pend⌝ ∗
    idxLogAuth γ (1 : Qp).half ilog ∗ ⧖ (logCh ilog + pend.length))

/-- The writer's handle once **sealed**: the pending revision `pend` (not empty) is final, its
commit marker already in the history (so the history's lower bound `histOf (ilog ++ [pend])`
is persistent before the commit, which needs `s.revMu`'s half of the committed log); the
committed log's authority is still at `ilog` until the commit (`idxWriterSealed_commit`). The
watchable store seals before it notifies the watchers of the revision. -/
def idxWriterSealed (γ : IdxNames) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop(monoListAuthOwn γ.hist 1 (histOf (ilog ++ [pend])) ∗
    monoNatLbOwn γ.nev (evsOf (ilog ++ [pend])).length ∗ ⌜IdxWf ilog pend ∧ pend ≠ []⌝ ∗
    idxLogAuth γ (1 : Qp).half ilog ∗ ⧖ (logCh ilog + pend.length))

/-- The writer's handle, sealed or not. -/
def idxWriterB (γ : IdxNames) (ilog : Log) (pend : List Change) (sealed : Bool) : IProp GF :=
  if sealed then idxWriterSealed γ ilog pend else idxWriter γ ilog pend

/-- A **sealed** log (unit W-M2b): its history is a prefix of the index's, and it is well
formed and bounded (`idxCert` without the committed log's lower bound and the events' count: a
revision is sealed before it is committed, `idxWriter_seal`, so this is what the watchers'
deliveries certify). Two sealed logs are in prefix order (`idxSealed_prefix`). Not a floor for
reads: a sealed log need not be committed yet (`idxCert` is). Its changes are fewer than the
time receipts' bound (D19b: the writer held a receipt per change when it sealed it): since M2's B2
(2026-11-01) the persistent receipt `⧖ (logCh log)` itself, which implies it (`idxSealed_small`). -/
def idxSealed (γ : IdxNames) (log : Log) : IProp GF :=
  iprop(monoListLbOwn γ.hist (histOf log) ∗
    ⌜LogWf' log ∧ log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63⌝ ∗
    ⧖ (logCh log))

/-- The certificate of a committed log `log`: its history is a prefix of the index's, and `log`
is a prefix of the committed log (so two certificates are of logs in prefix order:
`idxCert_prefix`). It names only the store's logical names (the history and the committed log),
not the index's event count (D22 receiver epochs, S1, 2026-10-22: the count is per index, and a
restore builds a new index; that the index had all the log's events is `idxNevLb`, which a
reader learns under the lock that pins the current index, `idxKnows`). -/
def idxCert (γ : IdxNames) (log : Log) : IProp GF :=
  iprop(monoListLbOwn γ.hist (histOf log) ∗
    ⌜LogWf' log ∧ log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63⌝ ∗
    monoListLbOwn γ.log log ∗ ⧖ (logCh log))

/-! ### What a reader of the index knows -/

end reprs2

end mvcc
end EtcdGrove
end Perennial
