/-
mvccfull's members (`notes/mvccfull-proof-plan.md`, "Draft (F1): the invariants in full", M).
Lean-first (no Rocq counterpart).

**A member's incarnation invariant** (`memberInv`, one per incarnation of a member: its store
between two restarts; namespace `memberN i`): until the writer retires it at a restart, the store's
state `σ` (`mvccState γk σ`; the writer, the only thread whose updates change `σ`, holds the other
half of `m.σ`), the four bound atomics (`1 ≤ revLo ≤ σ.rev ≤ revHi < 2 ^ 62`, `cmpLo ≤ σ.crev ≤
cmpHi`, the writer holding the other half of their values `m.bnd`; `revLo ≥ 1` for `watch`'s floating
window, the ceiling for a watcher's start and revision, kept by the writer from `Ops < 2 ^ 38`), the
monotone revision, compaction revision and notified log's length (a value read at `t₁` is at most
an upper bound loaded at `t₂ > t₁`: the notified length, `|σ.notifiedLog| ≤ revHi + 1`, bounds a
response at the pending revision, which `revHi` alone cannot since it goes back down after a
transaction without changes), and a lower bound of the shared
history covering the notified history (`histOkM`); the global history changes each key at most once
per revision (`onceUpToAll`), which the watch guarantee needs.

**Retirement** (a cancelable invariant): the invariant holds its contents or the incarnation's
retirement token (`ghostVar ret 1 ()`), which the writer holds while the incarnation lives. At a
restart, every reader and stream of the incarnation has ended (`stopReaders`, `endEpoch`), and
each had, besides the persistent handles (`isInc`), a share of the retirement token (a live share
rules the retired case out, so a goroutine may open the invariant), a reader token and a share of
the member's `kv` field (`incRd`), all returned through the wait groups; with the whole token back
the writer swaps it in and takes the contents out: the closed store's state for
`mvccImage_stop.law`, and the atomics, counters and `m.σ`'s half, which go into the next
incarnation's invariant. The incarnation's store name `γk` is a parameter: each reader and stream is
handed its incarnation's handles when started (no ghost state stores a store name, which is not
countable).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WatchModel
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.GhostVar
public import Perennial.Proof.sync.atomic.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model

/-- **Every revision of `L` changes each key at most once** (the generated log's invariant: a
transaction's puts are distinct and outside its deletes, a delete repeats nothing, a revoke's keys
are distinct). -/
def onceUpToAll (L : Log) : Prop :=
  ∀ r : Nat, ((L.getD r []).map Change.key).Nodup

/-- It gives the watch guarantee's condition at any first revision and compaction revision. -/
theorem onceUpTo_of_all {L : Log} (h : onceUpToAll L) (lo : Nat) (c : Int) : onceUpTo L lo c :=
  fun r _ _ => h r

end model

/-- **A member's ghost names** (across its incarnations). -/
structure MemberNames where
  /-- the store's state (an incarnation's invariant's half, the writer's half) -/
  σ : GName
  /-- the store's revision, monotone (auth in the incarnation's invariant) -/
  rev : GName
  /-- the store's compaction revision plus one, monotone (auth in the incarnation's invariant) -/
  crev : GName
  /-- the length of the store's notified log, monotone (auth in the incarnation's invariant): a
  notify adds one, a commit, a compaction or a `Restore` (a longer log, nothing pending) keeps or
  grows it, a restart keeps it (the reopened store has the closed one's log) -/
  nrev : GName
  /-- the bound atomics' values `(revLo, revHi, cmpLo, cmpHi)` (the invariant's half, the writer's) -/
  bnd : GName

/-- **An incarnation's names**: its store's, and its retirement token's. -/
structure IncNames where
  kv : MvccName
  ret : GName

/-- **The tester's ghost names.** -/
structure FullNames where
  h : HistNames
  m0 : MemberNames
  m1 : MemberNames

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A field of a member. -/
abbrev mF (f : GoString) (mp : Loc) : Loc := structFieldRef member f mp

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The members' invariants' namespace (member `i`: `0` the leader, `1` the follower, `2` the
builder, which has no invariant). -/
def memberN (i : Nat) : Namespace := ((nroot .@ "mvccfull") .@ "member") .@ toString i

/-- The bound atomics' values. -/
abbrev Bnd := w64 × w64 × w64 × w64

/-- **An incarnation's contents** (see the file header). `ks` the run's keys, `γh` the history's
names. -/
def memberState (ks : List GoString) (γh : HistNames) (mp : Loc) (m : MemberNames) (γk : MvccName) :
    IProp GF :=
  iprop(∃ (σ : MvccState) (b : Bnd) (Hl : List HRev),
    mvccState γk σ ∗ ghostVar m.σ (1 : Qp).half σ ∗
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

/-- **An incarnation's invariant** (cancelable; see the file header). -/
def memberInv (ks : List GoString) (γh : HistNames) (mp : Loc) (m : MemberNames) (ι : IncNames) :
    IProp GF :=
  iprop(memberState ks γh mp m ι.kv ∨ ghostVar ι.ret 1 ())

/-- **An incarnation's handles** (persistent): its invariant and its store's handle `kv`, the
member's `kv` field holding it (read-only for the incarnation's life: the writer alone writes it,
at a restart, after every reader and stream of the incarnation ended). -/
def isInc (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) : IProp GF :=
  iprop(inv (memberN i) (memberInv ks γh mp m ι) ∗ isMvcc kv ι.kv)

/-- **A goroutine's part of an incarnation** (exclusive, at the share `q`; a reader's, `Readers.lean`'s
`rdOwn`): its handles, one reader token of its store, the share `q` of the incarnation's retirement
token (so that it may open the invariant: a live share rules the retired case out) and of the
member's `kv` field (which it reads: the writer writes it only at a restart, once every share is
back). Returned at the goroutine's end through its wait group. -/
def incRd (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames)
    (ι : IncNames) (kv : GoInterface) (q : Qp) : IProp GF :=
  iprop(isInc ks γh i mp m ι kv ∗ mvccReaders ι.kv 1 ∗ ghostVar ι.ret q () ∗
    mF go!"kv" mp ↦{DFrac.own q} kv)

end defs

end mvccfull
end EtcdGrove
end Perennial
