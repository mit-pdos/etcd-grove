/-
The writer's shared definitions (`writer`, `examples/mvccrand/mvccrand.go`). Lean-first (no Rocq
counterpart).

- **The struct** (`writerRO`): every field but `vals` and `nextID` is written once, when `runChecks`
  makes the writer, and read by the writer and (`ticks`) the registering goroutine: persistent
  points-tos. `vals` and `nextID` are the writer's (`newVal`, `grant`).
- **The pending model of a write transaction** (`pendOf`): the tester's state and changes after
  mvcc's changes `cs` of revision `rev` from the state `M`, a put as `pending.put`, a delete of one
  key as `pending.del`'s. A pending transaction's model is `pendOf` of the last revision's state and
  the transaction's changes (`pendOk`), and so is each revision of the history (`revOk`, `World.lean`).
- **`end`'s callback** (`endCb`): what `w.end(p, end)` needs of `end` (`tw.End`, or `revoke`'s
  closure): given the writer's half of the store's ghost state, the store's state committed.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.World

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A field of the writer's struct. -/
abbrev wF (f : GoString) (w : Loc) : Loc := structFieldRef writer f w

end addrs

section model
variable [GooseExts]

/-- **A pending transaction's model is the tester's** (inside a write transaction begun at `σ`, the
history at `Hs`, mvcc's pending changes `pend`): `pendOf` of the last revision's state, and the
state it holds is the store's after the pending changes. -/
def pendOk (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM) : Prop :=
  P = pendOf (lastSt Hs) (W64 (Hs.length : Int)) pend ∧
  stMatch P.st (applyChanges (W64 (σ.log.length : Int)) (stateAfter σ.log) pend)

/-- The history after `end`: the pending revision appended if it has a change. -/
def histAfter (Hs : List HRev) (P : PendM) : List HRev :=
  if P.chs = [] then Hs else Hs ++ [(P.st, P.chs)]

/-- The store's state after the writer's transaction (`σ` with nothing pending, `pend` committed). -/
def commitSt (σ : MvccState) (pend : List Change) : MvccState :=
  (σ.notify pend).commitPending

/-- What `view` returns: the states (the pending one appended once it has a change), their
fractions, and the revision a read in the transaction is at. -/
def viewSt (Hs : List HRev) (P : PendM) : List (GMap GoString kvRec) :=
  Hs.map Prod.fst ++ (if P.chs = [] then [] else [P.st])

def viewDq (Hs : List HRev) (P : PendM) : List DFrac :=
  List.replicate Hs.length DFrac.discard ++ (if P.chs = [] then [] else [DFrac.own 1])

def viewRev (P : PendM) : w64 := if P.chs = [] then P.rev - W64 1 else P.rev

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The writer's struct, its fields written once** (persistent): all but `vals` and `nextID`. -/
def writerRO (w : Loc) (wv : writer) : IProp GF :=
  iprop(wF go!"kv" w ↦□ wv.kv' ∗ wF go!"le" w ↦□ wv.le' ∗ wF go!"h" w ↦□ wv.h' ∗
    wF go!"r" w ↦□ wv.r' ∗ wF go!"leases" w ↦□ wv.leases' ∗ wF go!"applying" w ↦□ wv.applying' ∗
    wF go!"saved" w ↦□ wv.saved' ∗ wF go!"ticks" w ↦□ wv.ticks')

instance writerRO_persistent (w : Loc) (wv : writer) : Persistent (writerRO (GF := GF) w wv) := by
  unfold writerRO; infer_instance

/-- What the tester's post-lock hook needs, at the index `i` being applied (`applying`) and the one
saved `s` (`saved`, `s ≤ i`): both counters. -/
def hookPre (wv : writer) (i s : w64) : IProp GF :=
  iprop(sync.atomic.ownInt64 wv.applying' (DFrac.own 1) i ∗ sync.atomic.ownInt64 wv.saved' (DFrac.own 1) s ∗
    ⌜sint.Z s ≤ sint.Z i⌝)

/-- What it gives: the batch lock's invariant (`True`: the tester's backend has none) and the
counters, `saved` at `i`. -/
def hookPost (wv : writer) (i : w64) : IProp GF :=
  iprop(sync.atomic.ownInt64 wv.applying' (DFrac.own 1) i ∗ sync.atomic.ownInt64 wv.saved' (DFrac.own 1) i)

/-- **The tester's hook `f`** (persistent): the triple of its closure at every index. -/
def hookOk (wv : writer) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ i s, hookRun iprop(True) f (hookPre wv i s) iprop(True ∗ hookPost wv i))

/-- **The writer's context** (persistent): the packages, the struct's fixed fields, the tester's and
the history's invariants, the store's handle, the backend's hook (frozen at `f`) and its triple. -/
def writerCtx (w : Loc) (wv : writer) (γ : RandNames) (B : MvccStorage) (f : GoFunc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
    writerRO w wv ∗ inv worldN (worldInv wv.h' γ) ∗ isHistory wv.h' γ.h ∗ isMvcc wv.kv' γ.kv ∗
    hookIs B f ∗ hookOk wv f)

/-- **The writer's own state between operations** (exclusive): its thread token, its share of the
store's backend (the batch lock's invariant `True`), its reader slot of the history, the store at
`σ` and the history at `Hs` (`writerIdle`), its generator, and the leases: the model's live leases
`Lm` (a map to `true`), mvcc's lease ownership at the live leases `L` (the same) and the items of
the store's state. -/
def writerOwn (wv : writer) (γ : RandNames) (B : MvccStorage) (q : Qp) (σ : MvccState) (Hs : List HRev)
    (L : List w64) : IProp GF :=
  iprop(threadTok ∗ mvccBackend γ.kv q B iprop(True) ∗ histRd wv.h' γ.h ∗ writerIdle γ σ Hs ∗
    (∃ g : rng, wv.r' ↦ g) ∗
    (∃ Lm : GMap w64 Bool, wv.leases' ↦$ Lm ∗ ⌜∀ id, (Lm !! id).isSome = true ↔ id ∈ L⌝) ∗
    lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log []))

/-- **`end`'s callback** (see the file header): from the writer's half of the store's ghost state at
`σ` (nothing pending) and a lower bound of the history `Hs'` with the transaction's revision, the
store's state committed (`commitSt σ pend`), the thread token back; `E`/`E'` the caller's. -/
def endCb (e : GoFunc) (γ : RandNames) (σ : MvccState) (pend : List Change) (Hs' : List HRev)
    (E E' : IProp GF) : IProp GF :=
  iprop(∀ Φ, ghostVar γ.σ (1 : Qp).half σ ∗ monoListLbOwn γ.h.l Hs' ∗ E -∗
    ▷ (ghostVar γ.σ (1 : Qp).half (commitSt σ pend) ∗ threadTok ∗ E' -∗ Φ #()) -∗
    WP (App (Val #e) (Val #())) {{ Φ }})

end defs

end mvccrand
end EtcdGrove
end Perennial
