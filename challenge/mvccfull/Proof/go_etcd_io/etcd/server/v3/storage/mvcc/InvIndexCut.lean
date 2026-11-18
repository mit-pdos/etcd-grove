/-
**The index at a full revision** (`notes/m2-storage-plan.md`, "The index at a full revision (branch
m2-index)"; the user's decision B1 after review round 5): a key index cut at a full revision (a main
and a sub-revision), the pure facts about it, and the index invariant over such cuts (`IdxCRepN`), up
to the unread header of a tombstone-only generation (`kiNorm`). Lean-first, pure.

**Why a full revision.** `restore()` rebuilds the index from the `Key` bucket, which a compaction job
may have thinned in batches (`scheduleCompaction`): a batch can stop between two sub-revisions of
one main revision, and one main revision can change a key twice (a put and a delete in sibling
transactions, `issues/etcd-txn-check-intervals-sibling.md`). The rebuilt key index then starts at
the key's first surviving revision, which no compaction at a *main* revision gives
(`M2StorageDraftIndex.lean`'s `cx3_not_compacted`). So the invariant's per-key level is a revision
of the key: the key index is the log's with every revision before that one dropped (`kiCutAt`, the
position of the revision in the key index: its generation `gi` and its index `j` there), at or
before what compaction at some `c ≤ cmax` keeps (`CutLe`). A compaction at `c` is such a cut
(`kiCompact_eq_cutAt`); a compaction at `c' ≥ c` erases the difference (`kiCompact_cutAt`); a reader
at or above `c` cannot tell (`kiGet_cutAt`); and neither can `doCompact`'s and `keep`'s choices
(`kiAvail_cutAt`, `kiKeep_cutAt`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## The cut -/

/-- A generation without its first `j` revisions (the header kept). -/
def genDrop (j : Nat) (g : Gen) : Gen := { g with revs := g.revs.drop j }

/-- **A key index cut at a full revision**, the revision at position `j` of generation `gi`: the
generations before `gi` dropped, generation `gi` cut to start at that revision (its header kept),
the later ones and `modified` unchanged. `kiCompact` is the cut at the position `doCompact` picks
(`kiCompact_eq_cutAt`). -/
def kiCutAt (gi j : Nat) (ki : KeyIndex) : KeyIndex :=
  { ki with gens := (ki.gens.set gi (genDrop j (ki.gens.getD gi Gen.empty))).drop gi }

/-- The cut, or nothing if it is empty (`treeIndex` has no such key). -/
def kiCutO (gi j : Nat) (ki : KeyIndex) : Option KeyIndex :=
  if kiIsEmpty (kiCutAt gi j ki) then none else some (kiCutAt gi j ki)

/-- The revision index `doCompact` cuts its generation at (`0` if the walk finds none). -/
def cmpRevIdx (c : w64) (ki : KeyIndex) : Nat :=
  (genWalk (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs (pAbove c)).toNat

/-- **The position `(gi, j)` is at or before the one compaction at `c` cuts at**: a revision of an
earlier generation, or of `doCompact`'s generation at or before its revision. -/
def CutLe (c : w64) (ki : KeyIndex) (gi j : Nat) : Prop :=
  (gi < compactGenIdx c ki.gens ∧ j < (ki.gens.getD gi Gen.empty).revs.length) ∨
    (gi = compactGenIdx c ki.gens ∧ j ≤ cmpRevIdx c ki)

/-! ## Compaction above the cut -/

/-! ## Readers above the cut -/

/-! ## The writer's next event on the cut -/

/-! ## Key indexes up to the unread header of a tombstone-only generation -/

/-- **A generation's unread header cleared**: a generation with one revision gets `created := 0`,
`ver := 1`, the values `restoreTombstone` gives it. Applied to the generations that are not the last
(`kiNorm`), whose one revision is their tombstone: `kiGet` never answers it (`kiGet_kiNorm`), and
compaction and `keep` read only revisions. -/
def genNorm (g : Gen) : Gen :=
  if g.revs.length = 1 then { g with created := W64 0, ver := W64 1 } else g

/-- **A key index up to the unread headers**: every generation but the last normalized. -/
def kiNorm (ki : KeyIndex) : KeyIndex :=
  { ki with gens := ki.gens.dropLast.map genNorm ++ ki.gens.getLast?.toList }

/-! ### What reads the key index sees no difference -/

/-! ### The writer's steps and compaction, up to the headers -/

/-! ## The index: every key cut at a full revision of its own -/

/-- **The index holds the events `evs`, each key cut at a full revision of its own** (up to the
unread headers): for every key, a level `c` with `-1 ≤ c ≤ cmax` and a revision of the key at or
before the one compaction at `c` keeps (`CutLe`), the tree's key index being the log's with every
revision before that one dropped (`kiCutAt`), absent if that leaves nothing (`kiCutO`); equal up to
the header of a tombstone-only generation that is not the last (`kiNorm`). A compaction at `c` is
the cut at the revision it keeps (`IdxCRepN_of`); `restore()` over a bucket a compaction job thinned
cuts at each key's first surviving revision (`InvIndexRestore.lean`'s `idxRestore_cut`). The lock's
invariant (`idxLockInv`'s `HL`). -/
def IdxCRepN (cmax : Int) (evs : List Ev) (idx : IndexM) : Prop :=
  idx.Pairwise idxLess ∧
    ∀ k, ∃ c : Int, -1 ≤ c ∧ c ≤ cmax ∧ ∃ gi j, CutLe (W64 c) (kiOfKey evs k) gi j ∧
      (idxGet idx k).map kiNorm = (kiCutO gi j (kiOfKey evs k)).map kiNorm

