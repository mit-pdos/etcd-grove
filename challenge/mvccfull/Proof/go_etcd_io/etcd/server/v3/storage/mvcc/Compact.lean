/-
Compaction, the pure model (`key_index.go`'s `compact`/`keep`/`doCompact`, `index.go`'s
`Compact`/`Keep`): a key index compacted at a revision `c`, what it still answers, and the
revisions compaction keeps in the bucket. Lean-first; `notes/decisions.md`, "mvcc: compaction".

**The key index** (`kiCompact c ki`, mirroring `keyIndex.compact`): `doCompact` walks the
generations from the oldest while the generation is not the last and its tombstone's main is
below `c` (`compactGenIdx`), then, in that generation, finds the last revision with main at or
below `c` (`genWalk … (pAbove c)`, the walk `get` uses): the revision is *available* (kept in the
bucket, `kiAvail`), the generation is cut to start at it, and the earlier generations are
dropped. `keep` (the hash's) makes the same choice but does not keep a tombstone that ends a
generation that is not the last (`kiKeep`; the asymmetry the code documents).

**What a compacted key index answers** (`kiGet_kiCompact`): at every revision at or above `c`,
what the uncompacted one does; a compaction that empties it (`treeIndex.Compact` then deletes
the key) leaves nothing to answer there (`kiGet_of_kiCompact_empty`). Compactions compose
(`kiCompact_kiCompact`, `kiCompact_kiCompact_le`), compaction at `-1` changes nothing
(`kiCompact_neg`), and compaction commutes with the writer's next event, which is above `c`
(`kiCompactO_step`).

**The index** (`IdxCRep cmax evs idx`): the tree holds, for every key, its key index of the
events compacted at a level of its own (`-1 ≤ c ≤ cmax`: the job compacts key by key, under the
index lock each time), or nothing if that compaction emptied it. At revisions at or above `cmax`
the index answers what the uncompacted index does (`IdxCRep.kiAt`, `IdxCRep.rangeAt`).

**The bucket** (`KeyDel log c key`): the bucket keys compaction at `c` may delete: a revision
with main at or below `c` that compaction does not keep. A read at or above `c` never names one
(`named_not_del`), also when revision `c` deletes a key and puts it again: the fixed `doCompact`
(etcd-io/etcd#22377) steps past the tombstone to the put that follows it in the same revision
(before the fix it kept the tombstone and dropped the key's live revision,
`issues/etcd-compaction-delete-then-put.md`, and the premise `NoDelPutAt` excluded the case, until
M2's item 18); so the compacted store's readers name no deleted key (`rangeAnswers_not_del`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ### Bounds -/

/-- A compaction revision (`-1`: none) as a natural number, for the monotone counter. -/
def crevN (c : Int) : Nat := (c + 1).toNat

/-! ### The key index (`key_index.go`) -/

/-- The main of a generation's last revision (its tombstone, for one that is not the last). -/
def tombZ (g : Gen) : Int := sint.Z (g.revs.getLastD Rev.zero).main

/-- `generation.isRecreatedAt(rev)`: not empty, its first revision's main is `rev`. -/
def genRecreatedAt (atRev : w64) (g : Gen) : Bool :=
  match g.revs with
  | [] => false
  | r :: _ => decide (sint.Z r.main = sint.Z atRev)

/-- **`doCompact` steps past `g`** (followed by `g'`): its tombstone is below `atRev`, or at `atRev`
with `g'` re-created in that revision (the key deleted and put again in it: the put, at a higher
sub revision, supersedes the tombstone; etcd-io/etcd#22377, the fork's `goose-lean-compactfix`,
M2, 2026-10-28; until then `doCompact` stopped at a tombstone at `atRev`). -/
def genAdv (atRev : w64) (g g' : Gen) : Bool :=
  decide (tombZ g < sint.Z atRev) || (decide (tombZ g = sint.Z atRev) && genRecreatedAt atRev g')

/-- `doCompact`'s generation: from the oldest, the first that is the last one or that `doCompact`
does not step past (`genAdv`). -/
def compactGenIdx (atRev : w64) : List Gen → Nat
  | [] => 0
  | [_] => 0
  | g :: g' :: gs => if genAdv atRev g g' then compactGenIdx atRev (g' :: gs) + 1 else 0

/-- The revision `doCompact` adds to `available`: compaction keeps it in the bucket. -/
def kiAvail (atRev : w64) (ki : KeyIndex) : Option Rev :=
  let g := ki.gens.getD (compactGenIdx atRev ki.gens) Gen.empty
  let ri := genWalk g.revs (pAbove atRev)
  if ri = -1 then none else some (g.revs.getD ri.toNat Rev.zero)

/-! ### Proof helpers: the structure of a log's key index, the scan, the walk, the cut -/

/-! ### Helpers -/

/-! ### The events of a log: strictly increasing revisions -/

/-! ### The key index of a log's events: its structure -/

/-! ### Derived facts of the structure -/

/-! ### The walk -/

/-! ### Dropping a prefix after setting its last element -/

/-! ### Compaction, piece by piece -/

/-! ### Consequences: (b), no compaction, composition, the last generation -/

/-! ### Compaction and the writer's next event -/

/-! ### The theorems, for a log's key index -/

/-! ### What compaction keeps -/

/-! ### The index: every key compacted at a level of its own -/

/-! ### The bucket: what compaction keeps, what it may delete -/

/-- Compaction at `c` keeps the revision `r`: some key's `doCompact` makes it available. -/
def keepAt (log : Log) (c : Int) (r : Rev) : Prop :=
  ∃ k, kiAvail (W64 c) (kiOfKey (evsOf log) k) = some r

/-- **A bucket key compaction at `c` may delete** (of a log with revision `c`): a revision's
bytes, with a main at or below `c`, that compaction does not keep (what the job deletes: the
keys of the range `[_, c + 1)` not in `treeIndex.Compact`'s `available`). A read at or above
`c` never names one (`named_not_del`; before the fork's fix, etcd-io/etcd#22377, it could when
revision `c` deletes and puts a key again: `issues/etcd-compaction-delete-then-put.md`). -/
def KeyDel (log : Log) (c : Int) (key : GoString) : Prop :=
  c < log.length ∧
    ∃ (r : Rev) (t : Bool), key = revBytes r t ∧ 0 ≤ sint.Z r.main ∧ sint.Z r.main ≤ c ∧
      ¬ keepAt log c r

/-! ### Compaction-aware readers (2026-10-13, unit 6a)

A read at or
above a compaction revision `c'` names no key compaction at `c'` deletes, of any certified log
agreeing with the reader's up to `c'` (`rangeAnswers_not_del`: `named_not_del` through the
prefix order). -/

end mvcc
end EtcdGrove
end Perennial
