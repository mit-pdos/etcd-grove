/-
The pure model of etcd's mvcc KV core (`server/v3/storage/mvcc`): revisions, the log of
changes, the states it determines, the key index and the backend's key bucket as functions
of the log. Lean-first (no Rocq counterpart); see `notes/decisions.md`, "mvcc".

**The log.** The store's history is a log `Log`: `log[r]` are the changes of revision `r`
(`Change`: a put of a key with a value and a lease, or a delete of a key), in sub-revision
order. Revision 0 is empty, and a fresh store starts at revision 1 with no changes
(`NewStore` sets `currentRev = 1`): `[[], []]`. The state at revision `r` (`stateAt`) is the
changes of revisions `0, ..., r` applied in order, a put being the client model's `putKv`
(`InvEtcdTxn.lean`: a new key is created at `r` with version 1, an existing one keeps its
create revision and gets version + 1) and a delete removing the key. So the state is the
client model's state, and etcd's history laws (`etcdState_revs`, ...) are theorems of this
model.

**The key index** (`index.go`, `key_index.go`) is a function of the log's events (`Ev`: a
revision `(main, sub)`, a key, and whether it is a tombstone): `indexOf (evsOf log)`, the
sorted list of `(key, KeyIndex)` built by `kiPut`/`kiTombstone` event by event, as the code
does. `kiGet` mirrors `keyIndex.get` (`kiFindGen` its `findGeneration`, `genWalk` its
`walk`), and the model's main theorem (`kiGet_indexOf`, `LogLemmas.lean`) says what it returns
of a key at a revision: the key-value of the state at that revision (its mod revision, create
revision and version), or nothing if the key is absent.

**The key bucket** (the backend's `Key` bucket) maps the bytes of a revision
(`revBytes`: 8 big-endian bytes of the main, `_`, 8 of the sub, and `t` for a tombstone) to
the protobuf encoding of the key-value the change wrote (`kvEncode`, an opaque encoding:
`proto.Marshal`/`Unmarshal` are the trust boundary; a tombstone's value is the key alone,
`zeroKv`): `bucketOf log`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## Revisions -/

/-- `mvcc.Revision`: a main revision and the sub-revision of a change in it. -/
structure Rev where
  main : w64
  sub : w64
deriving DecidableEq, Inhabited

/-- The strict order on revisions `Rev.gt` decides. -/
def Rev.lt (a b : Rev) : Prop :=
  sint.Z a.main < sint.Z b.main ∨ (a.main = b.main ∧ sint.Z a.sub < sint.Z b.sub)

/-- The zero revision (`Revision{}`). -/
def Rev.zero : Rev := ⟨W64 0, W64 0⟩

/-! ## Changes and the log -/

/-- A change: a put of `key` with `value` and `lease`, or a delete of `key`. -/
inductive Change where
  | put (key value : GoString) (lease : w64)
  | del (key : GoString)

def Change.key : Change → GoString
  | .put k _ _ => k
  | .del k => k

def Change.isDel : Change → Bool
  | .put .. => false
  | .del _ => true

/-- One change of revision `r` applied to a state: a put is the client model's `putKv`, a
delete removes the key. -/
def applyChange (r : w64) (s : List EtcdKv) : Change → List EtcdKv
  | .put k v l => putKv r k v l s
  | .del k => s.filter (fun x => !decide (x.key = k))

/-- The changes of revision `r`, in order. -/
def applyChanges (r : w64) (s : List EtcdKv) (cs : List Change) : List EtcdKv :=
  cs.foldl (applyChange r) s

/-- The log: `log[r]` are the changes of revision `r`, in sub-revision order. -/
abbrev Log := List (List Change)

/-- The state after every revision of `log`. -/
def stateAfter (log : Log) : List EtcdKv :=
  log.zipIdx.foldl (fun s p => applyChanges (W64 p.2) s p.1) []

/-- The state at revision `r`: after revisions `0, ..., r`. -/
def stateAt (log : Log) (r : Nat) : List EtcdKv := stateAfter (log.take (r + 1))

/-- The key-value of `k` in a state. -/
def findKey (k : GoString) (s : List EtcdKv) : Option EtcdKv := s.find? (fun v => decide (v.key = k))

/-! ## Events: what the key index sees of a change -/

/-- An event of the key index: the revision of a change and the change itself (the key index
sees its key and whether it is a tombstone, `Ev.key`/`Ev.tomb`; the history records the change
with its value, so that a lower bound of the history determines the log: `histOf_prefix_iff`). -/
structure Ev where
  rev : Rev
  change : Change

/-- The event's key. -/
abbrev Ev.key (e : Ev) : GoString := e.change.key

/-- The event is a tombstone (a delete). -/
abbrev Ev.tomb (e : Ev) : Bool := e.change.isDel

/-- The events of revision `r`'s changes `cs`. -/
def evsOfRev (r : Nat) (cs : List Change) : List Ev :=
  cs.zipIdx.map fun p => { rev := ⟨W64 r, W64 p.2⟩, change := p.1 }

/-- The events of the whole log, in order. -/
def evsOf (log : Log) : List Ev :=
  (log.zipIdx.map fun p => evsOfRev p.2 p.1).flatten

/-! ## The key index (`key_index.go`) -/

/-- A generation of a key: its versions' revisions, the main revision it was created at and
the number of versions (`ver`); a generation ends with the tombstone that deletes the key, and
a new, empty one follows it.

`created` is the main revision only: the Go field's sub-revision is not a function of the log.
`put` records the full revision of the generation's first change, `restore` (rebuilding the
index from the backend, whose key-values keep `CreateRevision`'s main only) sub-revision `0`.
No reader looks at it (a put's `CreateRevision`, `since`'s comparison and compaction read the
main revision or the revisions), so the model leaves it out and the representation
(`ownGen`) constrains only the field's `Main` (`notes/restore-plan.md`, "R1's findings"). -/
structure Gen where
  ver : w64
  created : w64
  revs : List Rev
deriving Inhabited

def Gen.empty : Gen := { ver := W64 0, created := W64 0, revs := [] }

/-- The mutable part of a `keyIndex` (its key is fixed): the revision of its last change and
its generations, oldest first (at least one once a revision was put). -/
structure KeyIndex where
  modified : Rev
  gens : List Gen
deriving Inhabited

/-- A fresh `keyIndex{key: k}`: no generations. -/
def KeyIndex.fresh : KeyIndex := { modified := Rev.zero, gens := [] }

/-- `g.revs = append(g.revs, rev); g.ver++`, and `g.created = rev` (its main revision) if `g`
was empty. -/
def genPut (g : Gen) (rev : Rev) : Gen :=
  { ver := g.ver + W64 1, created := if g.revs = [] then rev.main else g.created,
    revs := g.revs ++ [rev] }

/-- `keyIndex.put(main, sub)` (the revision must be above `modified`): the revision is
appended to the last generation (a first one is made if there is none). -/
def kiPut (ki : KeyIndex) (rev : Rev) : KeyIndex :=
  let gens := if ki.gens = [] then [Gen.empty] else ki.gens
  { modified := rev, gens := gens.dropLast ++ [genPut (gens.getLastD Gen.empty) rev] }

/-- `keyIndex.tombstone(main, sub)` when the last generation is not empty: a put, then a new
empty generation. -/
def kiTombstone (ki : KeyIndex) (rev : Rev) : KeyIndex :=
  let ki' := kiPut ki rev
  { ki' with gens := ki'.gens ++ [Gen.empty] }

/-- `keyIndex.isEmpty()`: one generation, with no revision. -/
def kiIsEmpty (ki : KeyIndex) : Bool :=
  match ki.gens with
  | [g] => decide (g.revs = [])
  | _ => false

/-- The last generation is empty (`tombstone` then returns `ErrRevisionNotFound`). -/
def kiLastEmpty (ki : KeyIndex) : Bool :=
  decide ((ki.gens.getLastD Gen.empty).revs = [])

/-- `generation.walk(f)`: the revisions are visited from the last to the first until `f`
returns false; the position where it stopped, or `-1` if it did not. With `p` the
predicate `f` decides: the largest index whose revision fails `p`. -/
def genWalk (revs : List Rev) (p : Rev → Bool) : Int :=
  match revs.reverse.findIdx? (fun r => !p r) with
  | some i => (revs.length - 1 - i : Nat)
  | none => -1

/-- `get`'s walk predicate: the revision is above `atRev`. -/
def pAbove (atRev : w64) (r : Rev) : Bool := decide (sint.Z atRev < sint.Z r.main)

/-! ## The index (`index.go`): key indexes by key -/

/-- The index: `(key, keyIndex)` pairs, keys strictly increasing. -/
abbrev IndexM := List (GoString × KeyIndex)

/-- The btree's order on the index's items: by key (`keyIndex.Less`). -/
def idxLess (a b : GoString × KeyIndex) : Prop := go.GoStringLt a.1 b.1

instance idxLess_dec : DecidableRel idxLess := fun a b => go.goStringLt_dec a.1 b.1

/-- The key index of `k`, if any. -/
def idxGet (idx : IndexM) (k : GoString) : Option KeyIndex :=
  (btFind idxLess (k, KeyIndex.fresh) idx).map Prod.snd

/-! ## The key bucket -/

/-- The protobuf encoding of a `mvccpb.KeyValue` (`proto.Marshal`): opaque; its only
properties are the trusted specs of `Marshal` and `Unmarshal`. -/
opaque kvEncode : EtcdKv → GoString

/-- The bytes of a revision as a key of the backend's `Key` bucket (`BucketKeyToBytes`): the
main and the sub in big-endian, separated by `_`, and `t` appended for a tombstone. -/
def revBytes (rev : Rev) (tomb : Bool) : GoString :=
  u64Be rev.main ++ [W8 95] ++ u64Be rev.sub ++ (if tomb then [W8 116] else [])

/-- The key-value a change of revision `r` at position `i` of `cs` writes (`stateBefore` is
the state before the changes of `r`): for a put, the key's new key-value; for a delete, the
key alone (`zeroKv`). -/
def changeKv (r : w64) (before : List EtcdKv) (cs : List Change) (i : Nat) : Option EtcdKv :=
  match cs[i]? with
  | some (.put k _ _) => findKey k (applyChanges r before (cs.take (i + 1)))
  | some (.del k) => some (zeroKv k)
  | none => none

/-- The bucket's entries of revision `r` (changes `cs`, state `before` before them): the
bytes of each change's revision, with the encoding of what it wrote. -/
def bucketOfRev (r : Nat) (before : List EtcdKv) (cs : List Change) : List (GoString × GoString) :=
  cs.zipIdx.filterMap fun p =>
    (changeKv (W64 r) before cs p.2).map fun kv => (revBytes ⟨W64 r, W64 p.2⟩ p.1.isDel, kvEncode kv)

/-- The bucket of the whole log: the entries of every revision. -/
def bucketOf (log : Log) : List (GoString × GoString) :=
  (log.zipIdx.map fun p => bucketOfRev p.2 (stateAt log (p.2 - 1)) p.1).flatten

/-- The bucket as a map (the backend's view): the entries' keys are distinct
(`bucketOf_nodup`, `Lemmas.lean`). -/
def bucketMap (log : Log) : GMap GoString GoString :=
  (bucketOf log).foldl (fun m p => GMap.insert p.1 p.2 m) GMap.empty

/-! ## Well-formed logs -/

/-- Revision 0 is empty, and every delete is of a key present at that point (the code deletes
only keys the index finds at the revision). -/
def LogWf (log : Log) : Prop :=
  log[0]? = some [] ∧
  ∀ (r : Nat) (cs : List Change) (i : Nat) (k : GoString), log[r]? = some cs →
    cs[i]? = some (.del k) →
    (findKey k (applyChanges (W64 r) (stateAt log (r - 1)) (cs.take i))).isSome

end mvcc
end EtcdGrove
end Perennial
