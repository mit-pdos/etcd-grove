/-
The pure model of the backend's buffers (`tx_buffer.go`). Lean-first (no Rocq counterpart); see
`notes/decisions.md`, "The backend: the buffers".

**Entries.** A bucket buffer holds a list of entries `(key, value)` (byte strings), in the order
they were added (`bucketBuffer.add`). Keys are compared as Go compares byte strings
(`go.GoStringLt`, what `bytes.Compare` decides).

**The canonical form.** `canon l` is `l` sorted by key, stably, keeping the last of the entries
of each key (`sort.Stable` then `dedupe`'s loop): the bucket as a map from a key to its newest
value, as a strictly increasing list. A read buffer's buckets are canonical (`entsSorted`);
`merge` and `writeback` produce `canon` of the old entries followed by the new ones.

**Range.** `bbRange es key endKey limit` is what `bucketBuffer.Range` returns of a sorted
buffer: from the first entry not below `key`, that entry if it is `key` (no `endKey`), or the
entries below `endKey`, at most `limit` of them.

**The buffers.** A write buffer (`txWriteBuffer`) is `WBuf`: its buckets' entry lists by bucket
id and its `bucket2seq` flags; a read buffer (`txReadBuffer`) is `RBuf`: its buckets and its
version. `wbPut`, `wbReset`, `rbReset`, `writebackR`/`writebackW` are the code's transitions.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-! ## Keys -/

/-- Go's `<` on byte strings. -/
abbrev strLt (a b : GoString) : Prop := go.GoStringLt a b

theorem strLt_irrefl (a : GoString) : ¬ strLt a a := by
  induction a with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | cons h => exact ih h
    | rel h => exact Int.lt_irrefl _ h

theorem strLt_trans {a b c : GoString} (h1 : strLt a b) (h2 : strLt b c) : strLt a c := by
  induction h1 generalizing c with
  | nil => cases h2 <;> exact List.Lex.nil
  | cons h ih =>
    cases h2 with
    | cons h' => exact List.Lex.cons (ih h')
    | rel h' => exact List.Lex.rel h'
  | rel h =>
    cases h2 with
    | cons _ => exact List.Lex.rel h
    | rel h' => exact List.Lex.rel (Int.lt_trans h h')

theorem strLt_asymm {a b : GoString} (h : strLt a b) : ¬ strLt b a :=
  fun h' => strLt_irrefl _ (strLt_trans h h')

/-- Go's `<` on strings is total. -/
theorem strLt_eq_of_not_lt {a b : GoString} (h1 : ¬ strLt a b) (h2 : ¬ strLt b a) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => exact absurd (List.Lex.nil : go.GoStringLt [] (y :: ys)) h1
  | cons x xs ih =>
    cases b with
    | nil => exact absurd (List.Lex.nil : go.GoStringLt [] (x :: xs)) h2
    | cons y ys =>
      have hxy : x = y := by
        apply BitVec.eq_of_toNat_eq
        have a1 : ¬ (uint.Z x < uint.Z y) := fun h => h1 (List.Lex.rel h)
        have a2 : ¬ (uint.Z y < uint.Z x) := fun h => h2 (List.Lex.rel h)
        simp only [uint.Z] at a1 a2
        omega
      subst hxy
      rw [ih (fun h => h1 (List.Lex.cons h)) (fun h => h2 (List.Lex.cons h))]

/-! ## Entries -/

/-- An entry of a bucket buffer: a key and its value. -/
abbrev Ent := GoString × GoString

/-- Entries strictly increasing by key (a canonical bucket). -/
def entsSorted (es : List Ent) : Prop := es.Pairwise (fun a b => strLt a.1 b.1)

/-- The comparison `sort.Stable` sorts a bucket buffer by (`bucketBuffer.Less` is `<` on keys):
`a` may stay before `b` unless `b`'s key is below `a`'s. -/
def entLe (a b : Ent) : Bool := !decide (strLt b.1 a.1)

/-- `dedupe`'s loop on a list sorted by key: of each run of entries with one key, the last. -/
def dedupLast : List Ent → List Ent
  | [] => []
  | [e] => [e]
  | e :: f :: rest => if e.1 = f.1 then dedupLast (f :: rest) else e :: dedupLast (f :: rest)

/-- The canonical form of a list of entries: sorted stably by key, the newest entry of each
key kept (`sort.Stable` then `dedupe`). -/
def canon (es : List Ent) : List Ent := dedupLast (es.mergeSort entLe)

/-- The newest value of `k` among the entries (the last entry with that key). -/
def lastVal (es : List Ent) (k : GoString) : Option GoString :=
  (es.reverse.find? (fun e => decide (e.1 = k))).map Prod.snd

/-- `bucketBuffer.Range(key, endKey, limit)` of a sorted buffer: from the first entry not below
`key` (`sort.Search`), that entry if its key is `key` and `endKey` is empty, else the entries
below `endKey`, at most `limit` (none if `limit ≤ 0`). -/
def bbRange (es : List Ent) (key endKey : GoString) (limit : w64) : List Ent :=
  match es.dropWhile (fun e => decide (strLt e.1 key)) with
  | [] => []
  | e :: rest =>
    if endKey = [] then (if e.1 = key then [e] else [])
    else ((e :: rest).takeWhile (fun e => decide (strLt e.1 endKey))).take (sint.Z limit).toNat

/-! ## The write buffer -/

/-- A write buffer (`txWriteBuffer`): each bucket's entries since the last write-back, by bucket
id, and the `bucket2seq` flags (`false`: the bucket was written by `put`, not only `putSeq`). -/
structure WBuf where
  bks : GMap w64 (List Ent)
  seq : GMap w64 Bool

/-- What `put` and `putSeq` may add without breaking the write-back's assumption: a bucket
written by `put` has distinct keys; one written by `putSeq` only (no flag, or `true`) strictly
increasing ones (`writeback` neither sorts nor deduplicates it). -/
def wbBucketOk (seq : Option Bool) (es : List Ent) : Prop :=
  if seq = some false then (es.map Prod.fst).Nodup else entsSorted es

/-- Every bucket of a write buffer is as `wbBucketOk` says. -/
def WBuf.Wf (W : WBuf) : Prop := ∀ id es, W.bks.lookup id = some es → wbBucketOk (W.seq.lookup id) es

/-- `WBuf.Wf` relaxed where `D` allows it: a bucket written by `put` may repeat a key (the
write-back deduplicates a bucket the read buffer lacks: `writeback`'s `!ok` branch calls
`dedupe`, so `D id` is "the read buffer has no bucket `id`" there; see
`issues/etcd-backend-duplicate-put-stale-read.md`). -/
def WBuf.WfR (W : WBuf) (D : w64 → Prop) : Prop :=
  ∀ id es, W.bks.lookup id = some es →
    wbBucketOk (W.seq.lookup id) es ∨ (W.seq.lookup id = some false ∧ D id)

/-- The entries of a bucket (none if absent). -/
def bkOf (B : GMap w64 (List Ent)) (id : w64) : List Ent := (B.lookup id).getD []

/-- `putInternal(bucket, k, v)`: the entry appended to the bucket's (a new bucket if absent). -/
def wbAdd (B : GMap w64 (List Ent)) (id : w64) (e : Ent) : GMap w64 (List Ent) :=
  B.insert id (bkOf B id ++ [e])

/-- `put`: the bucket flagged as written by `put`, and the entry added. -/
def WBuf.put (W : WBuf) (id : w64) (e : Ent) : WBuf :=
  { bks := wbAdd W.bks id e, seq := W.seq.insert id false }

/-- `putSeq`: the entry added (the flag unchanged). -/
def WBuf.putSeq (W : WBuf) (id : w64) (e : Ent) : WBuf :=
  { W with bks := wbAdd W.bks id e }

/-- `txBuffer.reset`: the buckets with no entries dropped, the others emptied. -/
def bksReset (B : GMap w64 (List Ent)) : GMap w64 (List Ent) :=
  (B.filter (fun _ es => !es.isEmpty)).fmap (fun _ => [])

/-- `txWriteBuffer.reset`: the buckets reset; a flag kept (as `true`: its bucket is empty) only
for a bucket that stays. -/
def WBuf.reset (W : WBuf) : WBuf :=
  let B := bksReset W.bks
  { bks := B, seq := (W.seq.filter (fun id _ => decide (id ∈ B))).fmap (fun _ => true) }

/-! ## The read buffer -/

/-- A read buffer (`txReadBuffer`): each bucket's written-back entries, and the version
`writeback` increments. -/
structure RBuf where
  bks : GMap w64 (List Ent)
  ver : w64

/-- A read buffer's buckets are canonical. -/
def RBuf.Wf (R : RBuf) : Prop := ∀ id es, R.bks.lookup id = some es → entsSorted es

/-- `txReadBuffer.reset` (`txBuffer.reset` of its buckets; the version unchanged). -/
def RBuf.reset (R : RBuf) : RBuf := { R with bks := bksReset R.bks }

/-- A map built from a function on the keys of another (`fmap` with the key). -/
def gmapImap {V V' : Type} (f : w64 → V → V') (m : GMap w64 V) : GMap w64 V' :=
  ⟨fun k => (m.lookup k).map (f k),
   by
    obtain ⟨l, hl⟩ := m.finite
    exact ⟨l, fun k h => hl k (by simpa using h)⟩⟩

/-- The read buffer's buckets after `writeback`: each bucket of the write buffer canonical with
its entries after the read buffer's (none if the read buffer has no such bucket); the others
as they were. -/
def wbMerge (W R : GMap w64 (List Ent)) : GMap w64 (List Ent) :=
  GMap.union (gmapImap (fun id es => canon (bkOf R id ++ es)) W) R

/-- `writeback`'s read buffer: the buckets merged, the version incremented. -/
def writebackR (W : WBuf) (R : RBuf) : RBuf :=
  { bks := wbMerge W.bks R.bks, ver := R.ver + W64 1 }

/-- `writeback`'s write buffer: the buckets the read buffer did not have moved to it (dropped
here), then `reset`. -/
def writebackW (W : WBuf) (R : RBuf) : WBuf :=
  WBuf.reset { W with bks := W.bks.filter (fun id _ => decide (id ∈ R.bks)) }

/-- The size bound of the buffers (`bucketBuffer.add` grows a buffer to `3/2` of its length:
the entries of one bucket, written back or pending, stay below `2^60`). -/
def bufBound : Nat := 2 ^ 60

end backend
end EtcdGrove
end Perennial
