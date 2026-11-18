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
public import Perennial.Golang.Defn.String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-! ## Keys -/

/-- Go's `<` on byte strings. -/
abbrev strLt (a b : GoString) : Prop := go.GoStringLt a b

/-! ## Entries -/

/-- An entry of a bucket buffer: a key and its value. -/
abbrev Ent := GoString × GoString

/-- Entries strictly increasing by key (a canonical bucket). -/
def entsSorted (es : List Ent) : Prop := es.Pairwise (fun a b => strLt a.1 b.1)

/-- The comparison `sort.Stable` sorts a bucket buffer by (`bucketBuffer.Less` is `<` on keys):
`a` may stay before `b` unless `b`'s key is below `a`'s. -/
def entLe (a b : Ent) : Bool := !decide (strLt b.1 a.1)

/-- The newest value of `k` among the entries (the last entry with that key). -/
def lastVal (es : List Ent) (k : GoString) : Option GoString :=
  (es.reverse.find? (fun e => decide (e.1 = k))).map Prod.snd

/-! ## The write buffer -/

/-- A write buffer (`txWriteBuffer`): each bucket's entries since the last write-back, by bucket
id, and the `bucket2seq` flags (`false`: the bucket was written by `put`, not only `putSeq`). -/
structure WBuf where
  bks : GMap w64 (List Ent)
  seq : GMap w64 Bool

/-- What `put` and `putSeq` may add without breaking the write-back's assumption: a bucket
written by `put` anything (the write-back deduplicates it, `dedupe`, whether or not the read
buffer has the bucket: the fork's fix of `issues/etcd-backend-duplicate-put-stale-read.md`,
etcd-io/etcd#21987); one written by `putSeq` only (no flag, or `true`) strictly increasing keys
(`writeback` neither sorts nor deduplicates it). -/
def wbBucketOk (seq : Option Bool) (es : List Ent) : Prop :=
  seq = some false ∨ entsSorted es

/-- Every bucket of a write buffer is as `wbBucketOk` says. -/
def WBuf.Wf (W : WBuf) : Prop := ∀ id es, W.bks.lookup id = some es → wbBucketOk (W.seq.lookup id) es

/-- The entries of a bucket (none if absent). -/
def bkOf (B : GMap w64 (List Ent)) (id : w64) : List Ent := (B.lookup id).getD []

/-! ## The read buffer -/

/-- A read buffer (`txReadBuffer`): each bucket's written-back entries, and the version
`writeback` increments. -/
structure RBuf where
  bks : GMap w64 (List Ent)
  ver : w64

/-- A read buffer's buckets are canonical. -/
def RBuf.Wf (R : RBuf) : Prop := ∀ id es, R.bks.lookup id = some es → entsSorted es

end backend
end EtcdGrove
end Perennial
