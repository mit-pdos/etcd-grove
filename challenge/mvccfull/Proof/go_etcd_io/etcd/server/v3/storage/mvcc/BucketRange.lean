/-
A range read of the backend's `Key` bucket (`UnsafeRange(schema.Key, lo, hi, 0)`, the watchable
store's `rangeEvents`): the entries of the bucket whose key is in `[lo, hi)`, in key order. Keys
are bytes ordered lexicographically (`go.GoStringLt`: bbolt's cursor order, Perennial's
`bytes.Compare`). Lean-first; `notes/decisions.md`, "The watchable store's concurrency (unit 3)".

`bucketRange m klo khi` is a pure function (the map's entries filtered and sorted); it is
characterized by its members and its keys strictly increasing (`bucketRange_eq_iff`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- The entries of the bucket `m` whose key is in `[klo, khi)`, in key order (`go.GoStringLt`,
lexicographic on bytes). -/
def bucketRange (m : GMap GoString GoString) (klo khi : GoString) : List (GoString × GoString) :=
  (m.toList.filter fun p => decide (go.GoStringLe klo p.1) && decide (go.GoStringLt p.1 khi)).mergeSort
    fun a b => decide (go.GoStringLe a.1 b.1)

/-! Go's `≤` on strings. -/

end mvcc
end EtcdGrove
end Perennial
