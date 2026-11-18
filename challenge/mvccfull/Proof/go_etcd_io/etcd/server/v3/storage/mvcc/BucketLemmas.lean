/-
The bucket's entries of the answers of a range read: every answer `(key, (mod, created, ver))`
of `rangeAnswers` at a revision `r` of a well-formed log is the state's key-value of `key` at
`r` (`kiGet_indexOf`), and the bucket holds that key-value, encoded, at the bytes of `mod`
(`BucketHas`, `bucketMap`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## Words -/

/-! ## The map built from the bucket's entries -/

/-! ## The encoding is injective -/

/-! ## The bucket's entry of a change -/

/-! ## The limited answers -/

/-! ## Filling a slice of pointers in order -/

/-! ## The answers of a range read -/

/-! ### The pending revision grows: well-formedness -/

/-! ## The write transaction: the pending revision -/

/-- The entries a write transaction has put: the pending revision's. -/
def pendPuts (ilog : Log) (pend : List Change) : List (GoString × GoString) :=
  bucketOfRev ilog.length (stateAfter ilog) pend

end mvcc
end EtcdGrove
end Perennial
