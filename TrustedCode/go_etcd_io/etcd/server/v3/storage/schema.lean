/-
Trusted code for `go.etcd.io/etcd/server/v3/storage/schema`, in namespace `go_etcd_io.etcd.server.v3.storage.schema` like the generated package (`Code/go_etcd_io/etcd/server/v3/storage/schema.toml`): its `init`
function, which the model skips: its docstring says why that is unobservable to the
translated code (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace go_etcd_io.etcd.server.v3.storage.schema

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `go.etcd.io/etcd/server/v3/storage/schema`'s `init` (etcd `edc800c6f262`) at `bucket.go:61`: for
each bucket of `AllBuckets` (a slice literal of ten `bucket` values) whose `IsSafeRangeBucket()` is
true, `backend.RegisterSafeRangeBucket(bk.Name())`, which stores the name in the `sync.Map`
`backend.safeRangeBucketNames` (`batch_tx.go:56-61`). It cannot panic: the loop ranges over a
fixed ten-element slice of non-nil interface values whose methods only read a field, and
`sync.Map.Store` of a string key does not panic. No translated code reads what it writes: the
registry is read only by `isRegisteredSafeRangeBucket` (`batch_tx.go:63`), called only by the
backend's defragmentation (`backend.go:898, 988`), which is not translated; `safeRangeBucketNames`,
`RegisterSafeRangeBucket` and `isRegisteredSafeRangeBucket` are names only in the translation of
`backend`. The model does nothing (etcd-grove#32; until 2026-11-23 the trust-boundary axiom
`initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end

end go_etcd_io.etcd.server.v3.storage.schema

end Perennial
