/-
The trust boundary:
`Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__snapshotDefragmented.lean`
(`backend.snapshotDefragmented` is names only: its body creates a temporary file with
`os.CreateTemp`, opens a temporary bbolt database `tmpdb`, runs `bolt.Compact(tmpdb, b.db, ...)`
outside the batch lock, begins a read transaction on `tmpdb`, and starts `newSnapshot`'s warning
goroutine; `etcd#21776`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__snapshotDefragmented

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **Trust boundary** (`etcd#21776`, mirroring `backend.Snapshot.wp_proof` in
`backend__Snapshot.lean`): `b.snapshotDefragmented(defragTxMaxBytes)` commits the batch transaction
(`b.batchTx.Commit()`, consuming `wbTok γ`), then under `b.mu.RLock()` creates a temporary database
file, opens `tmpdb`, compacts `b.db` into `tmpdb` via `bolt.Compact(tmpdb, b.db, defragTxMaxBytes)`
(which opens a single read-only bbolt transaction on `b.db` and copies all buckets and key-value
pairs verbatim into `tmpdb`, so `tmpdb`'s committed data is identical to `b.db`'s committed data `D`
at the moment `bolt.Compact`'s read transaction on `b.db` began), and opens a read-only transaction
on `tmpdb` wrapped in `&defragmentedSnapshot{snapshot: newSnapshot(b.lg, tx), closer: ...}`. On any
filesystem or bbolt error before returning, it closes `tmpdb` (if opened), removes the temporary
file, and returns `(nil, err)`. Note: see Findings 1–3 in `notes/pr-verify/etcd-21776.md` for the
lock-holding (`b.mu.RLock()` held across `bolt.Compact`) and `bolt.Options` (`NoSync: false`)
performance/liveness defects in `snapshotDefragmented`. -/
axiom backend.backend.snapshotDefragmented.wp_proof :
    backend.backend.snapshotDefragmented.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
