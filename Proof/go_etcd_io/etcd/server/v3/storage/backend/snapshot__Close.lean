/-
The trust boundary: `Spec/go_etcd_io/etcd/server/v3/storage/backend/snapshot__Close.lean`
(`snapshot.Close`, translated, over the opaque `snapOpen`). D22 S-h, 2026-10-20;
`notes/decisions.md`, "D22 S-h carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Close

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **Trust boundary** (D22 S-h): `(*snapshot).Close()` closes `stopc` (made by `Snapshot`,
closed only here), waits for `donec` (closed by `Snapshot`'s warning goroutine when it sees
`stopc` closed) and returns `s.Tx.Rollback()`, which for a read-only transaction still open (its
`db` set: `snapOpen`, consumed here, so `Close` runs once) releases it (`nonPhysicalRollback`) and
returns nil; bbolt returns an error (`ErrTxClosed`) only for a transaction already closed. So the
`lg.Panic` on a failed close in `newSnapshotReaderCloser` is not reached. What would discharge it:
`snapOpen` made concrete (the snapshot's fields, the stop/done channels with the warning
goroutine's protocol, and bbolt's read transaction open), over which the translated body is
proved with bbolt's `Tx.Rollback`. -/
axiom backend.snapshot.Close.wp_proof : backend.snapshot.Close.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
