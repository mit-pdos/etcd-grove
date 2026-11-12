/-
The trust boundary: `wal.ValidSnapshotEntries` (names-only; WAL W4a, 2026-11-11, revised after the Freeze review and its second and third rounds). An axiom: why the statement is true
of the Go code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

axiom wal.ValidSnapshotEntries.wp_proof : wal.ValidSnapshotEntries.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
