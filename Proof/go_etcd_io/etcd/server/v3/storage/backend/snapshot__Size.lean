/-
The trust boundary: `Spec/go_etcd_io/etcd/server/v3/storage/backend/snapshot__Size.lean`
(`snapshot.Size` is bbolt's `Tx.Size`, promoted; names only). D22 S-h, 2026-10-20;
`notes/decisions.md`, "D22 S-h carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Size

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

/-- **Trust boundary** (D22 S-h): bbolt's `Tx.Size()` returns `int64(tx.meta.Pgid()) *
int64(tx.db.pageSize)`, reading only the open transaction's own meta copy and the database's page
size (set once at `Open`); it writes nothing. What would discharge it: bbolt's `Tx` model with
`snapOpen` made concrete (the transaction's fields and its meta page). -/
axiom backend.snapshot.Size.wp_proof : backend.snapshot.Size.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
