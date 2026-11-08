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
size (set once at `Open`); it writes nothing. (Sweep repairs 1, S2, 2026-11-08) **The result is in
`[0, 2^62)`**: a `snapRO` is made only by `backend.Snapshot`, of an `isBackend`, whose database was
opened from a file the opener's premise says holds a database (`fileHolds path D`, `bbolt.Open_kv`;
`isBackend`'s `dbFile db path`), and is kept so by bbolt's commits. The verified bbolt's definition of
that premise (`Spec/go_etcd_io/bbolt/Api.lean`, `fileHolds`) states the file's size is below `2^62`
and the high-water mark times the page size is at most the file's length, so `Pgid() * pageSize <
2^62`. Caveat: the backend's `fileHolds` (`InvBbolt.lean`) is an axiom, linked to the verified bbolt's
definition by this argument, not by a proof. bbolt itself does not check the high-water mark against
the file at `Open` (`mmap` validates a meta's magic, version and checksum only, bbolt v1.5.0
`db.go:456-560`), so a forged file could break the bound: it is excluded by `fileHolds` (its producers:
`fileHolds_new` for the fresh data directory, `dataDirFresh`; a received snapshot's file, a bbolt image
of the sender's database; `DB.Close_kv`'s give-back). The bound is `2^62` (the file size), not
`MaxMapSize = 2^48`, which bbolt checks only when it grows a mapping, not when it opens a file. What
would discharge it: bbolt's `Tx` model with
`snapOpen` made concrete (the transaction's fields and its meta page). -/
axiom backend.snapshot.Size.wp_proof : backend.snapshot.Size.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
