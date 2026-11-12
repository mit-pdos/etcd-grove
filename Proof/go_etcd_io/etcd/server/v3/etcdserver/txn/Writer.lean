/-
The sole writer's resources over the KV (`kvWriter`).

Obsolete at strict M1 (2026-11-05): over mvcc's internals (`kvWriter`: the store's writer fragments, the sole writer's tokens). Kept as an empty module importing
txn's vocabulary over the API so that its importers build; their uses move to: the caller's `mvcc.api.mvccState` in its own invariant, and txn's updates `txn.readAU`/`txn.txnBeginAU`/`txn.putAU`/`txn.delAU`
(`notes/mvcc-migration/txn.md`, "Renamed and replaced").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas
