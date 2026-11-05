/-
The writer's pin observing the backend's keys (`kvWriter_keyObs`).

Obsolete at strict M1 (2026-11-05): over mvcc's internals (`writerPin`, `kvWriter`). Kept as an empty module importing
txn's vocabulary over the API so that its importers build; their uses move to: `mvcc.api.mvccImage_snapshot.law`
(`notes/mvcc-migration/txn.md`, "Renamed and replaced").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas
