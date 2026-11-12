/-
The KV's `Read`/`Write`/`End` over either store (`kv_Read`, `kv_Write`, `tw_End`).

Obsolete at strict M1 (2026-11-05): over mvcc's internals (`isKV`, `twWrap`, the watchable store's writer). Kept as an empty module importing
txn's vocabulary over the API so that its importers build; their uses move to: `mvcc.api.isMvcc` and the contracts from `mvcc.api.shapes.law` (`txn.isMvcc_shape`, `txn.mvccTxn_shape`, `txn.end_read`, `txn.end_write`)
(`notes/mvcc-migration/txn.md`, "Renamed and replaced").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas
