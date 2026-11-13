/-
`Put`/`DeleteRange`/`Range` at the sole writer (`put_soleWriter_of`, ...).

Obsolete at strict M1 (2026-11-05): over mvcc's internals (`soleWriter`, `kvWriter`, `idxCert`). Kept as an empty module importing
txn's vocabulary over the API so that its importers build; their uses move to: the specs themselves: the pin is the caller's `R`/`Q`
(`notes/mvcc-migration/txn.md`, "Renamed and replaced").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas
