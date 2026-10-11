/-
The trust base of the server's txn package's results: `#print axioms` of each. Built with the
rest; read its output to check it.

Unit 0 (translation and scaffolding): no function of the package is proved yet; `Link.lean`
links the trust-boundary axioms the package's functions call, and imports mvcc's results, of
which the read-only write transaction (`Txn`'s read-only path) is printed here. The later units
add the package's results (`txn_runTxn`, `put_putKv`, `deleteRange_filter`, the range's).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Link

@[expose] public section

/-! mvcc's read-only write transaction (`InvRoTxn.lean`), linked in mvcc's `Link.lean`. -/
#print axioms Perennial.EtcdGrove.mvcc.wp_NewReadOnlyTxnWrite
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_FirstRev
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Rev
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Range
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_End
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Changes
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_Put
#print axioms Perennial.EtcdGrove.mvcc.txnReadWrite.wp_DeleteRange
