/-
The trust base of every result of the mvcc KV core so far: `#print axioms` of each theorem
of `Link.lean`. Built with the rest; read its output to check it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Link

@[expose] public section

#print axioms Perennial.EtcdGrove.mvcc.Revision.wp_GreaterThan
#print axioms Perennial.EtcdGrove.mvcc.generation.wp_isEmpty
#print axioms Perennial.EtcdGrove.mvcc.generation.wp_walk
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_Less
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_isEmpty
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_findGeneration
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_get
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_put
#print axioms Perennial.EtcdGrove.mvcc.keyIndex.wp_tombstone
