/-
The results of etcd's gRPC KV service (`server/v3/etcdserver/api/v3rpc`: the handlers of
`key.go`, the request checks, the response header, `togRPCError`), restated at top level, with
the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart); plan: `notes/decisions.md`, "The request path".

A skeleton (unit 0, 2026-10-12): nothing of the package is proved yet. Planned (unit 1): the
seven checks as pure results over `Defs.lean`'s functions (`rangeCheck`, ..., `opCheck`,
`ivCheck`), `check_gives_nodup` (`intervalsOkCheckStmt` proved: a transaction passing
`checkIntervals`, with no from-key delete and no later-sibling delete of a nested put, writes
each key at most once), `checkRequestOp_nonempty` (the txn package's empty-`RequestOp`
precondition discharged), the header and the five handlers over `isRaftKV`'s triples (the
server's request path, units 2 and 3). Until then the linked results are the trust boundary's.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

#print axioms Perennial.EtcdGrove.v3rpc.status.wp_Error
#print axioms Perennial.EtcdGrove.v3rpc.status.wp_Errorf
#print axioms Perennial.EtcdGrove.v3rpc.errors.wp_Is

end EtcdGrove
end Perennial
