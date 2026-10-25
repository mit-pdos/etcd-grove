/-
**The Election service's server's results** (the auth plan's A3c, 2026-10-24;
`notes/decisions.md`, "A3c of the auth plan: Lock and Election"): the handlers, linked, with
`#print axioms` of each. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Link

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace v3election

#print axioms electionServer.wp_session
#print axioms electionServer.wp_Campaign
#print axioms electionServer.wp_Proclaim
#print axioms electionServer.wp_Resign
#print axioms electionServer.wp_Leader

end v3election
end EtcdGrove
end Perennial
