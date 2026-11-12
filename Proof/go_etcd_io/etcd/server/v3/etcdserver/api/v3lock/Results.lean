/-
**The Lock service's server's results** (the auth plan's A3c, 2026-10-24; `notes/decisions.md`,
"A3c of the auth plan: Lock and Election"): `Lock` and `Unlock`, linked, with `#print axioms` of
each. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Link

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace v3lock

#print axioms lockServer.wp_Lock
#print axioms lockServer.wp_Unlock

end v3lock
end EtcdGrove
end Perennial
