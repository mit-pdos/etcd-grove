/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the cluster's size bound

`typed.maxMembers`, Go's `deployment.MaxMembers`, in a module of its own: the deployment's
well-formedness (`DeploymentDefs.lean`) bounds the members by it, and the interim axiom
`bootstrap.wp_proof_dist` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapDist.lean`) takes the
initial cluster's size below it, without importing the deployment's definitions.
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace typed

/-- The cluster's size bound (Go's `deployment.MaxMembers`). -/
def maxMembers : Nat := 1000

end typed
end etcd_dist
end EtcdGrove
end Perennial

end
