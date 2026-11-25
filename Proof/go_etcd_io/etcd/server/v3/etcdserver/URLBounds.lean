/- Lean-first (no Rocq counterpart).

# etcd's URL bounds

The bounds the server's proofs take on a member's URLs: how many URLs a member has (its peer list,
its client list) and how long each URL string is. They keep the strings etcd joins from them
(`publishV3`'s attributes, rafthttp's `setPeerURLsHeader`) below `strings.Join`'s length bound.
`etcd_safe`'s deployment check gives them (`Deployment.WellFormed.urlBounds`, `DeploymentDefs.lean`).
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- **The most URLs of one member** in a list etcd joins (its peer URLs, its client URLs). -/
def etcdURLCountMax : Nat := 64

/-- **The longest URL string** of a member, in bytes. -/
def etcdURLLenMax : Nat := 1024

end EtcdGrove
end Perennial

end
