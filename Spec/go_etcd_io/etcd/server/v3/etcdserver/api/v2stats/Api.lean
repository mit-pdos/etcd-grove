/-
# The v2 statistics (`etcdserver/api/v2stats`): vocabulary (batch 2e)

Counters the server and its transport update (`ServerStats` on leadership changes and append
requests, `LeaderStats` with a `FollowerStats` per peer): nothing a client of etcd observes through
the v3 API, nothing a proof of the server reads back. Every spec here is "safe to call
concurrently": the statistics' own locks, read-only fields set at construction.
Translated: `NewLeaderStats`, `LeaderStats.Follower`; the rest names only (trusted; `ServerStats`
has an anonymous struct field Goose does not translate).

* `isServerStats p`, `isLeaderStats p`, `isFollowerStats p` (persistent).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V2stats

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- `p` is a `*ServerStats` (persistent). -/
opaque isServerStats (p : Loc) : IProp GF := iprop(True)

/-- `p` is a `*LeaderStats` (persistent). -/
opaque isLeaderStats (p : Loc) : IProp GF := iprop(True)

/-- `p` is a `*FollowerStats` (persistent). -/
opaque isFollowerStats (p : Loc) : IProp GF := iprop(True)

def isServerStats_persistent.spec : Prop := ∀ p, Persistent (isServerStats (GF := GF) p)
def isLeaderStats_persistent.spec : Prop := ∀ p, Persistent (isLeaderStats (GF := GF) p)
def isFollowerStats_persistent.spec : Prop := ∀ p, Persistent (isFollowerStats (GF := GF) p)

end res

end V2stats
end EtcdGrove
end Perennial
