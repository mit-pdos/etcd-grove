/-
`(*v2stats.LeaderStats).Follower(name)`: the trust boundary (v2stats is names-only but for
`NewLeaderStats`; rafthttp stage 6b, `Transport.AddPeer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `ls.Follower(name)` of a non-nil `*LeaderStats`: a non-nil `*FollowerStats` (the follower's,
made if new, under the stats' lock). -/
abbrev v2stats.LeaderStats.Follower.spec : Prop :=
  ∀ (ls : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ ⌜ls ≠ null⌝ }}
    (App (Val (ls @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.LeaderStats.ty @!! go!"Follower")) (Val #name))
  {{ (fs : Loc), RET #fs; ⌜fs ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
