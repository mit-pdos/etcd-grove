/-
`(*v2stats.LeaderStats).Follower(name)` (`leader.go`; rafthttp stage 6b, `Transport.AddPeer`):
translated with its body since D43 M5a (2026-10-26; the trust boundary until then).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `ls.Follower(name)` of the stats `ls`, with their followers' map (`v2stats.lsFollowers`, the
caller's: the transport's write lock): a non-nil `*FollowerStats` (the follower's, made and stored
if new, under the stats' lock), the map given back. (Until D43 M5a, 2026-10-26, an axiom with
`ls ≠ null` only.) -/
abbrev v2stats.LeaderStats.Follower.spec : Prop :=
  ∀ (ls : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗
      v2stats.isLeaderStats ls ∗ v2stats.lsFollowers ls 1 }}
    (App (Val (ls @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.LeaderStats.ty @!! go!"Follower")) (Val #name))
  {{ (fs : Loc), RET #fs; ⌜fs ≠ null⌝ ∗ v2stats.lsFollowers ls 1 }}

end spec

end EtcdGrove
end Perennial
