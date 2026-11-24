/-
`membership.RaftCluster.Member(id)` (`cluster.go` at the etcd pin `edc800c6f`: under the lock,
`c.members[id].Clone()`), for the holder of the members' other half (`clusterMem`), at a member of the
map: its clone, with the member's values. Claim #34, stage 4 (2026-11-25; `bootstrapRaftFromCluster`'s
`json.Marshal((*cl).Member(id))`). Lean-first.

**Not proved: a hypothesis** (`?` in the server's `Link.lean`). It holds of Go: the lock's half and
`clusterMem`'s agree (`memAt_agree`), and `Clone` copies the id, the learner flag, the name and both
URL slices' elements. Its proof needs `Member.Clone.spec` to give the clone's values (it gives only its
id, `memberIs`): a stronger `Clone` spec over the same body (`Member__Clone.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev membership.RaftCluster.Member.specMem : Prop :=
  ∀ (c : Loc) (mem : GMap w64 apply.MemberM) (id : w64) (mm : apply.MemberM),
  mem !! id = some mm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c ∗ membership.clusterMem c mem }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Member")) (Val #id))
  {{ (m : Loc), RET #m;
      ∃ v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member, m ↦ v ∗
        v.RaftAttributes'.PeerURLs' ↦* mm.peerURLs ∗ v.Attributes'.ClientURLs' ↦* mm.clientURLs ∗
        ⌜v.ID' = mm.id ∧ v.RaftAttributes'.IsLearner' = mm.isLearner ∧
          v.Attributes'.Name' = mm.name⌝ ∗
        membership.clusterMem c mem }}

end spec

end EtcdGrove
end Perennial
