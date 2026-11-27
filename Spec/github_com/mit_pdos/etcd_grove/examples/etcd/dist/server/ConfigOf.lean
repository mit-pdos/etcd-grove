/- Lean-first (no Rocq counterpart).

`server.ConfigOf(d, i)` (`examples/etcd/dist/server`): member `i`'s configuration of the deployment held by the
Go value `v` (`deploymentRepr`): `configRepr` (`MemberDefs.lean`), its initial cluster a fresh slice of every
member's entry, read-only. At most `typed.maxMembers` members (`WellFormed`'s bound; `append` needs fewer than `2 ^ 63`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MemberDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

/-- See the file header. -/
abbrev ConfigOf.spec : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment) (i : Nat) (m : Member),
  d.members[i]? = some m → d.members.length ≤ typed.maxMembers →
  {{ deploymentRepr (GF := GF) v d }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.ConfigOf)) (Val #v))
      (Val #(W64 i)))
  {{ (cv : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Config), RET #cv;
      configRepr (GF := GF) cv d i }}

end spec

end server
end etcd_dist
end EtcdGrove
end Perennial

end
