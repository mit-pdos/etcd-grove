/- Lean-first (no Rocq counterpart).

`server.inCluster(c)` (`examples/etcd/dist/server`): `true` only if an entry of `c`'s initial cluster (the
`server.Peer`s `pl`, read-only) is `c`'s own name and peer address.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

/-- See the file header. -/
abbrev inCluster.spec : Prop :=
  ∀ (cv : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Config)
    (pl : List github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Peer),
  {{ (cv.Cluster' ↦*□ pl : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.inCluster)) (Val #cv))
  {{ (b : Bool), RET #b; ⌜b = true → ∃ p ∈ pl, p.Name' = cv.Name' ∧ p.Addr' = cv.Peer'⌝ }}

end spec

end server
end etcd_dist
end EtcdGrove
end Perennial

end
