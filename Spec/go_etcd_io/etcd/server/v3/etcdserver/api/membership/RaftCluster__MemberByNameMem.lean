/-
`membership.RaftCluster.MemberByName(name)` (`cluster.go:155-168` at the etcd pin `edc800c6f`: under the
lock, the member named `name`, cloned; `lg.Panic` if two are), for the holder of the members' other half
(`clusterMem`), when exactly one member of the map is named `name`. Claim #34, stage 4 (2026-11-25;
`bootstrapRaftFromCluster`'s `cl.MemberByName(cfg.Name)`). Lean-first.

**Not proved: a hypothesis** (`?` in the server's `Link.lean`): `MemberByName` is names-only, one of stage
2's functions (`notes/bootstrap-proof-plan.md` §3). It holds of Go: the loop over the map (the lock's half,
which agrees with `clusterMem`'s) meets the named member once (the names are distinct, so no panic) and
returns its clone (`Clone`: the id copied); the clone's other fields are returned owned.
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
abbrev membership.RaftCluster.MemberByName.specMem : Prop :=
  ∀ (c : Loc) (mem : GMap w64 apply.MemberM) (name : GoString) (id : w64) (mm : apply.MemberM),
  mem !! id = some mm → mm.name = name →
  (∀ (k : w64) (m' : apply.MemberM), mem !! k = some m' → m'.name = name → k = id) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c ∗ membership.clusterMem c mem }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"MemberByName")) (Val #name))
  {{ (m : Loc), RET #m;
      ∃ v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member, m ↦ v ∗
        ⌜v.ID' = mm.id⌝ ∗ membership.clusterMem c mem }}

end spec

end EtcdGrove
end Perennial
