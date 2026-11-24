/-
`membership.RaftCluster.MemberIDs` (`cluster.go:170-179` at the etcd pin `edc800c6f`: under the lock,
the members map's keys, sorted, `sort.Sort(types.IDSlice(ids))`), for the holder of the members' other
half (`clusterMem`). Claim #34, stage 4 (2026-11-25; `bootstrapRaft`'s `cluster.cl.MemberIDs()`).
Lean-first.

**Not proved: a hypothesis** (`?` in the server's `Link.lean`): `MemberIDs` is names-only, one of stage
2's functions (`notes/bootstrap-proof-plan.md` §3: `MemberByName`, `MemberIDs`). It holds of Go: the lock
invariant's half of the members map (`memAt c ½ ms mem'`) and `clusterMem c mem`'s agree (`mem' = mem`,
the same `ms`), `memDom ms mem` gives the keys, and `IDSlice`'s order is `uint64`'s `<`, the keys
distinct.
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

/-- See the file header: the members' ids, strictly increasing, exactly the keys of `mem`. -/
abbrev membership.RaftCluster.MemberIDs.specMem : Prop :=
  ∀ (c : Loc) (mem : GMap w64 apply.MemberM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c ∗ membership.clusterMem c mem }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"MemberIDs")) (Val #()))
  {{ (s : GoSlice), RET #s; ∃ ids : List w64, s ↦* ids ∗
      ⌜ids.Pairwise (fun a b => uint.Z a < uint.Z b) ∧ ∀ k, k ∈ ids ↔ (mem !! k).isSome⌝ ∗
      membership.clusterMem c mem }}

end spec

end EtcdGrove
end Perennial
