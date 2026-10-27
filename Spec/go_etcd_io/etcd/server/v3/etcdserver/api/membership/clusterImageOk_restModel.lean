/-
**The membership buckets of a committed log's image are good for the server's cluster** (D22, J7,
2026-10-26; `notes/snapshot-sj-plan.md`, J0 decision 9): a fact about the Go code and the
deployment, not a Go function's triple; an axiom at the trust boundary
(`Proof/.../membership/clusterImageOk_restModel.lean`), why it is true of the Go code below.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The rest model's membership buckets at a committed log are a good image for the cluster
`c`** (`membership.clusterImageOk`, what `RaftCluster.Recover`'s axiom takes): for the server's
raft names `γ` from the fresh cluster's start (`γ.pre = []`, the start's consistent index
`c0 = 0`), the cluster `c` whose in-memory members are the rest model's at a log `L`
(`clusterMem`, which only the server's apply thread holds, at its applied log: `bootOk`'s
`memBoot`, then the cluster's contracts as the model says), and a committed log `L'` (`srvRLogLb`)
extending `L`, at least as long as the boot log, whose conf changes are all ones the server's
`applyConfChange` takes (`ccLogOk` at raft's configuration, the KV invariant's workload fact): the
model's buckets and members at `L'` satisfy `memBucketsOk c` (`clusterMem` given back).

Why it is true of the Go code (etcd at the pin `bc9c3868c`: `schema/membership.go`,
`api/membership/cluster.go`, `version/downgrade.go`) and the deployment (a fresh static cluster,
every member running the same binary, `bootOk`):

* *The buckets decode, to the model's members.* The rest model is what every member's apply
  thread writes (`InvRest.lean`): `members` holds, under `schema.BackendMemberKey(id)`, the JSON
  `MustSaveMemberToBackend` writes (`json.Marshal` of the `*Member`, `memberEnc`), which
  `MustReadMembersFromBackend` (`mustParseMemberIDFromBytes`, `json.Unmarshal`) decodes back to the
  record the model keeps in `mem` (`restUpdateAttrs` and `ccRest` change both together); the boot
  log's members, which `memBoot` puts in `mem` before any is saved, are saved when the boot log's
  conf changes are applied (each an `AddNode` of a boot member, above `c0 = 0` so `v3`, valid:
  `ValidateConfigurationChange` finds no member with its id or peer URLs yet, the boot members
  being distinct with their own URLs), which `L'` includes (it is committed, so it extends raft's
  boot log, and it is at least as long). `members_removed` stays empty (no `RemoveNode`:
  `ccLogOk`); `cluster` holds only the version `SetVersion` saves (`semver`'s `String()` of a
  parsed version, `semverNorm`, which `semver.MustParse` reads back) and no downgrade record
  (`DowngradeInfoSet` is not in the workload, `plainCover`).
* *The members are the static cluster's, the local member among them, none removed.* The later
  conf changes of `L'` are `AddNode`s of members of raft's configuration, the boot peers
  (`ccLogOk`), which `ValidateConfigurationChange` rejects (`ErrIDExists`: `ccValidOn` false), so
  `members` keeps exactly the boot members, with their boot peer URLs (`ClusterMemberAttrSet`
  changes only the name and client URLs); `c`'s local member (`isRaftCluster c`: `c.localID` in
  `c.members`, whose records are `clusterMem`'s, the model's at `L`, the boot members) is one.
* *The cluster version passes `MustDetectDowngrade`.* `Recover` panics only if the version in
  `cluster` is above the server's own major.minor (`downgrade.go:42-55`). The only proposer of
  `ClusterVersionSet` is a member's `monitorClusterVersions` (`updateClusterVersionV3`), with
  `decideClusterVersion`'s minimum of the members' versions, all the binary's: never above it.

Not true for a cluster that changes membership (a `RemoveNode`, an added member), for a log
shorter than the boot log (its image misses boot members `mem` already has), or across binaries
of different versions; the premises exclude the first two, the deployment the third. -/
abbrev membership.clusterImageOk_restModel.spec : Prop :=
  ∀ (c : Loc) (γ : ServerRaftNames) (c0 : w64) (L L' : List EntryModel),
    γ.pre = [] → c0 = W64 0 → L <+: L' → γ.raft.reBoot.length ≤ L'.length →
    -- (merge of D43 M5, 2026-10-27) `ccLogOk`'s static form, which `ccLogOk` was before M5d made it
    -- mode-aware (the same statement as before the merge)
    (∀ m ∈ L', m.typ ≠ W32 0 → ccBootOk γ.raft.reCfg m.data) →
    ⊢ membership.isRaftCluster (GF := GF) c -∗ srvRLogLb γ L' -∗
      membership.clusterMem c (restModel c0 γ.raft.reBoot L).mem -∗
      membership.clusterMem c (restModel c0 γ.raft.reBoot L).mem ∗
      ⌜membership.clusterImageOk c (restModel c0 γ.raft.reBoot L').bk
        (restModel c0 γ.raft.reBoot L').mem⌝

end spec

end EtcdGrove
end Perennial
