/-
`membership.RaftCluster.AddMember(m, shouldApplyV3)` (`cluster.go`): under the lock, the learner
metric if `m` is the local member; with `shouldApplyV3`, the backend's member save
(`c.be.MustSaveMemberToBackend(m)`), `m` into the members map (replacing any member of its id), the
metric, a log line; without, a log line. Lean-first (no Rocq counterpart); D43 M5b (2026-10-26).
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

/-- The backend's member save (`c.be`, the interface `bi`, `MustSaveMemberToBackend(m)`), by the
caller's triple from `Ps` to `Qs`, reading the member `m` (persistent). -/
def membership.beSaveOk (bi : GoInterfaceOk) (m : Loc) (mm : apply.MemberM) (Ps Qs : IProp GF) :
    IProp GF :=
  iprop(□ ({{ Ps ∗ membership.memberAt m 1 mm }}
    (App (Val #(methods bi.ty go!"MustSaveMemberToBackend" bi.v)) (Val #m))
    {{ RET #(); Qs ∗ membership.memberAt m 1 mm }}))

instance membership.beSaveOk_persistent (bi : GoInterfaceOk) (m : Loc) (mm : apply.MemberM)
    (Ps Qs : IProp GF) : Persistent (membership.beSaveOk (GF := GF) bi m mm Ps Qs) := by
  unfold membership.beSaveOk; infer_instance

/-- `c.AddMember(m, v3)` on a cluster at any side condition `RM` that an insert into the members
map keeps, with the in-memory members' apply-thread half at `mem` (`clusterMem`) and the owned member
`m` of value `mm` (the map, with `mm`'s id, of at most `2 ^ 62` members): with `v3`, it calls the
backend's save (`c.be`, an interface `bi` read-only, whose triple the caller gives: the backend's
buckets are the caller's, `Ps` to `Qs`) and puts `m` into the map, its half and the apply thread's
half now at `mem` with `mm` at its id, the map's entry `m` (`clusterMemIn`, D43 M5e: `m` given up, the map holds it); without, nothing (`m`
back). Its other reads are of read-only fields: the logger (non-nil), the cluster id, the local
id. -/
abbrev membership.RaftCluster.AddMember.spec : Prop :=
  ∀ (c : Loc) (RM : membership.RcSide GF) (mem : GMap w64 apply.MemberM) (m : Loc) (dqb : DFrac)
    (mm : apply.MemberM) (v3 : Bool) (lg : Loc) (cid : w64) (bi : GoInterfaceOk) (Ps Qs : IProp GF),
  (∀ lid ms rm, RM lid ms rm ⊢ RM lid (GMap.insert mm.id m ms) rm) →
  GMap.size (GMap.insert mm.id mm mem) ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftClusterG c RM ∗ membership.clusterMem c mem ∗ membership.memberAt m 1 mm ∗
      membership.rcLgAddr c ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ membership.rcCidAddr c ↦□ cid ∗
      membership.rcBeAddr c ↦{dqb} GoInterface.ok bi ∗
      (if v3 then iprop(membership.beSaveOk bi m mm Ps Qs ∗ Ps) else iprop(True)) }}
    (App (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!!
      go!"AddMember")) (Val #m)) (Val #v3))
  {{ RET #(); membership.rcBeAddr c ↦{dqb} GoInterface.ok bi ∗ if v3 then iprop(Qs ∗ membership.clusterMemIn c (GMap.insert mm.id mm mem) mm.id m)
      else iprop(membership.clusterMem c mem ∗ membership.memberAt m 1 mm) }}

end spec

end EtcdGrove
end Perennial
