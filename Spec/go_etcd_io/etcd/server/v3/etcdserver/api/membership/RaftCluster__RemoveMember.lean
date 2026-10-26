/-
`membership.RaftCluster.RemoveMember(id, shouldApplyV3)` (`cluster.go`): under the lock, with
`shouldApplyV3`, the backend's member delete (`c.be.MustDeleteMemberFromBackend(id)`), the member
out of the members map, `id` into the removed map, the metric, a log line; without, a log line.
Lean-first (no Rocq counterpart); D43 M4 (2026-10-26).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The backend's member delete (`c.be`, the interface `bi`, `MustDeleteMemberFromBackend(id)`),
by the caller's triple from `Pd` to `Qd` (persistent). -/
def membership.beDeleteOk (bi : GoInterfaceOk) (id : w64) (Pd Qd : IProp GF) : IProp GF :=
  iprop(□ ({{ Pd }}
    (App (Val #(methods bi.ty go!"MustDeleteMemberFromBackend" bi.v)) (Val #id))
    {{ RET #(); Qd }}))

instance membership.beDeleteOk_persistent (bi : GoInterfaceOk) (id : w64) (Pd Qd : IProp GF) :
    Persistent (membership.beDeleteOk (GF := GF) bi id Pd Qd) := by
  unfold membership.beDeleteOk; infer_instance

/-- `c.RemoveMember(id, v3)` on a cluster of the dynamic instance (`isRaftClusterG c (rcDyn γ)`)
with the removed map's writer half at `rm`: with `v3`, it calls the backend's delete (`c.be`, an
interface `bi` read-only, whose triple the caller gives: the backend's buckets are the caller's,
`Pd` to `Qd`) and moves the writer half to `rm` with `id` removed, and (D43 M5b, 2026-10-26) the
in-memory members' apply-thread half (`clusterMem`) to `mem` without `id`; without, nothing. Its
other reads are of read-only fields: the logger (non-nil), the cluster id. -/
abbrev membership.RaftCluster.RemoveMember.spec : Prop :=
  ∀ (c : Loc) (γ : GName) (rm : GMap w64 Bool) (mem : GMap w64 apply.MemberM) (id : w64) (dqb : DFrac)
    (v3 : Bool) (lg : Loc) (cid : w64) (bi : GoInterfaceOk) (Pd Qd : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftClusterG c (membership.rcDyn γ) ∗ membership.rcRemovedOwn γ rm ∗
      membership.clusterMem c mem ∗
      membership.rcLgAddr c ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ membership.rcCidAddr c ↦□ cid ∗
      membership.rcBeAddr c ↦{dqb} GoInterface.ok bi ∗
      (if v3 then iprop(membership.beDeleteOk bi id Pd Qd ∗ Pd) else iprop(True)) }}
    (App (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!!
      go!"RemoveMember")) (Val #id)) (Val #v3))
  {{ RET #(); membership.rcBeAddr c ↦{dqb} GoInterface.ok bi ∗ if v3 then iprop(Qd ∗ membership.rcRemovedOwn γ (GMap.insert id true rm) ∗
        membership.clusterMem c (GMap.delete id mem))
      else iprop(membership.rcRemovedOwn γ rm ∗ membership.clusterMem c mem) }}

end spec

end EtcdGrove
end Perennial
