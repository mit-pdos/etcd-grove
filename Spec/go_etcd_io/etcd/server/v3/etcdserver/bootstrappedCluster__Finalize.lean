/-
`(*bootstrappedCluster).Finalize(cfg, s)` (`bootstrap.go`), with etcd-io/etcd#21867's change
(pr-verify, 2026-10-17): after `Recover`, with `--force-new-cluster`, `RemoveMember(id, true)` of
every member but this node. Lean-first (no Rocq counterpart); see `InvFinalize.lean`.

**The membership** is a record of ids (`ClusterSt`) through a predicate `P` the spec quantifies
over, the cluster's names-only methods as contracts on it (`fzClusterOk`, `fzCalleesOk`).

**The post**: some error (`ValidateMaxLearnerConfig`'s, or the missing database's), and the
membership `σ'`:
* without a WAL (`!s.wal.haveWAL`): unchanged (`SetID`, `SetBackend`);
* with a WAL: `FinalizedSt cfg.ForceNewCluster c.nodeID σrec σ'`, from the backend's membership
  `σrec` that `Recover` loads: `σrec` itself without `--force-new-cluster`; with it, the members
  are `c.nodeID` at most, and every other member of `σrec` is among the removed ids (in memory and,
  through `RemoveMember`'s `ApplyBoth`, in the backend).

The consequence for the conf-change entries `--force-new-cluster` appends is
`finalize_force_rejects_removal` (`InvFinalize.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvFinalize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev bootstrappedCluster.Finalize.spec : Prop :=
  ∀ (c s : Loc) (dq : DFrac) (cb : bootstrappedCluster) (sb : bootstrappedStorage)
    (bb : bootstrappedBackend) (wb : bootstrappedWAL)
    (cv : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (P : ClusterSt → IProp GF) (σ0 σrec : ClusterSt),
  cv.Logger' ≠ null →
  fzClusterOk cb.cl' P σrec →
  fzCalleesOk c P →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      c ↦{dq} cb ∗ s ↦{dq} sb ∗ sb.backend' ↦{dq} bb ∗ sb.wal' ↦{dq} wb ∗
      P σ0 }}
    (App (App (Val (c @!! go.GoType.PointerType bootstrappedCluster.ty @!! go!"Finalize"))
      (Val #cv)) (Val #s))
  {{ (err : GoInterface), RET #err; ∃ σ' : ClusterSt,
      P σ' ∗ c ↦{dq} cb ∗ s ↦{dq} sb ∗ sb.backend' ↦{dq} bb ∗ sb.wal' ↦{dq} wb ∗
      ⌜if wb.haveWAL' then FinalizedSt cv.ForceNewCluster' cb.nodeID' σrec σ' else σ' = σ0⌝ }}

end spec

end EtcdGrove
end Perennial
