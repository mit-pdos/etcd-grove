/-
`(*bootstrappedCluster).Finalize(cfg, s)` (`bootstrap.go:512-527` at the etcd pin `edc800c6f`;
names-only, a callee of `bootstrap`'s proof, `?` in the server's link until stage 2 proves it over
`SetID`, `NewMembershipBackend`, `RaftCluster.SetBackend` and `ValidateMaxLearnerConfig`). Lean-first;
claim #34, stage 3 (2026-11-23), `notes/bootstrap-proof-plan.md` §7.3. Its vocabulary:
`Proof/.../etcdserver/BootParts.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`c.Finalize(cfg, s)` with no WAL read**: from the cluster as `bootstrapCluster` built it
(`clusterBuilt`, the initial cluster's facts `bootGo.membersOk`, the record's `nodeID` this member's
id), the storage record `s` (its WAL record not read, `haveWAL` false; its backend record's `be` the
real backend `d`, whose table has the membership's buckets) and the backend constructor's post over
the data `D` with a write-back token (`bootstrapBackend`'s): the constructor's post over `D` with the
membership's buckets created (`bootGo.withMemBkts D`, whatever the result: the error comes after
`SetBackend`, and `bootstrap`'s error path closes the backend), and either an error or the cluster's
rows of `bootOk` (`bootClusterDone`: `Hcl Hrc Hcid Hclg Hvcn Hmembers Hisc HclBe Hmem`). The
records are read and given back.

The cluster's lock invariant is `membership.isRaftCluster`, which stage 1 (`ea2dc2dcf2`, plan §7.1
I2) widened with the version slot, given by `clusterBuilt`'s `version ↦ nil`. Its I3 made `Hclok` and
`Hcvm` lemmas of `Hrc`, and `Hisc` the rest of the apply contract (`clusterApplyRest`).

Why it is true of Go: `!s.wal.haveWAL` (`:513`), so `SetID(c.nodeID, c.cl.ID())` (`cluster.go:241-245`)
writes `localID` (this member, in the members map: `membersOk`) and `cid` (unchanged, `bootGo.cid`)
and records the metric; `SetBackend(NewMembershipBackend(cfg.Logger, s.backend.be))` (`:516`,
`cluster.go:247-250`) stores the membership backend over `d` (`HclBe`) and runs
`MustCreateBackendBuckets` (`schema/membership.go:171-178`): one session creating `members`,
`members_removed` and `cluster` (empty if absent, kept if present: `withMemBkts`), one write-back; no
`Recover` (`:517`); then `ValidateMaxLearnerConfig(cfg.MaxLearners, c.cl.Members(), false)` (`:526`):
the members are voters, so an error only for a negative `MaxLearners`. The lock is made here from the
zero mutex over the fields (`Hrc`), its other half of the members map the apply thread's (`Hmem`); the
cluster is not shared before. The cluster's `Members()` answers the members by id with the directory's
URLs (`Hmembers`) and `IsIDRemoved` returns (`Hcl`); the logger is read-only from here on (`Hclg`);
`versionChanged` stays owned until `NewServer` sets it (`Hvcn`). -/
abbrev bootstrappedCluster.Finalize.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (c s : Loc)
    (bc : bootstrappedCluster) (sto : bootstrappedStorage) (bk : bootstrappedBackend)
    (bw : bootstrappedWAL) (d : mvcc.KBReal) (W Pk : backend.BNames → IProp GF) (N : Nat)
    (D : backend.Data) (dq dqs dqb dqw : DFrac),
  bootGo.membersOk cfg U → bc.nodeID' = bootGo.id cfg U → bw.haveWAL' = false →
  bk.be' = interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be →
  d.P.has mvcc.membersBI → d.P.has mvcc.membersRemovedBI → d.P.has mvcc.clusterBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗ c ↦{dq} bc ∗ s ↦{dqs} sto ∗ sto.backend' ↦{dqb} bk ∗
      sto.wal' ↦{dqw} bw ∗ clusterBuilt bc.cl' U cfg ∗
      backend.newPostK d.γB d.P W Pk (bootLeft N) d.be D ∗ backend.wbTok d.γB }}
    (App (App (Val (c @!! go.GoType.PointerType bootstrappedCluster.ty @!! go!"Finalize"))
      (Val #cfg)) (Val #s))
  {{ (err : GoInterface), RET #err;
      c ↦{dq} bc ∗ s ↦{dqs} sto ∗ sto.backend' ↦{dqb} bk ∗ sto.wal' ↦{dqw} bw ∗
      backend.newPostK d.γB d.P W Pk (bootLeft N) d.be (bootGo.withMemBkts D) ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootClusterDone U cfg bc.cl' d.be) }}

end spec

end EtcdGrove
end Perennial
