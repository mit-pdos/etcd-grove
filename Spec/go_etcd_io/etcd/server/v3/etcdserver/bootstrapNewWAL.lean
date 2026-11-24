/-
`bootstrapNewWAL(cfg, cl)` (`bootstrap.go:717-735` at the etcd pin `edc800c6f`), with its body since claim
#34's stage 4 (2026-11-25): `bootstrapStorage`'s first-start branch. Lean-first;
`notes/bootstrap-proof-plan.md` §7.4. Its vocabulary: `Proof/.../etcdserver/BootParts.lean`
(`bootFs.walPart`) and `WalApi.lean` (`wal.bootOk`).
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

/-- **`bootstrapNewWAL(cfg, c)` at a first start**: on the WAL's part of the start (`bootFs.walPart`:
the dedicated WAL directory the member's, its area fresh), with a zap logger, `cfg.UnsafeNoFsync`
false, the cluster record `c` (its `nodeID`) and its cluster's `cid` field (`cid`), both read: a new
WAL record `bw` (the logger, the WAL, no WAL read: `haveWAL` false, no hard state, entries, snapshot
or metadata) and the WAL opened by `wal.Create` with the member's metadata (`wal.bootOk cfg
bc.nodeID cid bw.w`).

Why it is true of Go: `MustMarshalMessage(&Metadata{NodeID: &nodeID, ClusterID: &cid})` (`:718-723`;
`cl.cl.ID()` reads `c.cid`) is protobuf-go's encoding of the two set fields (`walMetaEnc`), then
`wal.Create(cfg.Logger, cfg.WALDir(), metadata)` (`:724`) in the dedicated WAL directory (`WALDir()`
is `DedicatedWALDir`, non-empty, `config.go:302-307`) of the fresh area, which succeeds there (its
failure is `lg.Panic`, excluded by the area's facts, `walAreaFresh`); `cfg.UnsafeNoFsync` false, so
no `SetUnsafeNoFsync`; then `&bootstrappedWAL{lg: cfg.Logger, w: w}` (`:731-734`). -/
abbrev bootstrapNewWAL.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Loc) (bc : bootstrappedCluster)
    (dq dqc : DFrac) (cid : w64),
  cfg.UnsafeNoFsync' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗ bootFs.walPart cfg ∗ c ↦{dq} bc ∗
      membership.rcCidAddr bc.cl' ↦{dqc} cid }}
    (App (App (Val (@! bootstrapNewWAL)) (Val #cfg)) (Val #c))
  {{ (w : Loc), RET #w;
      ∃ bw : bootstrappedWAL, w ↦ bw ∗
        ⌜bw.lg' = cfg.Logger' ∧ bw.haveWAL' = false ∧ bw.st' = null ∧
          bw.ents' = slice.nil ∧ bw.snapshot' = null ∧ bw.meta' = null⌝ ∗
        wal.bootOk cfg bc.nodeID' cid bw.w' ∗
        c ↦{dq} bc ∗ membership.rcCidAddr bc.cl' ↦{dqc} cid }}

end spec

end EtcdGrove
end Perennial
