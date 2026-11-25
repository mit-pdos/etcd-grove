/-
`bootstrapStorage(cfg, be, wal, cl)` (`bootstrap.go:203-212` at the etcd pin `edc800c6f`, through
`bootstrapNewWAL`, `:717-735`; names-only, a callee of `bootstrap`'s proof, `?` in the server's link
until stage 4 proves it over `wal.Create`, with #15). Lean-first; claim #34, stage 3 (2026-11-23),
`notes/bootstrap-proof-plan.md` §7.3. Its vocabulary: `Proof/.../etcdserver/BootParts.lean`.
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

/-- **`bootstrapStorage(cfg, bkl, nil, c)` at a first start**: on the WAL's part of the start
(`bootFs.walPart`: the dedicated WAL directory the member's, its area fresh), with a zap logger, the
cluster record `c` (its `nodeID` `id`) and its cluster's `cid` field (`cid`), both read: the record
`sto` of the backend `bkl` and a new WAL record `bw` (`bootOk`'s `Hsto`, `Hbw`), the WAL opened by
`wal.Create` with the member's metadata (`Hwal`: `wal.bootOk cfg id cid`), and `bw` as
`bootstrapNewWAL` writes it: the logger, the WAL, no WAL read (`haveWAL` false, no hard state, entries,
snapshot or metadata), which `bootstrappedWAL.MemoryStorage` and `Finalize` read.

Why it is true of Go: `wal == nil` (`:204`), so `bootstrapNewWAL(cfg, cl)`: `MustMarshalMessage` of
`Metadata{NodeID: cl.nodeID, ClusterID: cl.cl.ID()}` (`:718-723`; `ID()` reads `c.cid`), then
`wal.Create(cfg.Logger, cfg.WALDir(), metadata)` (`:724`) in the dedicated WAL directory (`WALDir()`
is `DedicatedWALDir`, non-empty, `config.go:302-307`) of the fresh area, which succeeds there (its
failure is `lg.Panic`, excluded by the area's facts, `walAreaFresh`), then `SetUnsafeNoFsync` if
configured; `&bootstrappedWAL{lg: cfg.Logger, w: w}` (`:731-734`) and `&bootstrappedStorage{backend:
be, wal: wal}` (`:208-211`).

(Claim #34 stage 4, 2026-11-25; ledger, "`bootstrapStorage.spec` without `UnsafeNoFsync = false`") **Only
with `cfg.UnsafeNoFsync` false**: otherwise `bootstrapNewWAL` calls `w.SetUnsafeNoFsync()`
(`:728-730`), which sets the WAL's `unsafeNoSync`, and the open WAL `wal.bootOk` describes (its
handle, `walOpenWS`, holds `unsafeNoSync ↦ false`: its `Sync`s fsync) is not the WAL Go has. Until then
the spec covered both. Through `bootstrapNewWAL` (`bootstrapNewWAL.spec`). -/
abbrev bootstrapStorage.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (bkl c : Loc) (bc : bootstrappedCluster)
    (dq dqc : DFrac) (cid : w64),
  cfg.UnsafeNoFsync' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗ bootFs.walPart cfg ∗ c ↦{dq} bc ∗
      membership.rcCidAddr bc.cl' ↦{dqc} cid }}
    (App (App (App (App (Val (@! bootstrapStorage)) (Val #cfg)) (Val #bkl)) (Val #(null : Loc)))
      (Val #c))
  {{ (s : Loc), RET #s;
      ∃ (sto : bootstrappedStorage) (bw : bootstrappedWAL), s ↦ sto ∗ sto.wal' ↦ bw ∗
        ⌜sto.backend' = bkl ∧ bw.lg' = cfg.Logger' ∧ bw.haveWAL' = false ∧ bw.st' = null ∧
          bw.ents' = slice.nil ∧ bw.snapshot' = null ∧ bw.meta' = null⌝ ∗
        wal.bootOk cfg bc.nodeID' cid bw.w' ∗
        c ↦{dq} bc ∗ membership.rcCidAddr bc.cl' ↦{dqc} cid }}

end spec

end EtcdGrove
end Perennial
