/-
`storage.OpenSnapshotBackend(cfg, ss, snapshot, hooks)` (`server/storage/backend.go`): the
database snapshot of `snapshot`'s index, which the transport saved in the snapshotter's
directory, renamed onto the backend's path (`cfg.BackendPath()`) and opened (`OpenBackend`). D22
S-f, 2026-10-19 (translated with its body; `notes/decisions.md`, "D22 S-f carried out").
Lean-first (no Rocq counterpart); `applySnapshot`'s callee (D22 S-j).

The pre: the snapshotter (`isSnapshotter`), the snapshot's `Metadata` field and its metadata
`md` (read, given back), the file at `snapDBPath sd md.Index` (`sd` the snapshotter's directory) holding `D` (`fileAt`, S5: the claim on
its name with the file), taken from D22 S-i's snapshot directory with the taker's `R'` (`snapHeld`,
sealed: wal-link L2, T1, 2026-11-17; until then the file's `fileHolds` itself, which a client could keep
across a `Release` that removes the file, `notes/axiom-review/releasesnapdbs.md`), the backend's path
the program's (`bPath γo`, the claim on its name, the old backend's) and `openPre` (`InvOpen.lean`, with `openMmapOk cfg` since 2026-10-29) for the hooks `hooks` as a
`backend.Hooks`. The post: on success the backend over `D` (`newPostK`, whose `backend.fkCl γ P D`
gives the no-compaction token if `D` records none, `mvcc.bkNoCmp_of_fkCl`, and the bit `backend.fkV`
at `true` if `D`'s compaction keys are well formed, `mvcc.fkCl_wf`; until
the backend-compaction stage, 2026-10-29, a separate wand `⌜noCmpData D⌝ -∗ bkNoCmp γ`) and the
snapshot's entry the program's, and the taker's `R'` back (the file has left the directory's path);
on an error (the file not found, the rename failed), with `nil` for the backend, the token and the
path back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Perennial.ProgramLogic.Bounds
public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image
public import Proof.go_etcd_io.etcd.server.v3.storage.SnapHeld

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI backend storage go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `OpenSnapshotBackend(cfg, ss, snapshot, hooks)`: the snapshot's database file renamed onto the
backend's path and opened (2026-10-31: the program keeping its right to the backend's path,
`os.Rename`'s restated post; until then the snapshot file's), or an error with nothing moved, the environment having failed the
snapshot directory's read or the rename (D22 receiver epochs, S8d, 2026-10-24). (D22 receiver epochs, S8a, 2026-10-24:
the creator's `K` for the fresh backend's payment rights, `OpenBackend`'s.) (2026-11-06,
`notes/begin-tok-plan.md`) Under `[ThreadBoundLe GF (2 ^ 29)]`, `OpenBackend`'s. (S5, 2026-11-18) The
backend path's entry is the claim on its name, naming the old backend `γo`'s file (`bPath`, until then
the opaque `pathOwn`); on success the new backend's claim (`OpenBackend`'s), on an error the old one
back. (wal-link, 2026-11-19, option B1; then approved by the user via etcd-grove-03, the directory
per execution) The snapshotter's directory is the data directory's (`isSnapshotter ss (snapDirOf
cfg.DataDir)`, `bootOk`'s; until then the opaque `snapDBPath ss` and an equation,
`notes/snapdir-crossworld.md`): the snapshot's file and the backend's are then names of one
directory, which `os.Rename` needs. (bkarea, 2026-11-22) For a data directory shorter than `2^60`
bytes, which `cfg.BackendPath()`'s proof needs (`filepath.Join`'s premise; `applySnapshot`'s callers
have it from the data directory that fits, `srvSnapRO`). -/
abbrev storage.OpenSnapshotBackend.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)]
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss sn mp hk : Loc) (dq dq' : DFrac)
    (md : SnapshotMetadataM) (P : BParams) (D : Data) (W Pk K : BNames → IProp GF) (γo : DBNames)
    (R' : IProp GF),
  -- (bkarea, 2026-11-22) a data directory shorter than `2^60` bytes (`BackendPath`'s, proved:
  -- `filepath.Join`'s premise)
  cfg.DataDir'.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ snap.isSnapshotter ss (config.snapDirOf cfg.DataDir') ∗
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      snapHeld (snap.snapDBPath (config.snapDirOf cfg.DataDir') md.Index') D R' ∗ bPath γo (config.backendPathOf cfg.DataDir') ∗
      openPre cfg (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty) #hk)
        P D W Pk K }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend)) (Val #cfg))
      (Val #ss)) (Val #sn)) (Val #hk))
  {{ (be err : GoInterface), RET (PairV #be #err);
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (b : Loc) (γ : BNames),
          ⌜be = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b⌝ ∗
          newPostK γ P W Pk K b D ∗
          hooksAt b (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty) #hk) ∗
          bPath γ.db (config.backendPathOf cfg.DataDir') ∗ R' ∗
          -- (2026-11-04, R2b-3c part 2) the backend's file is the backend path (`OpenBackend`'s)
          bFile γ (config.backendPathOf cfg.DataDir')) ∨
       (⌜err ≠ GoInterface.nil ∧ be = GoInterface.nil ∧
          ¬ (snap.dirReadOk ss ∧
            renameOk (snap.snapDBPath (config.snapDirOf cfg.DataDir') md.Index') (config.backendPathOf cfg.DataDir'))⌝ ∗
          snapHeld (snap.snapDBPath (config.snapDirOf cfg.DataDir') md.Index') D R' ∗ bPath γo (config.backendPathOf cfg.DataDir'))) }}

end spec

end EtcdGrove
end Perennial
