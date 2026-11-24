/-
`bootstrapSnapshot(cfg)` (`bootstrap.go:214-257` at the etcd pin `edc800c6f`; names-only, a callee of
`bootstrap`'s proof, `?` in the server's link until stage 4 proves it). Lean-first; claim #34, stage 3
(2026-11-23), `notes/bootstrap-proof-plan.md` §7.3. Its vocabulary: `Proof/.../etcdserver/BootParts.lean`.
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

/-- **`bootstrapSnapshot(cfg)` at a first start**: on the fresh member directory `DataDir/member`
(`bootFs.dirFresh`, the member state's, `bootFs.memberDir`) of a data directory that fits
(`bootCfgFresh`'s `Fs.DirFits`), the snapshotter of the snapshot directory (`bootOk`'s `Hss`), the
claims on every index's `.snap.db` name there, free (`Hsfree`), and the backend file's name, free
(`backend.fileFree (config.backendPathOf DataDir)`, what `bootstrapBackend` opens), and (claim #34,
2026-11-23, approved by the owner via the coordinator) the snapshot directory's right
(`snap.snapDirOwn`, `Hsdo`): the claim on all its other names, which the directory's invariant keeps
(until then `Hsdo` was the member state's, over an opaque predicate).

Why it is true of Go: `TouchDirAll(cfg.SnapDir())` (`:215`) makes `DataDir/member/snap` (`SnapDir()`
is `filepath.Join(MemberDir(), "snap")`, `config.go:309`: `config.snapDirOf DataDir`), new and empty,
or fails, and then `lg.Fatal` does not return; the three `RemoveMatchFile`s (`:223-254`) list the
empty directory and remove nothing (an error only logs); `snap.New(cfg.Logger, cfg.SnapDir())`
(`:256`) returns the snapshotter with `dir` the snapshot directory and `lg` the configuration's
logger. So every name of the new directory, the `<16 hex>.snap.db` ones, `db` and the rest, names nothing,
and the paths fit (`config.pathFits_snapDir_child`, `config.pathFits_backendPathOf`). No error result. -/
abbrev bootstrapSnapshot.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig),
  Fs.DirFits cfg.DataDir' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗ bootFs.dirFresh (path.joinModel [cfg.DataDir', go!"member"]) }}
    (App (Val (@! bootstrapSnapshot)) (Val #cfg))
  {{ (ss : Loc), RET #ss;
      snap.isSnapshotter ss (config.snapDirOf cfg.DataDir') ∗
      snapFreeAll (snap.snapDBPath (config.snapDirOf cfg.DataDir')) ∗
      backend.fileFree (config.backendPathOf cfg.DataDir') ∗
      snap.snapDirOwn (snap.snapDBPath (config.snapDirOf cfg.DataDir')) }}

end spec

end EtcdGrove
end Perennial
