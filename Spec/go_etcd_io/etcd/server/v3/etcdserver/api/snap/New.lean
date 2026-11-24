/-
`snap.New(lg, dir)` (`server/etcdserver/api/snap/snapshotter.go:34-43` at the etcd pin `edc800c6f`):
`lg` replaced by `zap.NewNop()` when nil, then `&Snapshotter{lg: lg, dir: dir, fsyncDir:
fsyncSnapDir}`. The new snapshotter is one of `dir` (`isSnapshotter`), for a `dir` that is a member's
snapshot directory (`config.snapDirOf dd`, as `isSnapshotter` records; `bootstrapSnapshot` passes
`cfg.SnapDir()`). Claim #34, stage 4 (2026-11-23). Proved, `Proof/.../snap/New.lean`, since
`isSnapshotter`'s `snapshotterRO` names the `fsyncDir` field (the owner's option (a), 2026-11-23).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

/-- See the file header. -/
abbrev snap.New.spec : Prop :=
  ∀ (lg : Loc) (dir : GoString), (∃ dd, dir = config.snapDirOf dd) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      zapLoggerOrNil lg }}
    (App (App (Val (@! _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.New))
      (Val #lg)) (Val #dir))
  {{ (ss : Loc), RET #ss; isSnapshotter ss dir }}

end spec

end EtcdGrove
end Perennial
