/-
`os.Rename(oldpath, newpath)` (D22 S-f, 2026-10-19): the database file at `oldpath` moved to
`newpath`, replacing what was there, the only files the verified server renames
(`storage.OpenSnapshotBackend`'s received snapshot onto the backend's path). Over the backend's file
predicates in the tree's shared mode (`backend.fileAt`, `backend.bPath`, `backend.fileFree`,
`Proof/go_etcd_io/etcd/server/v3/storage/backend/InvBbolt.lean`); proved in `Proof/os/Rename.lean`
from the model (S5, 2026-11-18; until then an axiom over the abstract `srvFileHolds`, `pathOwn`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Spec.fmt.Errorf
public import Code.os

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `os.Rename(src, dst)` of the file at `src` holding `D` onto `dst`, the name of an open
database's file (S5, 2026-11-18): `nil`, the file at `dst` and the name `src` free. Over the tree's
shared mode (`fileAt`, `bPath`, `fileFree`: the claims on the two names), from the model
(`Proof/os/Rename.lean`'s `rename_fileNE`, a lemma, not a spec): no error, the semantics having no I/O error where a success exists
(`theFs`'s `FsNoErrAll`). The file at `dst` it replaces is the open database's, which keeps its
inode (`bClosed` after its `Close`). Until S5 an axiom over the abstract `srvFileHolds` and
`pathOwn`, with an error case `¬ renameOk src dst`. (wal-link, 2026-11-19, decided by etcd-grove-03,
option B1) The two names in one directory (`parentOf src = parentOf dst`): the model's rename needs
both in one root's tree (`SameRootR`, the per-root call model), which a spine of their common
directory gives (`osPathS_sameRoot`); the server's rename is in the snapshot directory
(`snap.snapDBPath`, `config.backendPathOf`). (pin e94f33b50, 2026-11-25) The rename's log entry
(`renamed src dst`: the log past it), for the directory sync after it to commit. -/
abbrev os.Rename.spec : Prop :=
  ∀ (src dst : GoString) (D : Data) (γ : DBNames), parentOf src = parentOf dst →
  {{ fileAt (GF := GF) src D ∗ bPath γ dst }}
    (App (App (Val (@! _root_.Perennial.os.Rename)) (Val #src)) (Val #dst))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ fileAt dst D ∗ fileFree src ∗
      renamed src dst }}

end spec

end EtcdGrove
end Perennial
