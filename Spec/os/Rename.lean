/-
`os.Rename(oldpath, newpath)` (names only in Perennial; D22 S-f, 2026-10-19): the database file
at `oldpath` moved to `newpath`, replacing what was there. The trust boundary, a file-system
fact (an axiom in `Proof/os/Rename.lean`), stated over the backend's file predicates
(`backend.fileHolds`, `backend.pathOwn`: `Proof/go_etcd_io/etcd/server/v3/storage/backend/
InvSnapshot.lean`), the only files the verified code renames (`storage.OpenSnapshotBackend`'s
received snapshot onto the backend's path).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Spec.fmt.Errorf
public import Perennial.Code.os

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `os.Rename(src, dst)` of the file holding `D` onto the program's entry `dst`: on success the
file is at `dst` and the entry `src` the program's; on an error (an error `fmt` can format)
nothing moved, the environment failing it (`¬ renameOk src dst`: D22 receiver epochs, S8d,
2026-10-24; the program holds `src` and owns `dst`, so an error is the environment's). -/
abbrev os.Rename.spec : Prop :=
  ∀ (src dst : GoString) (D : Data),
  {{ fileHolds (GF := GF) src D ∗ pathOwn dst }}
    (App (App (Val (@! _root_.Perennial.os.Rename)) (Val #src)) (Val #dst))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ fileHolds dst D ∗ pathOwn src) ∨
      (⌜err ≠ GoInterface.nil ∧ ¬ renameOk src dst⌝ ∗ fmt.argOk err ∗ fileHolds src D ∗
        pathOwn dst) }}

end spec

end EtcdGrove
end Perennial
