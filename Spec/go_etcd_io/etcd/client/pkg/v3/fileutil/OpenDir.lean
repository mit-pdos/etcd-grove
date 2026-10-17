/-
`fileutil.OpenDir(path)` (`client/pkg/fileutil/dir_unix.go`: `os.Open(path)`; names-only).
Lean-first (no Rocq counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`), see
`InvSnapshotBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvSnapshotBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `fileutil.OpenDir(dir)`: on success a handle of the directory `dir`. -/
abbrev fileutil.OpenDir.spec : Prop :=
  ∀ (dir : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir)) (Val #dir))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      fsResult err (fs.dirHandle f dir) iprop(True) }}

end spec

end EtcdGrove
end Perennial
