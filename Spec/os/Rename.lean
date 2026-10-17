/-
`os.Rename(src, dst)` (Perennial's `os` is names-only; no file-system model). Lean-first (no Rocq
counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`), see `InvSnapshotBackend.lean`.
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

/-- `os.Rename(src, dst)`: on success the rename has happened but its directory entry is not
known to be durable (`fs.renamePending src dst`); on failure, an error. -/
abbrev os.Rename.spec : Prop :=
  ∀ (src dst : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.os }}
    (App (App (Val (@! _root_.Perennial.os.Rename)) (Val #src)) (Val #dst))
  {{ (err : GoInterface), RET #err; fsResult err (fs.renamePending src dst) iprop(True) }}

end spec

end EtcdGrove
end Perennial
