/-
`fileutil.Fsync` (names-only here: no file-system model). Lean-first (no Rocq counterpart); etcd
PR #22046 (branch `pr-verify/etcd-22046`), for `(*snap.Snapshotter).SaveDBFrom`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

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

/-- `fileutil.Fsync(f)` of an open handle: nil or an error; the handle stays open. -/
abbrev fileutil.Fsync.spec : Prop :=
  ∀ (f : Loc) (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ fs.dirHandle f p }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync)) (Val #f))
  {{ (err : GoInterface), RET #err; fs.dirHandle f p ∗ fsResult err iprop(True) iprop(True) }}

end spec

end EtcdGrove
end Perennial
