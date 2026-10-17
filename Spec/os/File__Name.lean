/-
`os.File.Name` (names-only here: no file-system model). Lean-first (no Rocq counterpart); etcd
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

/-- `f.Name()`: the file's name. -/
abbrev os.File.Name.spec : Prop :=
  ∀ (f : Loc) (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ fs.fileName f p }}
    (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"Name")) (Val #()))
  {{ RET #p; True }}

end spec

end EtcdGrove
end Perennial
