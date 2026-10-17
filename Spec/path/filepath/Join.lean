/-
`filepath.Join` (the standard library, names-only here: no file-system model). The trust boundary.
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046`), for
`(*snap.Snapshotter).ReleaseSnapDBs`.
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

/-- `filepath.Join(elems...)`: the path `fs.join xs` of the elements `xs` (an abstract function,
`etcdserver/api/snap/Defs.lean`). -/
abbrev filepath.Join.spec : Prop :=
  ∀ (elems : GoSlice) (xs : List GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.path.filepath ∗ elems ↦*{dq} xs }}
    (App (Val (@! _root_.Perennial.path.filepath.Join)) (Val #elems))
  {{ (p : GoString), RET #p; ⌜p = fs.join xs⌝ ∗ elems ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
