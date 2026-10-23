/-
`path.Join(["/", p])` (Go's `path`, names-only here: `Code/path.lean`): `Clean("/" + "/" + p)`,
stated only where it is `p`: `p` an absolute path already clean (`PathCleanAbs`: it starts with
`/`, is not `/`, has no empty, `.` or `..` segment and no trailing `/`). `etcd3.New`'s
`pathPrefix`. Perennial has no model of `path`; `notes/perennial-changes.md`. The trust boundary: an axiom, `Proof/path/Join.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.path.Defs
public import Code.path

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev path.Join.spec : Prop :=
  ∀ (elems : GoSlice) (dq : DFrac) (p : GoString),
  path.PathCleanAbs p →
  {{ (elems ↦*{dq} [go!"/", p] : IProp GF) }}
    (App (Val #(functions _root_.Perennial.path.Join [])) (Val #elems))
  {{ RET #p; elems ↦*{dq} [go!"/", p] }}

end spec

end EtcdGrove
end Perennial
