/-
`fmt.Sprintf` with a `*clientv3.Client` argument: the trust boundary, for the one call shape
`clientv3`'s `dial` makes, `Sprintf("%s://%p/%s", resolver.Schema, c, authority(ep))` (item 5,
client construction). Perennial's `fmt.wp_Sprintf` admits arguments of predeclared basic types
only (`fmt.ArgsWf`: Go calls the `Error()`/`String()`/`Format`/`GoString` methods of other
arguments, which its model does not); a pointer is not one. A spec of its own (as
`fmt.SprintfNamed`), so that `Sprintf`'s other callers do not rest on it. Lean-first (no Rocq
counterpart).
-/
module

public import Perennial.Proof.fmt
public import Code.go_etcd_io.etcd.client.v3

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- An argument of `Sprintf` that Go formats without calling any method: `nil`, a value of a
predeclared basic type (`fmt.ArgWf`), or a `*clientv3.Client`, whose method set has no `Error`,
`String`, `Format` or `GoString` (checked against `client/v3`: `Client`'s own methods and those
promoted from its embedded `Cluster`, `KV`, `Lease`, `Watcher`, `Auth`, `Maintenance`), so that Go
formats it by its kind (a pointer: `%p` its address, `%v` too). -/
def fmt.SprintfClientArgOk : GoInterface → Prop
  | .nil => True
  | .ok ii => _root_.Perennial.fmt.ArgWf ii ∨
      ii.ty = go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- `fmt.Sprintf(format, args...)` with every argument `fmt.SprintfClientArgOk` returns a string
`s` with `fmt.SprintfOut format xs s`, as Perennial's `fmt.wp_Sprintf` states it (a pointer
argument is formatted by a directive the model does not interpret: the rest of the output is
arbitrary), and gives the arguments' slice back. At the trust boundary
(`Proof/fmt/SprintfClientPtr.lean`). -/
abbrev fmt.SprintfClientPtr.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args ↦*{dq} xs ∗
        ⌜∀ a ∈ xs, fmt.SprintfClientArgOk a⌝ }}
      (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
    {{ (s : GoString), RET #s; args ↦*{dq} xs ∗ ⌜_root_.Perennial.fmt.SprintfOut format xs s⌝ }}

end spec

end EtcdGrove
end Perennial
