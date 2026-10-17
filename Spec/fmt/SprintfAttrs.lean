/-
`fmt.Sprintf` of a `membership.Attributes` (etcd-io/etcd#22525: `publishV3`'s log lines format
`fmt.Sprintf("%+v", s.attributes)`). Perennial's `fmt.wp_Sprintf` admits arguments of predeclared
basic types only (`fmt.ArgsWf`); a struct is not one. The trust boundary,
`Proof/fmt/SprintfAttrs.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.fmt
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.membership

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

/-- `fmt.Sprintf(format, a)` with one argument, a `membership.Attributes` value (a struct of a
`string` and a `[]string`, with no methods), returns some string and gives the arguments' slice
back. -/
abbrev fmt.SprintfAttrs.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      args ↦*{dq} [interface.mkOk go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes.ty #a] }}
    (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
  {{ (s : GoString), RET #s;
      args ↦*{dq} [interface.mkOk go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes.ty #a] }}

end spec

end EtcdGrove
end Perennial
