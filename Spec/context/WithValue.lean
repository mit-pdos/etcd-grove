/-
`context.WithValue`: the trust boundary (Perennial translates `context` without `WithValue`'s body). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Perennial.Proof.context

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
variable [package_sem : context.Assumptions]

/-- `context.WithValue(parent, key, v)`: a context, not nil (a `valueCtx` over `parent`), for a
key of the auth store's two parameter types (empty structs, comparable: `WithValue` panics on
a nil or incomparable key), as the backend's `Authenticate` passes. -/
abbrev context.WithValue.spec : Prop :=
  ∀ (parent key : GoInterfaceOk) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      ⌜key.ty = go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty ∨
        key.ty = go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty⌝ }}
    (App (App (App (Val (@! context.WithValue)) (Val #(GoInterface.ok parent)))
      (Val #(GoInterface.ok key))) (Val #v))
  {{ (c : GoInterface), RET #c; ⌜c ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
