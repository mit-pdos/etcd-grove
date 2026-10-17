/-
`context.WithValue(parent, internalRootContextKey{}, internalRootContextValue{...})`
(etcd-io/etcd#22493, `pr-verify/etcd-22493`: `auth.WithRootInternal`): the trust boundary
(Perennial translates `context` without `WithValue`'s body). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.RootCtx

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

/-- `context.WithValue(parent, internalRootContextKey{}, x)`: a context `c'`, not nil (Go's
`&valueCtx{parent, key, x}`: the key is an empty struct, comparable), that carries the root
value `x` (`valueCtx.Value` returns `x` at an equal key, and every `internalRootContextKey{}`
is equal to it), and that is a context described as its parent is, with other values (a
`valueCtx`'s `Deadline`, `Done` and `Err` are its parent's; as `context.WithValue.spec`). -/
abbrev context.WithValueInternalRoot.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (x : go_etcd_io.etcd.server.v3.auth.internalRootContextValue),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (App (App (Val (@! context.WithValue)) (Val #(GoInterface.ok parent)))
      (Val #auth.rootKeyVal)) (Val #(auth.rootValAny x)))
  {{ (c : GoInterface), RET #c; ∃ c' : GoInterfaceOk, ⌜c = GoInterface.ok c'⌝ ∗
      auth.ctxRootIs c' (some x) ∗ auth.ctxDerived parent c' }}

end spec

end EtcdGrove
end Perennial
