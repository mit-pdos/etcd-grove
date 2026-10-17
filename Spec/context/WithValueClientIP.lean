/-
`context.WithValue(ctx, auth.ClientIPContextKey{}, addr)` (PR etcd#22259: the server's log
interceptor stores the client's address in a run's context): the trust boundary (Perennial
translates `context` without `WithValue`'s body). A second triple of `WithValue`, beside
`WithValue.lean`'s (whose keys are the auth store's parameters and the traces'), at this key,
stating `valueCtx.Value`'s behavior in general. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.context
public import Proof.go_etcd_io.etcd.server.v3.auth.ClientIP

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
variable [package_sem : context.Assumptions]

/-- `context.WithValue(parent, ClientIPContextKey{}, s)` (`s` a string, as an `any`) returns a
non-nil context `c` (a `valueCtx` over `parent`; the key is an empty struct, comparable, so
`WithValue` does not panic) such that: `c`'s `Deadline`, `Done` and `Err` are its parent's, so a
context (`isContext`) at a descriptor gives one at the same descriptor (a descriptor's `Values`
is read by no context predicate); its `Value` at the key returns `s` (`ctxClientIPIs c (some s)`:
an equal key, `ClientIPContextKey{} == ClientIPContextKey{}`); and at a key of another dynamic
type it is its parent's (`valueCtx.Value` compares the keys, unequal as interfaces of different
types, then asks the parent: `value(c.Context, key)`, which for every parent returns what the
parent's `Value(key)` returns). -/
abbrev context.WithValueClientIP.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (App (App (Val (@! context.WithValue)) (Val #(GoInterface.ok parent)))
      (Val #auth.clientIPKeyVal)) (Val #(interface.mkOk go.string #s : GoInterface)))
  {{ (c : GoInterfaceOk), RET #(GoInterface.ok c);
      □ (∀ cd : context.ContextDesc (IProp GF), context.isContext parent cd -∗
          context.isContext c cd) ∗
      auth.ctxClientIPIs c (some s) ∗
      □ (∀ (k : GoInterfaceOk) (Φ : val → IProp GF),
          ⌜k.ty ≠ go_etcd_io.etcd.server.v3.auth.ClientIPContextKey.ty⌝ -∗
          WP (App (Val #(methods parent.ty go!"Value" parent.v)) (Val #(GoInterface.ok k))) {{ Φ }} -∗
          WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #(GoInterface.ok k))) {{ Φ }}) }}

end spec

end EtcdGrove
end Perennial
