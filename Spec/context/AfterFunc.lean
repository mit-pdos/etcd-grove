/-
`context.AfterFunc(ctx, f)`: the trust boundary (Perennial has no spec of it). Lean-first (no
Rocq counterpart).
-/
module

public import Perennial.Proof.context

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
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **`context.AfterFunc(ctx, f)`** for a context `c` (`isContext c s`): `f()` may run, in a goroutine
of its own, at any time from the call on (Go runs it once, after `c` is done; the spec does not say
when, nor that it runs: an execution in which it never runs is a prefix of one in which it does,
as Perennial's `time.AfterFunc`), so `f()` must be safe to run then, any number of times (`□`),
and must not panic. The returned `stop` function returns some `bool` and does nothing the caller
sees (it only unregisters `f`). -/
abbrev context.AfterFunc.spec : Prop :=
  ∀ (c : GoInterfaceOk) (s : _root_.Perennial.context.ContextDesc (IProp GF)) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ _root_.Perennial.context.isContext c s ∗
      □ (WP (App (Val f) (Val #())) {{ (fun v : val => iprop(⌜v.isPanic = false⌝)) }} : IProp GF) }}
    (App (App (Val (@! _root_.Perennial.context.AfterFunc)) (Val #(interface.ok c))) (Val f))
  {{ (stop : GoFunc), RET #stop;
      □ (∀ Φ : val → IProp GF, ▷ (∀ b : Bool, Φ #b) -∗ WP (App (Val #stop) (Val #())) {{ Φ }}) }}

end spec

end EtcdGrove
end Perennial
