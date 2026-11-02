/-
`context.WithTimeout(context.Background(), d)` with its outgoing metadata (the auth-mode merge's 5b,
2026-10-29): `WithTimeoutBackground`'s, and the context carries no outgoing gRPC metadata
(`metadata.outgoingOf`, opaque: grpc's `metadata` is names-only, `Outgoing.lean`). What a caller
needs to know that an attempt of a client with no credentials carries no token
(`clientTokAt … (fun _ => False)`'s second disjunct: the context's own). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.context.WithTimeoutBackground
public import Proof.google_golang_org.grpc.metadata.Outgoing

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `context.WithTimeout(context.Background(), d)`: `WithTimeoutBackground.spec`'s post, and the
context's outgoing metadata is none. Go: grpc stores outgoing metadata under its own unexported key
(`mdOutgoingKey{}`, `metadata.NewOutgoingContext`/`AppendToOutgoingContext`), `Background()` holds
no value, and `WithTimeout` adds none (a `*timerCtx` whose `Value` defers to its parent), so
`FromOutgoingContext` of it finds nothing. -/
abbrev context.WithTimeoutBackgroundMd.spec : Prop :=
  ∀ (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.isClosedchanInit }}
    (App (App (Val (@! _root_.Perennial.context.WithTimeout))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #d))
  {{ (ctx' : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
      context.isContext ctx' cd ∗ ⌜metadata.outgoingOf (GoInterface.ok ctx') = none⌝ }}

end spec

end EtcdGrove
end Perennial
