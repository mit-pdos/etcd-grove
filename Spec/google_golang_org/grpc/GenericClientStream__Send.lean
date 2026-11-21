/-
`(*GenericClientStream[Req, Res]).Send(m)` (`stream_interfaces.go`): `x.ClientStream.SendMsg(m)`.

Proved over its translated body (prove-grpcext, 2026-11-20, `Proof/google_golang_org/grpc/GenericClientStream__Send.lean`;
an axiom from the watch slice's unit W-W until then, while the pinned Goose emitted no body for a method
of a generic type). Stated as the Go body: for any message types (Go types `T`, `U`, with Lean types
`V`, `W` that represent them, `TypeRepr`), on a wrapper `p` whose embedded `ClientStream` holds `si`
(read-only), the method is the wrapped method's call. (prove-grpcext) The `TypeRepr` premises are
new: without them the wrapper's Lean type `Generic…Stream V W` was unrelated to the Go type the body's
field access uses, and the field's address under it was not the body's. Lean-first (no Rocq counterpart).
(prove-grpcext) The wrapped `SendMsg`'s WP gives an `error` value: the body returns it through its
named result (a typed store and load), which a value of another shape would not pass unchanged.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import GeneratedProof.google_golang_org.grpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `(*GenericClientStream[Req, Res]).Send(m)` (`stream_interfaces.go`): `x.ClientStream.SendMsg(m)`. Stated as its body, for any postcondition `Φ`. -/
abbrev grpc.GenericClientStream.Send.spec : Prop :=
  ∀ (T U : go.GoType) (V W : Type) [ZeroVal V] [TypeRepr T V] [ZeroVal W] [TypeRepr U W] (p : Loc) (si : GoInterfaceOk) (m : Loc)
    (Φ : val → IProp GF),
  structFieldRef (google_golang_org.grpc.GenericClientStream V W) go!"ClientStream" p ↦□ (GoInterface.ok si) ∗
    WP (App (Val #(methods si.ty go!"SendMsg" si.v))
        (Val #(interface.mkOk (go.GoType.PointerType T) #m : GoInterface))) {{ v, ∃ err : GoInterface, ⌜v = #err⌝ ∗ Φ v }} ⊢
    WP (App (Val (p @!! go.GoType.PointerType (google_golang_org.grpc.GenericClientStream.ty T U) @!! go!"Send"))
      (Val #m)) {{ Φ }}

end spec

end EtcdGrove
end Perennial
