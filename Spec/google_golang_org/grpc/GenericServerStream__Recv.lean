/-
`(*GenericServerStream[Req, Res]).Recv()` (`stream_interfaces.go`): `m := new(Req)`, then `x.ServerStream.RecvMsg(m)`; `(m, nil)` if it returns `nil`, else `(nil, err)`.

Proved over its translated body (prove-grpcext, 2026-11-20, `Proof/google_golang_org/grpc/GenericServerStream__Recv.lean`;
an axiom from the watch slice's unit W-W until then, while the pinned Goose emitted no body for a method
of a generic type). Stated as the Go body: for any message types (Go types `T`, `U`, with Lean types
`V`, `W` that represent them, `TypeRepr`), on a wrapper `p` whose embedded `ServerStream` holds `si`
(read-only), the method is the wrapped method's call. (prove-grpcext) The `TypeRepr` premises are
new: without them the wrapper's Lean type `Generic…Stream V W` was unrelated to the Go type the body's
field access uses, and the field's address under it was not the body's. Lean-first (no Rocq counterpart).
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

/-- `(*GenericServerStream[Req, Res]).Recv()` (`stream_interfaces.go`): `m := new(Req)`, then `x.ServerStream.RecvMsg(m)`; `(m, nil)` if it returns `nil`, else `(nil, err)`. Stated as its body, for any postcondition `Φ`. -/
abbrev grpc.GenericServerStream.Recv.spec : Prop :=
  ∀ (T U : go.GoType) (V W : Type) [ZeroVal V] [TypeRepr T V] [ZeroVal W] [TypeRepr U W]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T] (p : Loc) (si : GoInterfaceOk) (Φ : val → IProp GF),
  structFieldRef (google_golang_org.grpc.GenericServerStream V W) go!"ServerStream" p ↦□ (GoInterface.ok si) ∗
    (∀ m : Loc, m ↦ (zero_val V) -∗
      WP (App (Val #(methods si.ty go!"RecvMsg" si.v))
          (Val #(interface.mkOk (go.GoType.PointerType T) #m : GoInterface)))
      {{ v, ∃ err : GoInterface, ⌜v = #err⌝ ∗
          Φ (if err = GoInterface.nil then PairV #m #GoInterface.nil else PairV #null #err) }}) ⊢
    WP (App (Val (p @!! go.GoType.PointerType (google_golang_org.grpc.GenericServerStream.ty T U) @!! go!"Recv"))
      (Val #())) {{ Φ }}

end spec

end EtcdGrove
end Perennial
