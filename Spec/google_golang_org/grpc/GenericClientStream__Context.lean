/-
`(*GenericClientStream[Req, Res]).Context()`, promoted from the embedded `ClientStream`: `x.ClientStream.Context()`.

**At the trust boundary** (an axiom, `Proof/google_golang_org/grpc/GenericClientStream__Context.lean`; the watch slice's
unit W-W): Goose (the pinned translator) emits no body for a method of a generic type (it emits
the method's `MethodUnfold` assumption naming an undefined `.impl`) and drops the type arguments
of a promoted method's field access (`StructFieldRef GenericClientStream.ty`), so the generic
wrappers' methods are axiomatized, each stated as its Go body: for any message types (Go types
`T`, `U`; Lean types `V`, `W`), on a wrapper `p` whose embedded `ClientStream` holds `si` (read-only),
the method is the wrapped method's call. Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `(*GenericClientStream[Req, Res]).Context()`, promoted from the embedded `ClientStream`: `x.ClientStream.Context()`. Stated as its body, for any postcondition `Φ`. -/
abbrev grpc.GenericClientStream.Context.spec : Prop :=
  ∀ (T U : go.GoType) (V W : Type) (p : Loc) (si : GoInterfaceOk) (Φ : val → IProp GF),
  structFieldRef (google_golang_org.grpc.GenericClientStream V W) go!"ClientStream" p ↦□ (GoInterface.ok si) ∗
    WP (App (Val #(methods si.ty go!"Context" si.v)) (Val #())) {{ Φ }} ⊢
    WP (App (Val (p @!! go.GoType.PointerType (google_golang_org.grpc.GenericClientStream.ty T U) @!! go!"Context"))
      (Val #())) {{ Φ }}

end spec

end EtcdGrove
end Perennial
