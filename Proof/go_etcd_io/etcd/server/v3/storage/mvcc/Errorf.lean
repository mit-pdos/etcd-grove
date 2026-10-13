/-
`fmt.Errorf`'s error, with its exact type in Perennial's model (`mvcc.errorfIs`): `errors.New` of
the format, an `*errors.errorString`. Perennial's `fmt.wp_Errorf` keeps only that `Error()`
returns; the request path's read side (2026-10-12, unit 3b) needs the type to tell the gRPC layer
the error is a pointer leaf (`applyErrIs`). Lean-first (no Rocq counterpart).

This steps into Perennial's model of `Errorf` (`errors.New(format)`), outside the arguments
Perennial's `fmt.wp_Errorf` admits (`fmt.ArgsWf`); etcd-grove's axiom for the others
(`Spec/fmt/Errorf.lean`) does not give the leaf, which Go's `%w` error is not
(`notes/decisions.md`, "`fmt.Errorf`'s `%w` errors: the model's body, not the axiom").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Perennial.Proof.fmt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode

section wp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions] [fmt_sem : _root_.Perennial.fmt.Assumptions]

/-- `errors.New(msg)` with the exact type of what it returns (as Perennial's
`context.wp_New_errorString`, without its section's method-set classes). -/
theorem wp_New_errorString (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x);
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
            go!"Error" #x)) (Val #())) {{ Φ }} }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  imodintro
  iintro %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

/-- **`fmt.Errorf(format, args...)`** returns an error `errorfIs` describes (Perennial's model:
`errors.New(format)`). -/
theorem wp_Errorf_errorfIs (format : GoString) (args_sl : GoSlice) (args : List GoAny) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterface), RET #err; errorfIs err }} := by
  wp_start as _
  wp_apply wp_New_errorString as %x #Herr
  iapply HΦ
  iunfold errorfIs
  iexists x
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ HΦ
  iapply Herr
  inext
  iapply HΦ

end wp

end mvcc
end EtcdGrove
end Perennial
