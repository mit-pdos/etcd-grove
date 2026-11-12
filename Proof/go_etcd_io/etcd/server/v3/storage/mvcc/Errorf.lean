/-
`fmt.Errorf`'s error, with its exact type, for a format without verbs and no arguments
(`mvcc.errorfIs`): `errors.New(format)`, an `*errors.errorString`, in Go (`fmt/errors.go:23-31`'s fast
path) and in Perennial's model alike. Perennial's `fmt.wp_Errorf` keeps only that `Error()` returns;
the compaction's caller needs the type (a pointer leaf). Lean-first (no Rocq counterpart).

This steps into Perennial's model of `Errorf` (`errors.New(format)`), which is faithful only on that
path: since 2026-11-06 (errorf-wrap) its premises are that path's, no `%` in the format and no
arguments. A `%w` error goes through `fmt.ErrorfWrap` (`Spec/fmt/ErrorfWrap.lean`;
`notes/decisions.md`, "`fmt.Errorf` with `%w`: no fact from the model").
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **`fmt.Errorf(format)`, without verbs or arguments**, returns an error `errorfIs` describes
(`errors.New(format)`, in Go as in Perennial's model: the fast path; errorf-wrap, 2026-11-06). -/
theorem wp_Errorf_errorfIs (format : GoString) (args_sl : GoSlice)
    (_hfmt : (W8 37 : w8) ∉ format) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* ([] : List GoAny) }}
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
