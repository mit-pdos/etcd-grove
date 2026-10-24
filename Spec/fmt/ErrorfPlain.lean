/-
`fmt.Errorf` of a format without `%w`: the trust boundary (rafthttp stage 5e-3). Go's `Errorf`
returns `errors.New(s)` of the formatted string when the format wraps no error
(`fmt/errors.go`: `p.wrappedErrs` empty), an `*errors.errorString`, a leaf of an error tree; the
stream reader's `dial` returns such errors to `run`, which asks `errors.Is` of them. A spec of its
own (as `fmt.SprintfID`), so that `Errorf`'s other callers do not rest on it. Lean-first.
-/
module

public import Spec.fmt.Errorf
public import Proof.errors.NewVarCell

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]
/-- **The literal text of a format before its first verb** (2026-10-24, rafthttp stage 6e): what
the formatted message begins with (`fmt`'s `doPrintf` copies the format up to its first `%`). -/
def fmt.litPrefix (format : GoString) : GoString := format.takeWhile (fun b => b ≠ W8 37)

/-- **`fmt.Errorf(format, args...)`** of a format without `%w`, for arguments that are
`fmt.argsOk`: an `*errors.errorString` (`errors.New` of the formatted message), whose `Error()`
returns that message; the arguments' slice comes back. (2026-10-24, rafthttp stage 6e) Its `s`
field holds the message for good (`errStrCell`: `errors.New`'s `&errorString{s}`, which nothing
writes), the message beginning with the format's literal text (`fmt.litPrefix`): what tells it
from another error of a different message (`checkPostResponse`'s, from `errMemberRemoved`). -/
abbrev fmt.ErrorfPlain.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  ¬ List.IsInfix go!"%w" format →
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOk xs }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x);
      args_sl ↦*{dq} xs ∗ ∃ msg : GoString, errStrCell x msg ∗ ⌜fmt.litPrefix format <+: msg⌝ ∗
      □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }} }}

end spec

end EtcdGrove
end Perennial
