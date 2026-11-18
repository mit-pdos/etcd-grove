/-
The specs of the lab's models of `google.golang.org/grpc/status` and `grpc/codes` (statements;
proved in `Status.lean`): a status is a code and a message (`isStatus`, persistent: Go code never
writes a `*Status`'s fields after `New`), its error a `*statusError` (`statusErrOf`, persistent).

* `codes.Code.String`: some string (the code's name; `"Code(n)"` for codes past 16).
* `New(c, msg)`: a non-nil status of `c` and `msg`.
* `Error(c, msg)` and `(*Status).Err()`: `nil` for `OK`, else a status error of `c` and `msg`.
* `(*Status).Code()`, `Message()`: the status's code and message (`OK` and `""` for `nil`).
* `FromError(err)`: `(nil, true)` for `nil`; a status error's own status and `true`; for another
  error (`errAny`, not a `*statusError`), a status `Unknown` with its message and `false`.
* `FromContextError(err)`: for a non-nil error whose comparison with `context`'s two errors does
  not panic (`cmpSafe`), a status with a code that is not `OK`.
* `Code(err)`: `OK` for `nil`, a status error's code, `Unknown` for another error.
* A status error has some `Error()` (`statusErrOf_errAny`).
* `handlerErr err`: what the grpc server needs of a handler's non-nil error: a status error, or
  an error with some `Error()` that is not a `*statusError` and compares with the context errors
  without panicking (any pointer-typed error, or `context.DeadlineExceeded`'s value).
-/
module

public import Harness.Proof.grpc.Base
public import Harness.Proof.net.rpc.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace google_golang_org.grpc.status

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `s` is a status of code `c` and message `msg` (persistent): `nil` (the status `OK`), or a
`*Status` whose fields hold them for good. -/
def isStatus (s : Loc) (c : w32) (msg : GoString) : IProp GF :=
  iprop(⌜s = null ∧ c = W32 0 ∧ msg = []⌝ ∨
    (⌜s ≠ null⌝ ∗ structFieldRef Status go!"code" s ↦□ c ∗
      structFieldRef Status go!"msg" s ↦□ msg))

/-- `err` is a status error of code `c` (not `OK`) and message `msg` (persistent). -/
def statusErrOf (err : GoInterface) (c : w32) (msg : GoString) : IProp GF :=
  iprop(∃ (e s : Loc), ⌜err = interface.mkOk (go.GoType.PointerType statusError.ty) #e ∧
      c ≠ W32 0⌝ ∗ structFieldRef statusError go!"s" e ↦□ s ∗ isStatus s c msg)

/-- `err` is not a `*statusError` (nor `nil`... `nil` is not one either). -/
def notStatusErr (err : GoInterface) : Prop :=
  ∀ e : GoInterfaceOk, err = interface.ok e → e.ty ≠ go.GoType.PointerType statusError.ty

/-- Comparing `err` with `context.Canceled` and `context.DeadlineExceeded` does not panic: it is
pointer-typed, or `DeadlineExceeded`'s value. -/
def cmpSafe (err : GoInterface) : Prop :=
  (∃ (T : go.GoType) (l : Loc), err = interface.mkOk (go.GoType.PointerType T) #l) ∨
  err = interface.mkOk context.deadlineExceededError.ty #(zero_val context.deadlineExceededError)

/-- What the grpc server needs of a handler's non-nil error (persistent). -/
def handlerErr (err : GoInterface) : IProp GF :=
  iprop((∃ (c : w32) (msg : GoString), statusErrOf err c msg) ∨
    (net.rpc.errAny err ∗ ⌜notStatusErr err ∧ cmpSafe err⌝))

instance isStatus_persistent (s : Loc) (c : w32) (msg : GoString) :
    Persistent (isStatus (GF := GF) s c msg) := by
  unfold isStatus; infer_instance
instance statusErrOf_persistent (err : GoInterface) (c : w32) (msg : GoString) :
    Persistent (statusErrOf (GF := GF) err c msg) := by
  unfold statusErrOf; infer_instance
instance handlerErr_persistent (err : GoInterface) :
    Persistent (handlerErr (GF := GF) err) := by
  unfold handlerErr; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [google_golang_org.grpc.codes.Assumptions] [google_golang_org.grpc.status.Assumptions]
variable [context.Assumptions] [fmt.Assumptions]

/-- `c.String()`: some string. -/
abbrev codes.Code.String.spec : Prop :=
  ∀ (c : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes }}
    (App (Val (c @!! google_golang_org.grpc.codes.Code.ty @!! go!"String")) (Val #()))
  {{ (r : GoString), RET #r; True }}

/-- `New(c, msg)`. -/
abbrev New.spec : Prop :=
  ∀ (c : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status }}
    (App (App (Val (@! google_golang_org.grpc.status.New)) (Val #c)) (Val #msg))
  {{ (s : Loc), RET #s; ⌜s ≠ null⌝ ∗ isStatus s c msg }}

/-- What `Error(c, msg)` and `Err()` return. -/
def errPost (c : w32) (msg : GoString) (err : GoInterface) : IProp GF :=
  iprop((⌜c = W32 0 ∧ err = interface.nil⌝) ∨ statusErrOf err c msg)

/-- `Error(c, msg)`. -/
abbrev Error.spec : Prop :=
  ∀ (c : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status }}
    (App (App (Val (@! google_golang_org.grpc.status.Error)) (Val #c)) (Val #msg))
  {{ (err : GoInterface), RET #err; errPost c msg err }}

/-- `s.Code()`. -/
abbrev Status.Code.spec : Prop :=
  ∀ (s : Loc) (c : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ isStatus s c msg }}
    (App (Val (s @!! go.GoType.PointerType Status.ty @!! go!"Code")) (Val #()))
  {{ RET #c; True }}

/-- `s.Message()`. -/
abbrev Status.Message.spec : Prop :=
  ∀ (s : Loc) (c : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ isStatus s c msg }}
    (App (Val (s @!! go.GoType.PointerType Status.ty @!! go!"Message")) (Val #()))
  {{ RET #msg; True }}

/-- `s.Err()`. -/
abbrev Status.Err.spec : Prop :=
  ∀ (s : Loc) (c : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ isStatus s c msg }}
    (App (Val (s @!! go.GoType.PointerType Status.ty @!! go!"Err")) (Val #()))
  {{ (err : GoInterface), RET #err; errPost c msg err }}

/-- `FromError(err)`. -/
abbrev FromError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      (⌜err = interface.nil⌝ ∨ (∃ c msg, statusErrOf err c msg) ∨
        (net.rpc.errAny err ∗ ⌜notStatusErr err⌝)) }}
    (App (Val (@! google_golang_org.grpc.status.FromError)) (Val #err))
  {{ (s : Loc) (ok : Bool), RET (PairV #s #ok);
      (⌜err = interface.nil ∧ s = null ∧ ok = true⌝) ∨
      (∃ c msg, ⌜ok = true⌝ ∗ statusErrOf err c msg ∗ isStatus s c msg) ∨
      (⌜ok = false⌝ ∗ ∃ msg, isStatus s (W32 2) msg) }}

/-- `FromContextError(err)` on a non-nil error. -/
abbrev FromContextError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ net.rpc.errAny err ∗
      ⌜cmpSafe err⌝ }}
    (App (Val (@! google_golang_org.grpc.status.FromContextError)) (Val #err))
  {{ (s : Loc), RET #s; ∃ c msg, ⌜c ≠ W32 0⌝ ∗ isStatus s c msg }}

/-- `Code(err)`. -/
abbrev Code.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      (⌜err = interface.nil⌝ ∨ (∃ c msg, statusErrOf err c msg) ∨
        (net.rpc.errAny err ∗ ⌜notStatusErr err⌝)) }}
    (App (Val (@! google_golang_org.grpc.status.Code)) (Val #err))
  {{ (c : w32), RET #c;
      ⌜err = interface.nil ∧ c = W32 0⌝ ∨ (∃ msg, statusErrOf err c msg) ∨ ⌜c = W32 2⌝ }}

/-- A status error has some `Error()` (a lemma over `codes.Code.String`'s spec; with the
status package initialized). -/
abbrev statusErrOf_errAny.stmt : Prop :=
  ∀ (err : GoInterface) (c : w32) (msg : GoString),
  isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOf err c msg ⊢
    net.rpc.errAny err

end spec

end google_golang_org.grpc.status

end Perennial
