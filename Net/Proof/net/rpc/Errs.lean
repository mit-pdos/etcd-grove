/-
The errors the rpc client passes on, as `errAny` (`models_lab/Errors.lean`) and not `ServerError`s
(`notServerErr`, `Codec.lean`): an `errors.New` variable's value (`ErrShutdown`, `errFrame`, `io`'s
`EOF` and `ErrUnexpectedEOF`), a new `errors.New` error, and the net extension's `*OpError` (whose
`Error()` is the trusted model's arbitrary string, `Net/TrustedCode/net.lean`; dsverify-lab's
`opErr_errAny`). `errNE`: an error whose message is never empty, what the server answers a
request with (`errNE_opErr`: the model's `*OpError`'s message is not empty).
-/
module

public import Net.Proof.net.rpc.Codec
public import Net.Proof.net.Base
public import Perennial.Proof.errors.NewVar
public import GooseLang.Ext.Net.Specs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [net.Assumptions]

theorem errorString_ptr_isError :
    go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true := by
  go_type_set

theorem opError_ptr_isError :
    go.typeSetContains (go.GoType.PointerType net.OpError.ty) go.error = true := by
  go_type_set

/-- An `errors.New` error `*errorString` `x` with its `Error()` is `errAny`. -/
theorem errAny_errorString (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
        (Val #())) {{ Φ }}) ⊢
      models_lab.errAny (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  iintro #H
  unfold models_lab.errAny
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact errorString_ptr_isError
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iapply HΦ

/-- An `errors.New` variable's value is `errAny`. -/
theorem errAny_newVar (X msg : GoString) (e : GoInterface) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗ models_lab.errAny e := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, -, #HE⟩ #He
  icombine He Hx gives %Heq
  subst Heq
  iapply errAny_errorString x msg $$ HE

theorem notServerErr_errorString (x : Loc) :
    notServerErr (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  intro e he
  cases he
  simp [ServerError.ty]

/-- An `errors.New` variable's value is not a `ServerError`. -/
theorem notServerErr_newVar (X msg : GoString) (e : GoInterface) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗ ⌜notServerErr e⌝ := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, -⟩ #He
  icombine He Hx gives %Heq
  subst Heq
  ipureintro
  exact notServerErr_errorString x

theorem notServerErr_opError (pe : Loc) :
    notServerErr (interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe) := by
  intro e he
  cases he
  simp [ServerError.ty]

/-- `err` is a non-nil error whose `Error()` returns some message, never empty (persistent): what
the server needs of an error it answers a request with (`sendResponse` with `""` would send a
success response). -/
def errNE (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ ⌜go.typeSetContains e.ty go.error = true⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ (∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ #msg) -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errNE_persistent (err : GoInterface) : Persistent (errNE (GF := GF) err) := by
  unfold errNE; infer_instance

theorem errNE_errAny (err : GoInterface) : errNE (GF := GF) err ⊢ models_lab.errAny err := by
  unfold errNE models_lab.errAny
  iintro ⟨%e, %He, %Ht, #H⟩
  iexists e
  iframe %He %Ht
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iintro %msg -
  iapply HΦ

/-- An `errors.New` error `*errorString` `x` with a message not empty is `errNE`. -/
theorem errNE_errorString (x : Loc) (msg : GoString) (hm : msg ≠ []) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
        (Val #())) {{ Φ }}) ⊢
      errNE (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  iintro #H
  unfold errNE
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact errorString_ptr_isError
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iapply HΦ; ipureintro; exact hm

/-- An `errors.New` variable's value, of a message not empty, is `errNE`. -/
theorem errNE_newVar (X msg : GoString) (e : GoInterface) (hm : msg ≠ []) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗ errNE e := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, -, #HE⟩ #He
  icombine He Hx gives %Heq
  subst Heq
  iapply errNE_errorString x msg hm $$ HE

/-- A new `*OpError` is `errNE`: its `Error()` is an arbitrary string, not empty. -/
theorem errNE_opErr (op : GoString) (src addr e err : GoInterface) :
    net.opErr (GF := GF) op src addr e err ⊢ errNE err := by
  unfold net.opErr
  iintro ⟨%pe, %nw, ⟨%Herr, -⟩, -⟩
  subst Herr
  unfold errNE
  iexists ⟨go.GoType.PointerType net.OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact opError_ptr_isError
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_call
  unfold net.OpError.Error.impl
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyString
  iintro %str
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; simp
  · iapply HΦ; ipureintro; exact Hif

/-- A new `*OpError` is `errAny`: its `Error()` is an arbitrary string. -/
theorem errAny_opErr (op : GoString) (src addr e err : GoInterface) :
    net.opErr (GF := GF) op src addr e err ⊢ models_lab.errAny err := by
  iintro H
  iapply errNE_errAny
  iapply errNE_opErr $$ H

/-- A failure's error (`resErr (some k)`, an `*OpError`) is `errNE`. -/
theorem errNE_resErr (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    net.resErr (GF := GF) (some k) op src addr ed nm err ⊢ errNE err := by
  unfold net.resErr
  iintro ⟨%e, Hop, -⟩
  iapply errNE_opErr $$ Hop

/-- A failure's error (`resErr (some k)`, an `*OpError`) is `errAny`. -/
theorem errAny_resErr (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    net.resErr (GF := GF) (some k) op src addr ed nm err ⊢ models_lab.errAny err := by
  unfold net.resErr
  iintro ⟨%e, Hop, -⟩
  iapply errAny_opErr $$ Hop

/-- A failure's error is not a `ServerError`. -/
theorem notServerErr_resErr (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    net.resErr (GF := GF) (some k) op src addr ed nm err ⊢ ⌜notServerErr err⌝ := by
  unfold net.resErr net.opErr
  iintro ⟨%e, ⟨%pe, %nw, ⟨%Herr, -⟩, -⟩, -⟩
  ipureintro
  subst Herr
  exact notServerErr_opError pe

end lemmas

end net.rpc
end Perennial
