/-
The errors the rpc client passes on, as `errAny` (`models_lab/Errors.lean`) and not `ServerError`s
(`notServerErr`, `Codec.lean`): an `errors.New` variable's value (`ErrShutdown`, `errFrame`, `io`'s
`EOF` and `ErrUnexpectedEOF`), a new `errors.New` error, and the net extension's `*OpError` (whose
`Error()` is the trusted model's arbitrary string, `Net/TrustedCode/net.lean`; dsverify-lab's
`opErr_errAny`). `errNE`: an error whose message is never empty (`errNE_opErr`: the model's
`*OpError`'s message is not empty).

**The server's own error answers** (`srvErrMsg`): the messages net/rpc's server itself answers a
request with (`models/net/rpc/server.go`, `codec.go`), which a service's spec must accept
(`errOk`, `ServerDefs.lean`), and no others: `readRequestHeader`'s `errors.New` of
`"rpc: service/method request ill-formed: "`, `"rpc: can't find service "` and
`"rpc: can't find method "` followed by the request's `ServiceMethod`; the codec's decoding error
(`rpcErrDecode()`'s `"net/rpc model: malformed value"`, `decErr`); and a read error's
(`rdErrMsg`: of the body frame's read, `serverCodec.ReadRequestBody`): `errFrame`'s
`"rpc: malformed frame"`, `io.EOF`'s `"EOF"`, `io.ErrUnexpectedEOF`'s `"unexpected EOF"`, or a
`Read`'s `*OpError`'s, of Go's form `"read" ++ s1 ++ ": " ++ s2` (`net.opErrMsg`). (Go's
`"rpc: server cannot decode request: "` is never sent: the loop stops instead.) `errSrv`: an error
whose `Error()` returns such a message.
-/
module

public import Net.Proof.net.rpc.Codec
public import Net.Proof.net.Base
public import Net.Proof.net.Errors
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.errors.Base
public import GooseLang.Ext.Net.Specs
public import Net.Proof.models_lab.ErrFmt

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

/-- A new `*OpError` is `errNE`: its `Error()` is of Go's form, not empty. -/
theorem errNE_opErr (op : GoString) (src addr e err : GoInterface) :
    net.opErr (GF := GF) op src addr e err ⊢ errNE err := by
  unfold net.opErr
  iintro ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩
  subst Herr
  unfold errNE
  iexists ⟨go.GoType.PointerType net.OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact opError_ptr_isError
  imodintro
  iintro %Φ HΦ
  iapply net.wp_OpError_Error $$ Hpe
  inext
  iintro %msg %hmsg
  iapply HΦ; ipureintro; exact net.opErrMsg_ne _ _ hmsg

/-- A new `*OpError` is `errAny`: its `Error()` is an arbitrary string. -/
theorem errAny_opErr (op : GoString) (src addr e err : GoInterface) :
    net.opErr (GF := GF) op src addr e err ⊢ models_lab.errAny err := by
  iintro H
  iapply errNE_errAny
  iapply errNE_opErr $$ H

/-- Any `*OpError` (its fields persistent) is `errAny`: its `Error()` (the net model's) returns a
message of Go's form (`DialHTTPPath`'s `"dial-http"` error, whose `Net` is not a TCP network's
name). -/
theorem errAny_opErrPtr (pe : Loc) (v : net.OpError) :
    (pe ↦□ v : IProp GF) ⊢
      models_lab.errAny (GF := GF) (interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe) := by
  iintro #Hpe
  unfold models_lab.errAny
  iexists ⟨go.GoType.PointerType net.OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact opError_ptr_isError
  imodintro
  iintro %Φ HΦ
  iapply net.wp_OpError_Error $$ Hpe
  inext
  iintro %msg -
  iapply HΦ

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

/-! ### The server's own error answers -/

/-- A read error's message (see the file header). -/
def rdErrMsg (msg : GoString) : Prop :=
  msg = go!"rpc: malformed frame" ∨ msg = go!"EOF" ∨ msg = go!"unexpected EOF" ∨
    net.opErrMsg go!"read" msg

/-- The messages net/rpc's server itself answers a request with (see the file header). -/
def srvErrMsg (msg : GoString) : Prop :=
  (∃ sm : GoString, msg = go!"rpc: service/method request ill-formed: " ++ sm) ∨
  (∃ sm : GoString, msg = go!"rpc: can't find service " ++ sm) ∨
  (∃ sm : GoString, msg = go!"rpc: can't find method " ++ sm) ∨
  msg = go!"net/rpc model: malformed value" ∨ rdErrMsg msg

theorem srvErrMsg_ne (msg : GoString) (h : srvErrMsg msg) : msg ≠ [] := by
  rcases h with ⟨sm, rfl⟩ | ⟨sm, rfl⟩ | ⟨sm, rfl⟩ | rfl | h
  · simp
  · simp
  · simp
  · simp
  unfold rdErrMsg at h
  rcases h with rfl | rfl | rfl | h
  · simp
  · simp
  · simp
  · exact net.opErrMsg_ne _ _ h

theorem srvErrMsg_method (sm : GoString) : srvErrMsg (go!"rpc: can't find method " ++ sm) :=
  Or.inr (Or.inr (Or.inl ⟨sm, rfl⟩))

theorem srvErrMsg_dec : srvErrMsg go!"net/rpc model: malformed value" :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem srvErrMsg_rd (msg : GoString) (h : rdErrMsg msg) : srvErrMsg msg :=
  Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- `err` is a non-nil error whose `Error()` returns one of the server's own error answers
(`srvErrMsg`, persistent). -/
def errSrv (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ ⌜go.typeSetContains e.ty go.error = true⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ (∀ msg : GoString, ⌜srvErrMsg msg⌝ -∗ Φ #msg) -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errSrv_persistent (err : GoInterface) : Persistent (errSrv (GF := GF) err) := by
  unfold errSrv; infer_instance

theorem errNE_errSrv (err : GoInterface) : errSrv (GF := GF) err ⊢ errNE err := by
  unfold errSrv errNE
  iintro ⟨%e, %He, %Ht, #H⟩
  iexists e
  iframe %He %Ht
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iintro %msg %hmsg
  iapply HΦ; ipureintro; exact srvErrMsg_ne msg hmsg

/-- An `errors.New` error `*errorString` `x` with a server message is `errSrv`. -/
theorem errSrv_errorString (x : Loc) (msg : GoString) (hm : srvErrMsg msg) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
        (Val #())) {{ Φ }}) ⊢
      errSrv (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  iintro #H
  unfold errSrv
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

/-- An `errors.New` variable's value, of a server message, is `errSrv`. -/
theorem errSrv_newVar (X msg : GoString) (e : GoInterface) (hm : srvErrMsg msg) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗ errSrv e := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, -, #HE⟩ #He
  icombine He Hx gives %Heq
  subst Heq
  iapply errSrv_errorString x msg hm $$ HE

/-- A read's failure (`resErr (some k)` of the operation `"read"`, an `*OpError`) is `errSrv`. -/
theorem errSrv_resErr_read (k : NetErr) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    net.resErr (GF := GF) (some k) go!"read" src addr ed nm err ⊢ errSrv err := by
  unfold net.resErr net.opErr
  iintro ⟨%e, ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩, -⟩
  subst Herr
  unfold errSrv
  iexists ⟨go.GoType.PointerType net.OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact opError_ptr_isError
  imodintro
  iintro %Φ HΦ
  iapply net.wp_OpError_Error $$ Hpe
  inext
  iintro %msg %hmsg
  iapply HΦ; ipureintro
  exact srvErrMsg_rd msg (Or.inr (Or.inr (Or.inr hmsg)))

end lemmas

/-! ### `errPlain`: the errors `fmt` formats calling only their `Error()` (`models_lab/ErrFmt.lean`) -/

section plain
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [net.Assumptions] [errors.Assumptions] [fmt.Assumptions]

/-- An `errors.New` error `*errorString` `x`, its field `s` and its `Error()`, is `errPlain`. -/
theorem errPlain_errorString (x : Loc) (msg : GoString) :
    x.[errors.errorString, go!"s"] ↦□ msg ∗
      (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
          (Val #())) {{ Φ }}) ⊢
      models_lab.errPlain (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  iintro ⟨#Hs, #H⟩
  ihave #Ha := errAny_errorString x msg $$ H
  unfold models_lab.errPlain
  iframe Ha
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  unfold models_lab.errFmt
  isplitr
  · ipureintro; exact models_lab.noFmt_errorString
  iright; ileft
  iexists x, msg
  iframe Hs
  ipureintro; rfl

/-- An `errors.New` variable's value is `errPlain`. -/
theorem errPlain_newVar (X msg : GoString) (e : GoInterface) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗ models_lab.errPlain e := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, #Hs, #HE⟩ #He
  icombine He Hx gives %Heq
  subst Heq
  iapply errPlain_errorString x msg $$ [$Hs $HE]

/-- `Err` of an `*OpError` the client sees is `errLeaf` or the value of `poll.ErrDeadlineExceeded`
(see `models_lab.errFmt`). -/
def errLeafOrEd (e : GoInterface) : IProp GF :=
  iprop(⌜models_lab.errLeaf e⌝ ∨ globalAddr internal.poll.ErrDeadlineExceeded ↦□ e)

instance errLeafOrEd_persistent (e : GoInterface) : Persistent (errLeafOrEd (GF := GF) e) := by
  unfold errLeafOrEd; infer_instance

/-- A new `*OpError` whose `Source` and `Addr` are `errLeaf`, and its `Err` `errLeafOrEd`, is
`errPlain`. -/
theorem errPlain_opErr (op : GoString) (src addr e err : GoInterface)
    (hs : models_lab.errLeaf src) (ha : models_lab.errLeaf addr) :
    net.opErr (GF := GF) op src addr e err ∗ errLeafOrEd e ⊢ models_lab.errPlain err := by
  iintro ⟨#Hop, #Hl⟩
  ihave #Ha := errAny_opErr $$ Hop
  unfold net.opErr
  icases Hop with ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩
  subst Herr
  unfold models_lab.errPlain
  iframe Ha
  iexists ⟨go.GoType.PointerType net.OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  unfold models_lab.errFmt
  isplitr
  · ipureintro; exact models_lab.noFmt_opError
  iright; iright; iright; iright
  iexists pe, net.OpError.mk op nw src addr e
  iframe Hpe
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact ⟨hs, ha⟩
  iunfold errLeafOrEd at Hl
  iexact Hl

/-- Any `*OpError` whose fields are persistent and whose `Source`, `Addr` and `Err` are `errLeaf` is
`errPlain` (`DialHTTPPath`'s `"dial-http"` error). -/
theorem errPlain_opErrPtr (pe : Loc) (v : net.OpError)
    (h : models_lab.errLeaf v.Source' ∧ models_lab.errLeaf v.Addr' ∧ models_lab.errLeaf v.Err') :
    (pe ↦□ v : IProp GF) ⊢
      models_lab.errPlain (interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe) := by
  iintro #Hpe
  ihave #Ha := errAny_opErrPtr pe v $$ Hpe
  unfold models_lab.errPlain
  iframe Ha
  iexists ⟨go.GoType.PointerType net.OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  unfold models_lab.errFmt
  isplitr
  · ipureintro; exact models_lab.noFmt_opError
  iright; iright; iright; iright
  iexists pe, v
  iframe Hpe
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact ⟨h.1, h.2.1⟩
  ileft; ipureintro; exact h.2.2

/-- A failure's `Err` (`kindErr`) is `errLeafOrEd`, given that `ed` is `poll.ErrDeadlineExceeded`'s
value. -/
theorem kindErr_leaf [os.Assumptions] [internal.poll.Assumptions] (k : NetErr)
    (ed : Option GoInterface) (nm : GoString → Prop) (e : GoInterface) :
    net.kindErr (GF := GF) k ed nm e ∗
      (∀ ed', ⌜ed = some ed'⌝ -∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed') ⊢
      errLeafOrEd e := by
  iintro ⟨#Hk, Hed⟩
  unfold errLeafOrEd
  cases k with
  | closed =>
    unfold net.kindErr
    icases Hk with %He
    subst He
    ileft; ipureintro
    exact Or.inr ⟨⟨internal.poll.errNetClosing.ty, _⟩, rfl, models_lab.noFmt_errNetClosing,
      Or.inr (Or.inl rfl)⟩
  | timeout =>
    cases ed with
    | none =>
      unfold net.kindErr
      icases Hk with %Hf
      exact Hf.elim
    | some ed =>
      unfold net.kindErr
      icases Hk with %He
      subst He
      iright
      iapply Hed
      ipureintro; rfl
  | sys =>
    unfold net.kindErr net.sysErr
    icases Hk with ⟨%p, %name, %n, ⟨%He, -⟩, -⟩
    subst He
    ileft; ipureintro
    exact models_lab.errLeaf_ptr _ _ models_lab.noFmt_syscallError

/-- A failure's error (`resErr (some k)`) of `Source` and `Addr` `errLeaf` is `errPlain`, given that
`ed` is `poll.ErrDeadlineExceeded`'s value. -/
theorem errPlain_resErr [os.Assumptions] [internal.poll.Assumptions] (k : NetErr) (op : GoString)
    (src addr : GoInterface) (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface)
    (hs : models_lab.errLeaf src) (ha : models_lab.errLeaf addr) :
    net.resErr (GF := GF) (some k) op src addr ed nm err ∗
      (∀ ed', ⌜ed = some ed'⌝ -∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed') ⊢
      models_lab.errPlain err := by
  iintro ⟨#HE, Hed⟩
  unfold net.resErr
  icases HE with ⟨%e, #Hop, #Hk⟩
  ihave #Hl := kindErr_leaf k ed nm e $$ [$Hk $Hed]
  iapply errPlain_opErr op src addr e err hs ha $$ [$Hop $Hl]

/-- A `netAddr` (a `*TCPAddr`) is `errLeaf`. -/
theorem errLeaf_netAddr (x : GoInterface) : net.netAddr (GF := GF) x ⊢ ⌜models_lab.errLeaf x⌝ := by
  unfold net.netAddr
  iintro ⟨%p, %v, %Hx, -⟩
  subst Hx
  ipureintro
  exact models_lab.errLeaf_ptr _ _ models_lab.noFmt_TCPAddr

end plain

section errorsNew
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [errors.Assumptions]

/-- `errors.New(msg)`, its result's type made explicit (`errors.New.spec` says only that it is a
pointer; `errAny` needs its type to implement `error`) and its field `s` (what `fmt`'s `%#v` reads:
`models_lab.errFmt`): proved from its body, as
`errors.New.wp_proof`. -/
theorem wp_errors_New' (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x);
        x.[errors.errorString, go!"s"] ↦□ msg ∗
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
            (Val #())) {{ Φ }} }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  iframe s
  imodintro
  iintro %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

end errorsNew

end net.rpc
end Perennial
