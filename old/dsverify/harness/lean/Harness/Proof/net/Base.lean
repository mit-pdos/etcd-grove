/-
Shared definitions of the specs of `net`'s trusted model (`Harness/TrustedCode/net.lean`):
* the typed points-to of the model's trusted layouts (`netFD`, `TCPListener`, the model-only
  `connError`), which proofgen does not emit for a trusted type, and the struct-field facts of
  `model.Assumptions` as instances;
* `net`'s package-initialized state (`isInit`, `isPkgInit pkg_id.net`): the model's
  `poll.ErrNetClosing` and `net.ErrClosed`, which the model's errors for a closed end use;
* the representation predicates of a connection end (`ownTCPConn`) and of a listener
  (`ownListener`), both persistent; a connection end's local and remote addresses, and a
  listener's address, are non-`nil` `*TCPAddr`s (`isTCPAddr`, `connAddrs`, `listenerAddr`), whose
  `String()` returns some string (`wp_Addr_String`);
* what a returned `error` is (`opErr`, `connErr`, `opResult`) and what `Dial` and `Accept`
  return (`newConnResult`: on success the new end's tokens and its fresh token `connFresh`, for
  per-connection ghost state keyed by the connection id);
* specs of the model's helpers (not Go functions: `wp_codeErr`, `wp_connResult`, `wp_newFD`,
  ...), of `Dial.impl` (which `DialTimeout` calls) and of `model.setDeadline`.
Everything said about the network comes from the extension's specs
(`Harness/GooseLang/Ext/NetConn/Specs.lean`).
-/
module

public import Harness.GeneratedProof.net
public import Harness.GooseLang.Ext.NetConn.Specs
public import Perennial.Proof.io.Base
public import Perennial.Proof.time.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net

/-! The struct-field facts of the trusted layouts (`model.Assumptions`), as instances, as goose's
`TypeAssumptions` are. -/
attribute [instance] model.Assumptions.netFD_get_id model.Assumptions.netFD_get_side
  model.Assumptions.netFD_get_laddr model.Assumptions.netFD_get_raddr
  model.Assumptions.netFD_set_id model.Assumptions.netFD_set_side
  model.Assumptions.netFD_set_laddr model.Assumptions.netFD_set_raddr
  model.Assumptions.TCPListener_get_fd model.Assumptions.TCPListener_set_fd
  model.Assumptions.connError_type_repr model.Assumptions.connError_underlying
  model.Assumptions.connError_get_timeout model.Assumptions.connError_get_temporary
  model.Assumptions.connError_set_timeout model.Assumptions.connError_set_temporary
  model.Assumptions.connError_method_set model.Assumptions.connError_ptr_method_set
  model.Assumptions.connError_ptr_Error_unfold model.Assumptions.connError_ptr_Timeout_unfold
  model.Assumptions.connError_ptr_Temporary_unfold

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! The model's type names are goose's. -/

theorem netFD_ty_eq : model.netFDTy = netFD.ty := by unfold netFD.ty; rfl
theorem conn_ty_eq : model.connTy = conn.ty := by unfold conn.ty; rfl
theorem TCPConn_ty_eq : model.TCPConnTy = TCPConn.ty := by unfold TCPConn.ty; rfl
theorem TCPListener_ty_eq : model.TCPListenerTy = TCPListener.ty := by unfold TCPListener.ty; rfl
theorem Conn_ty_eq : model.ConnTy = Conn.ty := by unfold Conn.ty; rfl
theorem Listener_ty_eq : model.ListenerTy = Listener.ty := by unfold Listener.ty; rfl
theorem Addr_ty_eq : model.AddrTy = Addr.ty := by unfold Addr.ty; rfl
theorem TCPAddr_ty_eq : model.TCPAddrTy = TCPAddr.ty := by unfold TCPAddr.ty; rfl
theorem IP_ty_eq : model.IPTy = IP.ty := by unfold IP.ty; rfl
theorem OpError_ty_eq : model.OpErrorTy = OpError.ty := by unfold OpError.ty; rfl
theorem Time_ty_eq : model.timeTy = time.Time.ty := by unfold time.Time.ty; rfl

/-! The typed points-to of the trusted layouts, as proofgen emits it for a translated struct. -/

instance netFD_fields_unfold :
    EqualsUnfold [go.field_decl.FieldDecl go!"id" go.uint64,
      go.field_decl.FieldDecl go!"side" go.bool,
      go.field_decl.FieldDecl go!"laddr" model.AddrTy,
      go.field_decl.FieldDecl go!"raddr" model.AddrTy]
    [go.field_decl.FieldDecl go!"id" go.uint64,
      go.field_decl.FieldDecl go!"side" go.bool,
      go.field_decl.FieldDecl go!"laddr" model.AddrTy,
      go.field_decl.FieldDecl go!"raddr" model.AddrTy] := ⟨rfl⟩

instance TCPListener_fields_unfold :
    EqualsUnfold [go.field_decl.FieldDecl go!"fd" (go.GoType.PointerType model.netFDTy)]
      [go.field_decl.FieldDecl go!"fd" (go.GoType.PointerType model.netFDTy)] := ⟨rfl⟩

instance connError_fields_unfold :
    EqualsUnfold [go.field_decl.FieldDecl go!"timeout" go.bool,
      go.field_decl.FieldDecl go!"temporary" go.bool]
    [go.field_decl.FieldDecl go!"timeout" go.bool,
      go.field_decl.FieldDecl go!"temporary" go.bool] := ⟨rfl⟩

noncomputable instance netFD_typed_pointsto : TypedPointsto (GF := GF) net.netFD where
  typedPointstoDef l v dq := iprop(
    "id" ∷ typedPointsto (structFieldRef net.netFD go!"id" l) v.id' dq ∗
    "side" ∷ typedPointsto (structFieldRef net.netFD go!"side" l) v.side' dq ∗
    "laddr" ∷ typedPointsto (structFieldRef net.netFD go!"laddr" l) v.laddr' dq ∗
    "raddr" ∷ typedPointsto (structFieldRef net.netFD go!"raddr" l) v.raddr' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

noncomputable instance TCPListener_typed_pointsto : TypedPointsto (GF := GF) net.TCPListener where
  typedPointstoDef l v dq := iprop(
    "fd" ∷ typedPointsto (structFieldRef net.TCPListener go!"fd" l) v.fd' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

noncomputable instance connError_typed_pointsto : TypedPointsto (GF := GF) net.model.connError where
  typedPointstoDef l v dq := iprop(
    "timeout" ∷ typedPointsto (structFieldRef net.model.connError go!"timeout" l) v.timeout' dq ∗
    "temporary" ∷ typedPointsto (structFieldRef net.model.connError go!"temporary" l)
      v.temporary' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

variable [package_sem' : net.Assumptions] [model_sem : net.model.Assumptions]

/-- The model names `net.Addr` by its Go name (`model.AddrTy`), as the layouts of `netFD` do. -/
instance AddrTy_underlying : go.UnderlyingDirectedEq model.AddrTy Addr.underlying := by
  rw [Addr_ty_eq]; infer_instance

noncomputable instance netFD_into_val_typed :
    IntoValTypedUnderlying (GF := GF) net.netFD net.netFD.underlying := by
  solve_into_val_typed_struct

noncomputable instance TCPListener_into_val_typed :
    IntoValTypedUnderlying (GF := GF) net.TCPListener net.TCPListener.underlying := by
  solve_into_val_typed_struct

noncomputable instance connError_into_val_typed :
    IntoValTypedUnderlying (GF := GF) net.model.connError net.model.connError.underlying := by
  solve_into_val_typed_struct

end def_

section addr
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The networks the model's `Listen`, `Dial` and `DialTimeout` cover: `"tcp"`, and `"tcp4"`,
which they treat as `"tcp"` (`model.tcpNetwork`, `TrustedCode/net.lean`). -/
def tcpNet (nw : GoString) : Prop := nw = go!"tcp" ∨ nw = go!"tcp4"

theorem tcpNet_tcp : tcpNet go!"tcp" := Or.inl rfl
theorem tcpNet_tcp4 : tcpNet go!"tcp4" := Or.inr rfl

/-- `a` is a non-`nil` `*TCPAddr` as a `net.Addr`: what the model's `Dial` and `Accept` put in a
connection's `laddr` and `raddr` (`model.arbitraryAddr`). -/
def isTCPAddr (a : GoInterface) : Prop :=
  ∃ x : Loc, a = interface.mkOk (go.GoType.PointerType TCPAddr.ty) #x

end addr

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The `*netFD` `fd` is the socket of the extension's id `id` at end `side` (a listener's has
`side` false), with some local and remote addresses, which never change (persistent). -/
def ownFD (fd : Loc) (id : w64) (side : Bool) : IProp GF :=
  iprop(structFieldRef net.netFD go!"id" fd ↦□ id ∗
    structFieldRef net.netFD go!"side" fd ↦□ side ∗
    ∃ la ra : GoInterface, structFieldRef net.netFD go!"laddr" fd ↦□ la ∗
      structFieldRef net.netFD go!"raddr" fd ↦□ ra)

/-- The addresses of a connection's `*netFD` `fd` are non-`nil` `*TCPAddr`s (persistent). -/
def connAddrs (fd : Loc) : IProp GF :=
  iprop(∃ la ra : GoInterface, structFieldRef net.netFD go!"laddr" fd ↦□ la ∗
    structFieldRef net.netFD go!"raddr" fd ↦□ ra ∗ ⌜isTCPAddr la ∧ isTCPAddr ra⌝)

/-- The `*TCPConn` `c` is end `side` of the extension's connection `cid` (persistent): what
`Close`, the deadline setters and the address getters need; `Read` and `Write` also need the
end's tokens (`recvTok`, `sendTok`). Its addresses are `*TCPAddr`s (`connAddrs`). -/
def ownTCPConn (c : Loc) (cid : w64) (side : Bool) : IProp GF :=
  iprop(∃ fd : Loc,
    structFieldRef net.conn go!"fd" (structFieldRef net.TCPConn go!"conn" c) ↦□ fd ∗
    ownFD fd cid side ∗ isConnP cid ∗ connAddrs fd)

/-- The local address of a listener's `*netFD` `fd` is a non-`nil` `*TCPAddr` (persistent). -/
def listenerAddr (fd : Loc) : IProp GF :=
  iprop(∃ la : GoInterface, structFieldRef net.netFD go!"laddr" fd ↦□ la ∗ ⌜isTCPAddr la⌝)

/-- The `*TCPListener` `l` is the extension's listener `lid`, made by `Listen(a)`
(persistent). Its address (`Addr`) is a `*TCPAddr` (`listenerAddr`), not tied to `a`. -/
def ownListener (l : Loc) (lid : w64) (a : GoString) : IProp GF :=
  iprop(∃ fd : Loc, structFieldRef net.TCPListener go!"fd" l ↦□ fd ∗ ownFD fd lid false ∗
    isListener lid a ∗ listenerAddr fd)

instance ownFD_persistent (fd : Loc) (id : w64) (side : Bool) :
    Persistent (ownFD (GF := GF) fd id side) := by
  unfold ownFD; infer_instance

instance connAddrs_persistent (fd : Loc) : Persistent (connAddrs (GF := GF) fd) := by
  unfold connAddrs; infer_instance

instance listenerAddr_persistent (fd : Loc) : Persistent (listenerAddr (GF := GF) fd) := by
  unfold listenerAddr; infer_instance

instance ownTCPConn_persistent (c : Loc) (cid : w64) (side : Bool) :
    Persistent (ownTCPConn (GF := GF) c cid side) := by
  unfold ownTCPConn; infer_instance

instance ownListener_persistent (l : Loc) (lid : w64) (a : GoString) :
    Persistent (ownListener (GF := GF) l lid a) := by
  unfold ownListener; infer_instance

end preds

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The model-only variable holding the model's `poll.ErrNetClosing` (`ErrClosed.init`). -/
abbrev errNetClosing : GoString := go!"net#model.errNetClosing"

/-- The error the model returns (inside an `*OpError`) for a closed end: `&connError{x}` as an
`error`. -/
abbrev errClosedVal (x : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType model.connErrorTy) #x

/-- The package-initialized state of `net` (persistent): `net#model.errNetClosing` and
`net.ErrClosed` hold the one closed-end error `&connError{false, false}` (`ErrClosed.init`).
Go's other package variables are not allocated by the model (`TrustedCode/net.lean`). -/
abbrev isInit : IProp GF :=
  iprop(∃ x : Loc, globalAddr errNetClosing ↦□ errClosedVal x ∗
    x ↦□ model.connError.mk false false ∗
    globalAddr net.ErrClosed ↦□ errClosedVal x)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.net ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.net

theorem io_init_of_net :
    isPkgInit (PROP := IProp GF) pkg_id.net ⊢ isPkgInit (PROP := IProp GF) pkg_id.io := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.net).trans ?_
  show iprop(isPkgInit pkg_id.time ∗ isPkgInit pkg_id.io ∗ True) ⊢ _
  iintro ⟨-, H, -⟩
  iexact H

end init

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `err` is a fresh `*OpError` of operation `op` (as an `error`), whose `Err` is, for a closed
end or listener (`code = errClosed`), the model's `poll.ErrNetClosing`, the value
`net.ErrClosed` holds (`isInit`). Its fields are given persistently (Go code does not write
them). -/
def opErr (op : GoString) (code : w64) (err : GoInterface) : IProp GF :=
  iprop(∃ (e : Loc) (inner : GoInterface),
    ⌜err = interface.mkOk (go.GoType.PointerType OpError.ty) #e⌝ ∗
    structFieldRef net.OpError go!"Op" e ↦□ op ∗
    structFieldRef net.OpError go!"Err" e ↦□ inner ∗
    if code = NetConn.errClosed then globalAddr errNetClosing ↦□ inner else True)

/-- `err` is the `error` the model returns for operation `op` with result `code`: `nil` on
success, the value of `io.EOF` at the end of a stream, an `*OpError` otherwise (`opErr`). -/
def connErr (op : GoString) (code : w64) (err : GoInterface) : IProp GF :=
  if code = NetConn.errNone then iprop(⌜err = interface.nil⌝)
  else if code = NetConn.errEOF then iprop(⌜err ≠ interface.nil⌝ ∗ globalAddr io.EOF ↦□ err)
  else opErr op code err

/-- `err` is the `error` the model returns for a listener's `Close` with result `code`: `nil` on
success, an `*OpError` of `op` otherwise. -/
def opResult (op : GoString) (code : w64) (err : GoInterface) : IProp GF :=
  if code = NetConn.errNone then iprop(⌜err = interface.nil⌝) else opErr op code err

instance opErr_persistent (op : GoString) (code : w64) (err : GoInterface) :
    Persistent (opErr (GF := GF) op code err) := by
  unfold opErr
  by_cases h : code = NetConn.errClosed <;> simp only [h, ite_true, ite_false] <;> infer_instance

instance connErr_persistent (op : GoString) (code : w64) (err : GoInterface) :
    Persistent (connErr (GF := GF) op code err) := by
  unfold connErr; split
  · infer_instance
  · split <;> infer_instance

instance opResult_persistent (op : GoString) (code : w64) (err : GoInterface) :
    Persistent (opResult (GF := GF) op code err) := by
  unfold opResult; split <;> infer_instance

theorem connErr_nil (op : GoString) (code : w64) (err : GoInterface) :
    connErr (GF := GF) op code err ⊢ ⌜err = interface.nil ↔ code = NetConn.errNone⌝ := by
  unfold connErr
  by_cases h0 : code = NetConn.errNone
  · simp only [h0, ite_true]
    iintro %h; ipureintro; simp [h]
  · simp only [h0, ite_false]
    by_cases h1 : code = NetConn.errEOF
    · simp only [h1, ite_true]
      iintro ⟨%h, -⟩; ipureintro; subst h1; simp [h]
    · simp only [h1, ite_false]
      unfold opErr
      iintro ⟨%e, %inner, %h, -⟩
      ipureintro; subst h; simp [interface.mkOk]

theorem opErr_ne_nil (op : GoString) (code : w64) (err : GoInterface) :
    opErr (GF := GF) op code err ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold opErr
  iintro ⟨%e, %inner, %h, -⟩
  ipureintro; subst h; simp [interface.mkOk]

end errs

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The results `(cv, err)` of `Dial` (`op` `"dial"`, `side` false) or `Accept` (`"accept"`,
`side` true): a new `*TCPConn` as a `net.Conn` and no error, with the end of a new connection
(writing with protocol `Pout`, reading with `Pin`, nothing written or read yet) and its fresh
token (`connFresh cid side`, handed out once per end); or `nil` and an
`*OpError` of `op`, a non-`nil` interface value (`interface.ok i`, the form `if err != nil`
evaluates on). -/
def newConnResult (op : GoString) (side : Bool) (Pout Pin : Proto GF) (cv err : GoInterface) :
    IProp GF :=
  iprop((∃ (c : Loc) (cid : w64),
      ⌜cv = interface.mkOk (go.GoType.PointerType TCPConn.ty) #c ∧ err = interface.nil⌝ ∗
      ownTCPConn c cid side ∗ connEnd cid side Pout Pin [] [] ∗ connFresh cid side) ∨
    (∃ i, ⌜cv = interface.nil ∧ err = interface.ok i⌝ ∗
      ∃ code : w64, ⌜code ≠ NetConn.errNone⌝ ∗ opErr op code err))

/-- An end's tokens name an existing connection. -/
theorem connEnd_isConnP (cid : w64) (side : Bool) (Pout Pin : Proto GF) (W R : List w8) :
    connEnd (G := hG.goose_globalGS) cid side Pout Pin W R ⊢
      connEnd cid side Pout Pin W R ∗ isConnP cid := by
  refine persistent_entails_left ?_
  unfold connEnd sendTok isConnP isConnG sendTokG
  iintro ⟨⟨%n, #Hn, -⟩, -⟩
  iexists n; iexact Hn

end results

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [model_sem : net.model.Assumptions]

/-! Specs of the model's helpers (not Go functions). -/

/-- `model.tcpNetwork` on `"tcp"` or `"tcp4"`: `"tcp"`. -/
theorem wp_tcpNetwork (nw : GoString) (hnw : tcpNet nw) :
    {{ (True : IProp GF) }}
      (App (Val model.tcpNetwork) (Val #nw))
    {{ RET #(go!"tcp"); True }} := by
  rcases hnw with rfl | rfl
  · wp_start
    iapply HΦ; itrivial
  · wp_start
    iapply HΦ; itrivial

theorem wp_arbitraryBool :
    {{ (True : IProp GF) }}
      (App (Val model.arbitraryBool) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  iapply HΦ; itrivial

theorem wp_connErr (t tmp : Bool) :
    {{ (True : IProp GF) }}
      (App (App (Val model.connErr) (Val #t)) (Val #tmp))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType model.connErrorTy) #x);
        x ↦ model.connError.mk t tmp }} := by
  wp_start
  wp_alloc x as Hx
  wp_auto
  iapply HΦ
  iframe

theorem wp_codeErr (code : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net }}
      (App (Val model.codeErr) (Val #code))
    {{ (inner : GoInterface), RET #inner;
        if code = NetConn.errClosed then globalAddr errNetClosing ↦□ inner else True }} := by
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨%x, #Hnc, #Hx, #HE⟩
  wp_if_destruct
  · wp_apply wp_connErr as %y -
    iapply HΦ
    simp only [show NetConn.errTimeout ≠ NetConn.errClosed from by decide, ↓reduceIte]
    itrivial
  · wp_if_destruct
    · iapply HΦ
      iexact Hnc
    · wp_apply wp_arbitraryBool as %b1 -
      wp_apply wp_arbitraryBool as %b2 -
      wp_apply wp_connErr as %y -
      iapply HΦ
      split
      · exfalso; simp_all
      · itrivial

theorem wp_opError (op : GoString) (src addr err : GoInterface) :
    {{ (True : IProp GF) }}
      (App (App (App (App (Val model.opError) (Val #op)) (Val #src)) (Val #addr)) (Val #err))
    {{ (e : Loc), RET #(interface.mkOk (go.GoType.PointerType OpError.ty) #e);
        structFieldRef net.OpError go!"Op" e ↦□ op ∗
        structFieldRef net.OpError go!"Err" e ↦□ err }} := by
  wp_start
  rw [OpError_ty_eq, Addr_ty_eq]
  wp_auto
  wp_alloc e as He
  iStructNamed He
  iapply wp_fupd
  wp_auto
  ipersist Op
  ipersist Err
  imodintro
  iapply HΦ
  iframe Op Err

theorem wp_connResult (fd : Loc) (id : w64) (side : Bool) (op : GoString) (code : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ ownFD fd id side }}
      (App (App (App (Val model.connResult) (Val #fd)) (Val #op)) (Val #code))
    {{ (err : GoInterface), RET #err; connErr op code err }} := by
  unfold ownFD
  wp_start as ⟨#Hid, #Hside, %la, %ra, #Hla, #Hra⟩
  rw [netFD_ty_eq, Addr_ty_eq]
  unfold connErr
  wp_if_destruct
  · iapply HΦ
    ipureintro; trivial
  · ihave #Hio := io_init_of_net $$ Hpkg
    ihave #HEOF := io.eof_of_init $$ Hio
    unfold errors.newVar
    icases HEOF with ⟨%eof, #HEOF, -⟩
    wp_if_destruct
    · iapply HΦ
      simp (config := {decide := true}) only [↓reduceIte]
      iframe HEOF
      ipureintro; simp [interface.mkOk]
    · wp_apply wp_codeErr as %inner Hinner
      wp_apply wp_opError as %e ⟨#HOp, #HErr⟩
      iapply HΦ
      rename_i h0
      simp only [h0, Hif, ↓reduceIte]
      unfold opErr
      iexists e, inner
      iframe HOp HErr Hinner
      ipureintro; rfl

theorem wp_fdOf (c fd : Loc) :
    {{ (structFieldRef net.conn go!"fd" c ↦□ fd : IProp GF) }}
      (App (Val model.fdOf) (Val #c))
    {{ RET #fd; True }} := by
  wp_start as #Hfd
  rw [netFD_ty_eq, conn_ty_eq]
  wp_auto
  iapply HΦ; itrivial

theorem wp_idSide (fd : Loc) (id : w64) (side : Bool) :
    {{ ownFD (GF := GF) fd id side }}
      (App (Val model.idSide) (Val #fd))
    {{ RET (PairV #id #side); True }} := by
  unfold ownFD
  wp_start as ⟨#Hid, #Hside, -⟩
  rw [netFD_ty_eq]
  wp_auto
  iapply HΦ; itrivial

/-- `fmt.arbitraryString` (a helper of Perennial's trusted `fmt`, which the model calls for
addresses) returns some string; Perennial's `fmt.wp_arbitraryString`, whose proof needs nothing
of `fmt`, restated without `fmt.Assumptions` (which `net`'s do not include). -/
theorem wp_arbitraryString :
    {{ (True : IProp GF) }}
      (App (Val fmt.arbitraryString) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  iintro %Φ - HΦ
  unfold fmt.arbitraryString
  wp_auto
  ihave IH : iprop(∃ str : GoString, "s" ∷ s_ptr ↦ str) $$ [s]
  · iexists _; iframe
  wp_for IH
  wp_apply wp_ArbitraryInt as %c -
  wp_if_destruct
  · wp_apply wp_ArbitraryInt as %b -
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z b)]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z b)))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    wp_apply wp_bytes_to_string $$ Hsl as -
    wp_for_post
    iframe
    iexists _
    iframe
  · have Hf : (!decide (c = W64 0)) = false := by
      revert Hif; cases (!decide (c = W64 0)) <;> simp
    rw [Hf]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

theorem wp_arbitraryAddr :
    {{ (True : IProp GF) }}
      (App (Val model.arbitraryAddr) (Val #()))
    {{ (a : GoInterface), RET #a; ⌜isTCPAddr a⌝ }} := by
  wp_start
  rw [TCPAddr_ty_eq, IP_ty_eq, Addr_ty_eq]
  wp_apply wp_arbitraryString as %ip -
  wp_apply wp_string_to_bytes as %sl -
  wp_apply wp_ArbitraryInt as %p -
  wp_apply wp_arbitraryString as %z -
  wp_alloc x as Hx
  wp_auto
  iapply HΦ
  ipureintro; exact ⟨x, rfl⟩

/-- `(*TCPAddr).String` (the model's `TCPAddr.String.impl`, `TrustedCode/net.lean`): some
string, for any receiver. -/
theorem wp_TCPAddr_String (x : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (x @!! go.GoType.PointerType TCPAddr.ty @!! go!"String")) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  wp_start
  wp_apply wp_arbitraryString as %s -
  iapply HΦ; itrivial

/-- `a.String()` on a `net.Addr` that is a non-`nil` `*TCPAddr` (`isTCPAddr`): the dynamic call
resolves to `(*TCPAddr).String` (goose's method set of `*TCPAddr`), whose model
(`TrustedCode/net.lean`, `TCPAddr.String.impl`) returns an arbitrary string; it does not
panic. -/
theorem wp_Addr_String (a : GoInterface) (ha : isTCPAddr a) :
    {{ (True : IProp GF) }}
      (App (App (Val (GoInstruction (MethodResolve Addr.ty go!"String"))) (Val #a)) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  obtain ⟨x, rfl⟩ := ha
  wp_start
  wp_auto
  wp_apply wp_TCPAddr_String x as %s -
  iapply HΦ; itrivial

theorem wp_maybeAddr :
    {{ (True : IProp GF) }}
      (App (Val model.maybeAddr) (Val #()))
    {{ (a : GoInterface), RET #a; True }} := by
  wp_start
  wp_apply wp_arbitraryBool as %b -
  wp_if_destruct
  all_goals first
    | (iapply HΦ; itrivial)
    | (wp_apply wp_arbitraryAddr as %a -; iapply HΦ; itrivial)

theorem wp_newFD (id : w64) (side : Bool) (la ra : GoInterface) :
    {{ (True : IProp GF) }}
      (App (App (App (App (Val model.newFD) (Val #id)) (Val #side)) (Val #la)) (Val #ra))
    {{ (fd : Loc), RET #fd; ownFD fd id side ∗ structFieldRef net.netFD go!"laddr" fd ↦□ la ∗
        structFieldRef net.netFD go!"raddr" fd ↦□ ra }} := by
  wp_start
  rw [netFD_ty_eq, Addr_ty_eq]
  wp_auto
  iapply wp_fupd
  wp_alloc fd as Hfd
  iStructNamed Hfd
  ipersist id
  ipersist side
  ipersist laddr
  ipersist raddr
  imodintro
  iapply HΦ
  unfold ownFD
  iframe id side laddr raddr

theorem wp_newConn (fd : Loc) :
    {{ (True : IProp GF) }}
      (App (Val model.newConn) (Val #fd))
    {{ (c : Loc), RET #(interface.mkOk (go.GoType.PointerType TCPConn.ty) #c);
        structFieldRef net.conn go!"fd" (structFieldRef net.TCPConn go!"conn" c) ↦□ fd }} := by
  wp_start
  rw [netFD_ty_eq, conn_ty_eq, TCPConn_ty_eq, Conn_ty_eq]
  wp_auto
  iapply wp_fupd
  wp_alloc c as Hc
  iStructNamed Hc
  iStructNamed conn
  ipersist fd
  wp_auto
  imodintro
  iapply HΦ
  iexact fd

end wps

section modelWps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [model_sem : net.model.Assumptions]

/-- The model of `Dial` (`Dial.impl`, which `DialTimeout` calls too). -/
theorem wp_Dial_impl (nw a : GoString) (hnw : tcpNet nw) (P Q : Proto GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrProto a P Q }}
      (App (App (Val Dial.impl) (Val #nw)) (Val #a))
    {{ (cv err : GoInterface), RET (PairV #cv #err);
        newConnResult go!"dial" false P Q cv err }} := by
  wp_start as #Hpr
  wp_apply wp_tcpNetwork nw hnw
  wp_apply NetConn.wp_Dial a P Q $$ Hpr as %cid %code Hres
  wp_if_destruct
  · wp_apply wp_arbitraryAddr as %ra %Hra
    wp_apply wp_arbitraryAddr as %la %Hla
    wp_apply wp_newFD as %fd ⟨#Hfd, #Hlp, #Hrp⟩
    wp_apply wp_newConn as %c #Hc
    icases Hres with ⟨Hres, Hf⟩
    ihave ⟨Hres, #Hcp⟩ := connEnd_isConnP $$ Hres
    iapply HΦ
    unfold newConnResult
    ileft
    iexists c, cid
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · unfold ownTCPConn connAddrs
      iexists fd
      iframe Hc Hfd Hcp
      iexists la, ra
      iframe Hlp Hrp
      ipureintro; exact ⟨Hla, Hra⟩
    · iframe Hres Hf
  · wp_apply wp_codeErr as %inner Hinner
    wp_apply wp_maybeAddr as %ad -
    wp_apply wp_opError as %e ⟨#HOp, #HErr⟩
    iapply HΦ
    unfold newConnResult
    iright
    iexists _
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists code
    isplitr
    · ipureintro; assumption
    unfold opErr
    iexists e, inner
    iframe HOp HErr Hinner
    ipureintro; rfl

/-- `model.setDeadline` on the `*conn` `cc` (inside a `*TCPConn`). -/
theorem wp_setDeadline (cc fd : Loc) (cid : w64) (side : Bool) (which : w64)
    (hw : which = 0 ∨ which = 1 ∨ which = 2) (t : time.Time) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ structFieldRef net.conn go!"fd" cc ↦□ fd ∗
        ownFD fd cid side ∗ isConnP cid }}
      (App (App (App (Val model.setDeadline) (Val #cc)) (Val #which)) (Val #t))
    {{ (err : GoInterface), RET #err; ∃ code, connErr go!"set" code err }} := by
  wp_start as ⟨#Hfd, #HFD, #Hc⟩
  wp_apply wp_fdOf $$ Hfd
  rw [Time_ty_eq]
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals
    wp_apply wp_idSide $$ HFD
    wp_apply wp_idSide $$ HFD
    wp_apply NetConn.wp_SetDeadline cid side which _ hw $$ Hc as %code -
    wp_apply wp_connResult $$ [$HFD] as %err Herr
    iapply HΦ
    iexists code
    iexact Herr

end modelWps

end net

end Perennial
