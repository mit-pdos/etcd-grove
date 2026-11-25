/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver/svc`: the stream methods' contracts

grpc's wrapped server end (`srvStreamIs`, `InvGrpcStream.lean`) has `Recv`, `Send` and `Context`;
the driver's `ClientStream` also answers with `SendAndClose` (`sacOk`: `SendMsg` on the raw end,
`sacOk_of_raw`). The generated handlers call the service's stream methods with that end
(`strmMethodOk`: `ClientStream`, `Bidi`, called with the stream), or with the first request already
received (`ssMethodOk`: `ServerStream`, called with the request and the stream).

**Errors**: an `errors.New` error is one grpc's server takes (`errStr_srvErrOk`), with its message
as its description (`errStr_descIs`); `io.EOF` is one (`eof_srvErrOk`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.google_golang_org.protobuf.types.known.wrapperspb.PerTypeStringValue
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Base
public import Proof.errors.NewVar
public import Perennial.Proof.io.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The driver's stream message (`StringValue`, `pbStringValueST`). -/
abbrev strmT : StreamMsg GF := pbStringValueS (GF := GF)

/-- **The wrapped server end's `SendAndClose`** (persistent): as `srvStreamIs`'s `Send`. -/
def sacOk {Rep : StreamMsg GF} (st : GoInterface) (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF) :
    IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (L : List Rep.M) (l : Loc) (m : Rep.M),
      {{ srvSendTok (Rep := Rep) γ L ∗ Rep.send l m ∗ Dn L.length m }}
        (App (Val #(methods si.ty go!"SendAndClose" si.v)) (Val #l))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ srvSendTok (Rep := Rep) γ (L ++ [m])) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ streamErr err ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
            ∃ L' : List Rep.M, ⌜L' = L ∨ L' = L ++ [m]⌝ ∗ srvSendTok (Rep := Rep) γ L') }}))

instance sacOk_persistent {Rep : StreamMsg GF} (st : GoInterface) (γ : StreamNames)
    (Dn : Nat → Rep.M → IProp GF) : Persistent (sacOk st γ Dn) := by
  unfold sacOk; infer_instance

/-- **A stream method called with the stream** (`ClientStream`, `Bidi`; persistent): as
`grpcStreamHandlerOk`, on the wrapped end with its `SendAndClose`. -/
def strmMethodOk {Req Rep : StreamMsg GF} (h : val) (S : IProp GF) (Up : Nat → Req.M → IProp GF)
    (Spec : GrpcMd → StreamSpec Rep) : IProp GF :=
  iprop(□ ∀ (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (st : GoInterface) (Φ : val → IProp GF),
    grpcStreamSpecAt Spec ci γ Dn -∗ S -∗ srvStreamIs st γ Req Rep Up Dn ci cd -∗ sacOk st γ Dn -∗
    srvRecvTok (Req := Req) γ [] -∗ srvSendTok (Rep := Rep) γ [] -∗
    ▷ (∀ err : GoInterface, go_etcd_io.etcd.cache.v3.srvErrOk err -∗ S -∗ Φ #err) -∗
    WP (App (Val h) (Val #st)) {{ Φ }})

instance strmMethodOk_persistent {Req Rep : StreamMsg GF} (h : val) (S : IProp GF)
    (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) :
    Persistent (strmMethodOk h S Up Spec) := by
  unfold strmMethodOk; infer_instance

/-- **A stream method called with the first request and the stream** (`ServerStream`;
persistent): the request received (`Req.recv r v`, the receiver's token at `[v]`). -/
def ssMethodOk {Req Rep : StreamMsg GF} (h : val) (S : IProp GF) (Up : Nat → Req.M → IProp GF)
    (Spec : GrpcMd → StreamSpec Rep) : IProp GF :=
  iprop(□ ∀ (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (st : GoInterface) (r : Loc) (v : Req.M)
      (Φ : val → IProp GF),
    grpcStreamSpecAt Spec ci γ Dn -∗ S -∗ srvStreamIs st γ Req Rep Up Dn ci cd -∗
    Req.recv r v -∗ srvRecvTok (Req := Req) γ [v] -∗ srvSendTok (Rep := Rep) γ [] -∗
    ▷ (∀ err : GoInterface, go_etcd_io.etcd.cache.v3.srvErrOk err -∗ S -∗ Φ #err) -∗
    WP (App (App (Val h) (Val #r)) (Val #st)) {{ Φ }})

instance ssMethodOk_persistent {Req Rep : StreamMsg GF} (h : val) (S : IProp GF)
    (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) :
    Persistent (ssMethodOk h S Up Spec) := by
  unfold ssMethodOk; infer_instance

/-- **An `errors.New` error is one grpc's `status` takes** (`statusErrOk`): a `*errorString` is a
leaf without `Is` or `GRPCStatus` (`ErrorStringLeaf`), and its `Error()` returns its message. -/
theorem errStr_statusErrOk [_root_.Perennial.errors.Assumptions] (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"Error" #x)) (Val #())) {{ Φ }}) ⊢
    go_etcd_io.etcd.cache.v3.statusErrOk
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  obtain ⟨-, hl, hIs, hG⟩ := EtcdGrove.errorString_errLeaf x
  iintro #Hm
  unfold go_etcd_io.etcd.cache.v3.statusErrOk
  iintro !> %e %he
  cases he
  isplitr
  · iexists msg
    unfold go_etcd_io.etcd.cache.v3.errorMsgIs
    iexact Hm
  isplitr
  · ipureintro; exact hl
  isplitr
  rotate_left
  · ipureintro; exact ⟨EtcdGrove.ErrorStringLeaf.noFormat, EtcdGrove.errorString_errorSig⟩
  unfold go_etcd_io.etcd.cache.v3.grpcErrMethodsOk
  isplitl
  · iintro %h
    simp only [hG.1] at h; cases h
  · iintro %h
    exact absurd h hIs

/-- **An `errors.New` error is one grpc's server takes** (`srvErrOk`). -/
theorem errStr_srvErrOk [_root_.Perennial.errors.Assumptions] (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"Error" #x)) (Val #())) {{ Φ }}) ⊢
    go_etcd_io.etcd.cache.v3.srvErrOk
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  iintro #Hm
  iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk
  iapply errStr_statusErrOk $$ Hm

/-- **An `errors.New` error's description is its message** (`descIs`). -/
theorem errStr_descIs [_root_.Perennial.errors.Assumptions] (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"Error" #x)) (Val #())) {{ Φ }}) ⊢
    go_etcd_io.etcd.cache.v3.descIs
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) msg := by
  iintro #Hm
  iapply (go_etcd_io.etcd.cache.v3.descIs_of_msg
    ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ msg
    (go_etcd_io.etcd.cache.v3.ptrTy_ne_etcdError _)
    (by rw [EtcdGrove.ErrorStringLeaf.noGRPC]; simp))
  unfold go_etcd_io.etcd.cache.v3.errorMsgIs
  iexact Hm

/-- **`io.EOF`'s value is one grpc's `status` takes.** -/
theorem eof_statusErrOk [_root_.Perennial.errors.Assumptions] [_root_.Perennial.io.Assumptions]
    (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ eofIs err ⊢ go_etcd_io.etcd.cache.v3.statusErrOk err := by
  iintro ⟨#Hio, #He⟩
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Hpt, #_, #Hmsg⟩
  iunfold eofIs at He
  icombine He Hpt gives %Heq
  subst Heq
  iapply errStr_statusErrOk $$ Hmsg

/-- **`io.EOF`'s value is one grpc's server takes.** -/
theorem eof_srvErrOk [_root_.Perennial.errors.Assumptions] [_root_.Perennial.io.Assumptions]
    (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ eofIs err ⊢ go_etcd_io.etcd.cache.v3.srvErrOk err := by
  iintro ⟨#Hio, #He⟩
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Hpt, #_, #Hmsg⟩
  iunfold eofIs at He
  icombine He Hpt gives %Heq
  subst Heq
  iapply errStr_srvErrOk $$ Hmsg

/-- **`SendAndClose` on the generated wrapper** of grpc's raw end: `SendMsg` on the raw end. -/
theorem sacOk_of_raw [grpc_sem : google_golang_org.grpc.Assumptions]
    {Req Rep : StreamMsg GF} (V W : Type) [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V Req.ty] [TypeRepr Req.ty V]
    [ZeroVal W] [TypeRepr Rep.ty W]
    (p : Loc) (st : GoInterface) (γ : StreamNames) (Up : Nat → Req.M → IProp GF)
    (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    structFieldRef (google_golang_org.grpc.GenericServerStream V W) go!"ServerStream" p ↦□ st ∗
      srvRawStreamIsW st γ Req Rep Up Dn ci cd ⊢
    sacOk (Rep := Rep) (interface.mkOk (go.GoType.PointerType
      (google_golang_org.grpc.GenericServerStream.ty Req.ty Rep.ty)) #p) γ Dn := by
  iintro ⟨#Hf, #Hraw⟩
  unfold sacOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro !> %L %l %m %Φ !> ⟨Htok, Hs, HDn⟩ HΦ
  wp_method_call
  try wp_call
  iunfold srvRawStreamIsW at Hraw
  icases Hraw with ⟨%si, %Hst, -, #HSend, -⟩
  subst Hst
  wp_auto
  wp_bind (App (Val #(methods si.ty go!"SendMsg" si.v)) _)
  iapply HSend $$ %L %l %m [Htok Hs HDn]
  · iframe
  iintro !> %err ⟨-, Hres⟩
  wp_auto
  iapply HΦ
  iexact Hres

end defs

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

end Perennial
