/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver/svc`: the client's stream ends

The generated stubs wrap grpc's raw client end in `&grpc.GenericClientStream[Msg, Msg]{...}`
(`cliBidiStreamIs`, `cliBidiStreamIs_of_raw`: `Send`, `Recv`, `CloseSend`, `Context`); a client stream
also answers with `CloseAndRecv` (`carOk`: `CloseSend`, then `RecvMsg` into a new message, on the raw
end, `carOk_of_raw`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.StreamDefs

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

/-- **The wrapped client end's `CloseAndRecv`** (persistent): closes the up queue after the requests
sent (`upClosed`), then receives the first response: its content (`Dn`), or an error (`io.EOF`'s
value, or a stream error). -/
def carOk {Req Rep : StreamMsg GF} (cs : GoInterface) (γ : StreamNames)
    (Md : GoString → GrpcMd → IProp GF) (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF)
    (E : GoInterface → IProp GF) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cs = GoInterface.ok ci⌝ ∗
    □ (∀ (L : List Req.M),
      {{ cliSendTok (Req := Req) γ L ∗ cliRecvTok (Rep := Rep) γ [] }}
        (App (Val #(methods ci.ty go!"CloseAndRecv" ci.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); upClosed (Req := Req) γ L ∗
          ((⌜err = GoInterface.nil⌝ ∗ ∃ (a : GoString) (md : GrpcMd) (m : Rep.M), Md a md ∗
              Rep.recv resp m ∗ Dn a md 0 m) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ (eofIs err ∨ cliStreamErr err E))) }}))

instance carOk_persistent {Req Rep : StreamMsg GF} (cs : GoInterface) (γ : StreamNames)
    (Md : GoString → GrpcMd → IProp GF) (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF)
    (E : GoInterface → IProp GF) : Persistent (carOk (Req := Req) (Rep := Rep) cs γ Md Dn E) := by
  unfold carOk; infer_instance

/-- **`CloseAndRecv` on the generated wrapper** of grpc's raw client end. -/
theorem carOk_of_raw [grpc_sem : google_golang_org.grpc.Assumptions]
    {Req Rep : StreamMsg GF} (V W : Type) [ZeroVal W]
    [TypedPointsto (GF := GF) W] [IntoValTyped (GF := GF) W Rep.ty] [TypeRepr Rep.ty W]
    [ZeroVal V] [TypeRepr Req.ty V]
    (p : Loc) (cs : GoInterface) (γ : StreamNames) (Up : Nat → Req.M → IProp GF)
    (Md : GoString → GrpcMd → IProp GF) (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF)
    (cd : context.ContextDesc (IProp GF)) (Ok : IProp GF → Prop) (E : GoInterface → IProp GF)
    (hOk : Ok iprop(True)) :
    structFieldRef (google_golang_org.grpc.GenericClientStream V W) go!"ClientStream" p ↦□ cs ∗
      cliStreamIs cs γ Req Rep Up Md Dn cd Ok E ∗ (□ ∀ l : Loc, l ↦ (zero_val W) -∗ Rep.own l) ⊢
    carOk (Req := Req) (Rep := Rep) (interface.mkOk (go.GoType.PointerType
      (google_golang_org.grpc.GenericClientStream.ty Req.ty Rep.ty)) #p) γ Md Dn E := by
  iintro ⟨#Hf, #Hraw, #Hown⟩
  unfold carOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro !> %L %Φ !> ⟨HSt, HRt⟩ HΦ
  wp_method_call
  try wp_call
  iunfold cliStreamIs at Hraw
  icases Hraw with ⟨%ci, %Hci, -, #HRecv, #HClose, -⟩
  subst Hci
  wp_auto
  wp_bind (App (Val #(methods ci.ty go!"CloseSend" ci.v)) _)
  iapply HClose $$ %L %iprop(True) [HSt]
  · isplitr
    · ipureintro; exact hOk
    isplitr
    · itrivial
    iexact HSt
  iintro !> %err ⟨-, #Hcl, Herr⟩
  icases Herr with (%He | #Hce)
  · subst He
    wp_auto
    ihave Hm := Hown $$ %«$r0_ptr» «$r0»
    wp_bind (App (Val #(methods ci.ty go!"RecvMsg" ci.v)) _)
    iapply HRecv $$ %[] %«$r0_ptr» %iprop(True) [HRt Hm]
    · isplitr
      · ipureintro; exact hOk
      isplitr
      · itrivial
      iframe
    iintro !> %err2 ⟨-, Hres⟩
    icases Hres with (⟨%He2, %a, %md, %m, HMd, -, Hrv, HDn, -⟩ | ⟨#Heof, %Hne, -, -, -⟩ |
      ⟨#Hce2, -, -⟩)
    · subst He2
      wp_auto
      iapply HΦ
      iframe Hcl
      ileft
      isplitr
      · ipureintro; rfl
      iexists a, md, m
      iframe
    · cases err2 with
      | nil => exact absurd rfl Hne
      | ok e =>
        wp_auto
        iapply HΦ
        iframe Hcl
        iright
        isplitr
        · ipureintro; exact Hne
        ileft
        iexact Heof
    · ihave #Hce2' := Hce2
      iunfold cliStreamErr at Hce2'
      icases Hce2' with ⟨%Hne, -⟩
      cases err2 with
      | nil => exact absurd rfl Hne.1
      | ok e =>
        wp_auto
        iapply HΦ
        iframe Hcl
        iright
        isplitr
        · ipureintro; exact Hne.1
        iright
        iexact Hce2
  · ihave #Hce' := Hce
    iunfold cliStreamErr at Hce'
    icases Hce' with ⟨%Hne, -⟩
    cases err with
    | nil => exact absurd rfl Hne.1
    | ok e =>
      wp_auto
      iapply HΦ
      iframe Hcl
      iright
      isplitr
      · ipureintro; exact Hne.1
      iright
      iexact Hce

end defs

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

end Perennial
