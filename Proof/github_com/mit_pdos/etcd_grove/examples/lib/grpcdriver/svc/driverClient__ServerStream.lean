/- Lean-first (no Rocq counterpart).

# `svc.(*driverClient).ServerStream`'s proof

As etcd's `watchClient.Watch`: `NewStream` with `Driver_ServiceDesc.Streams[0]` (`drvDescs`), the stream
wrapped (`cliBidiStreamIs_of_raw`); then the request sent and the up queue closed on the raw end.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__ServerStream
public import Spec.google_golang_org.grpc.StaticMethod
public import Spec.google_golang_org.grpc.ClientConn__NewStream
public import Spec.google_golang_org.grpc.GenericClientStream__Send
public import Spec.google_golang_org.grpc.GenericClientStream__Recv
public import Spec.google_golang_org.grpc.GenericClientStream__CloseSend
public import Spec.google_golang_org.grpc.GenericClientStream__Context
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove
  google_golang_org.protobuf.types.known

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem driverClient.ServerStream.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_NewStream : grpc.ClientConn.NewStream.spec (GF := GF) (hG := hG))
    (wp_Send : grpc.GenericClientStream.Send.spec (GF := GF) (hG := hG))
    (wp_Recv : grpc.GenericClientStream.Recv.spec (GF := GF) (hG := hG))
    (wp_CloseSend : grpc.GenericClientStream.CloseSend.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericClientStream.Context.spec (GF := GF) (hG := hG)) :
    driverClient.ServerStream.spec (GF := GF) (hG := hG) := by
  intro dc conn addrs d Up Spec ctx cd om inp v
  wp_start as ⟨#Hcc, #Hconn, #Hopts, %hnone, #Hstr, #Hctx, #Hom, Hinp, HUp⟩
  ihave #Hsvc : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  ihave #Hd := drvDescs_of_init $$ Hsvc
  icases Hd with ⟨%mds, %sds, #Hdesc, %Hms⟩
  obtain ⟨-, hs⟩ := Hms
  iunfold go_etcd_io.etcd.cache.v3.pbDescIs at Hdesc
  icases Hdesc with ⟨%msl, %ssl, -, -, -, -, #HSs, #Hssl⟩
  have hlen : sds.length = 3 := by
    have := congrArg List.length hs
    simpa using this
  obtain ⟨sd0, hsd0n⟩ : ∃ sd0, sds[0]? = some sd0 :=
    ⟨sds[0]'(by omega), by simp⟩
  have hsd0 : sds[((0 : Nat) : Int).toNat]? = some sd0 := hsd0n
  have hmem : (sd0.StreamName', (#sd0.Handler' : val), sd0.ServerStreams', sd0.ClientStreams') =
      (sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams',
        sd.ClientStreams')))[0]'(by simp; omega) := by
    simp [hsd0n]
  have hmem2 := hmem.trans (List.getElem_of_eq hs _)
  have h1 : sd0.ServerStreams' = true := (congrArg (fun p => p.2.2.1) hmem2).trans rfl
  wp_auto
  wp_apply wp_StaticMethod as %sm ⟨#Hsm, %Hsms⟩
  wp_apply wp_slice_literal (V := GoInterface) [sm]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, Hcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap] as %copts ⟨Hco, Hcocap, -⟩
  · iapply (ownSlice_nil (V := GoInterface) DFrac.discard)
  ipersist Hco
  ihave #Hs1 := callOptsOk_singleton sm $$ Hsm
  ihave %Hdl := ownSlice_len ssl _ sds $$ Hssl
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ssl.len := by
    constructor
    · word
    · have := Hdl.1; word
  wp_auto
  simp only [hb, and_self, ↓reduceIte]
  ihave ⟨#Hd0, -⟩ := ownSlice_elem_acc ((0 : Nat) : Int) sd0 ssl _ sds (by omega) hsd0 $$ Hssl
  wp_auto
  wp_bind (App (App (App (App (Val _) _) _) _) _)
  ihave #Hok3 := streamCallOptsOk_of ([sm] ++ []) $$ [Hs1]
  · simp only [List.append_nil]; iexact Hs1
  have hNS := wp_NewStream conn addrs [] anyRes d (fun om om' => om' = om)
    go!"/grpcdriver.Driver/ServerStream" pbStringValueST pbStringValueST pbStringValueST_reqReg
    pbStringValueST_repReg Up Spec ctx cd om
  iapply (hNS _ copts ([sm] ++ []) iprop(True))
  · isplitr
    · iframe #
    isplitr
    · iframe #
    isplitr
    · iframe #
    isplitr
    · ipureintro; exact Or.inl ⟨hnone, fun _ _ => Iff.rfl⟩
    isplitr
    · ipureintro; trivial
    isplitr
    · itrivial
    iframe #
    iexists _
    simp only [show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl]
    iframe Hd0
    ipureintro; exact Or.inr ⟨h1, hnone⟩
  inext
  iintro %cs %err ⟨-, Hres⟩
  wp_auto
  icases Hres with (⟨%Herr, %γ, %Dn, %cd', #Hcs, HSt, HRt, #HSpec⟩ | ⟨%Hcs, #Herr⟩)
  · subst Herr
    wp_auto
    iStructNamed «$r0»
    ipersist ClientStream
    ihave #Hw := cliBidiStreamIs_of_raw (GF := GF) (Req := (pbStringValueST (GF := GF)).toStreamMsg)
      (Rep := (pbStringValueST (GF := GF)).toStreamMsg) wrapperspb.StringValue wrapperspb.StringValue
      wp_Send wp_Recv wp_CloseSend wp_Context «$r0_ptr» cs γ Up
      (fun a md => iprop(⌜a ∈ addrs⌝ ∗ streamAttemptMd conn (fun om om' => om' = om) om md)) Dn cd'
      anyRes (streamErrShape d) $$ [ClientStream]
    · iframe #
      iintro !> %l Hl
      iexists _
      iexact Hl
    -- the request, then the end of the up queue
    iunfold cliStreamIs at Hcs
    icases Hcs with ⟨%ci, %Hci, #HSend, -, #HClose, -⟩
    subst Hci
    try wp_auto
    iunfold stringValueSend at Hinp
    iunfold stringValueSendB at Hinp
    icases Hinp with ⟨%sv, Hsv, %Hsvp⟩
    have hwl : (pbStringValueST (GF := GF)).wireLen v < grpcMsgMax := by
      have h := Hsvp.2.2
      simp only [pbStringValueST, pbStringValueS, stringValueWireLen, grpcMsgMax]
      simp only [stringValueMax] at h
      omega
    ihave Hinp : iprop((pbStringValueST (GF := GF)).send inp v) $$ [Hsv]
    · simp only [pbStringValueST, pbStringValueS, stringValueSend, stringValueSendB]
      iexists sv
      iframe
      ipureintro; exact Hsvp
    have hty : msgAny (pbStringValueST (GF := GF)).ty inp =
        interface.mkOk (go.GoType.PointerType Msg.ty) #inp := rfl
    rw [← hty]
    wp_bind (App (Val #(methods ci.ty go!"SendMsg" ci.v)) _)
    iapply HSend $$ %([] : List (pbStringValueST (GF := GF)).M) %inp %v %iprop(True) [HSt Hinp HUp]
    · isplitr
      · ipureintro; trivial
      isplitr
      · itrivial
      iframe
      ipureintro; exact hwl
    iintro !> %err1 ⟨-, -, Hres1⟩
    icases Hres1 with (⟨%He1, HSt⟩ | ⟨#Hce1, -⟩)
    · subst He1
      wp_auto
      iunfold cliSendTok at HSt
      ihave #Hlb := monoListLbOwn_get γ.up (1 : Qp).half [v] $$ HSt
      ihave HSt : iprop(cliSendTok (Req := (pbStringValueST (GF := GF)).toStreamMsg) γ [v]) $$ [HSt]
      · iunfold cliSendTok; iexact HSt
      wp_bind (App (Val #(methods ci.ty go!"CloseSend" ci.v)) _)
      iapply HClose $$ %([v] : List (pbStringValueST (GF := GF)).M) %iprop(True) [HSt]
      · isplitr
        · ipureintro; trivial
        isplitr
        · itrivial
        iexact HSt
      iintro !> %err2 ⟨-, #Hcl, Hres2⟩
      icases Hres2 with (%He2 | #Hce2)
      · subst He2
        wp_auto
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists γ, Dn, cd'
        iframe Hw HRt HSpec Hcl
        unfold upLb
        iexact Hlb
      · ihave #Hce2' := Hce2
        iunfold cliStreamErr at Hce2'
        icases Hce2' with ⟨%Hne, -⟩
        cases err2 with
        | nil => exact absurd rfl Hne.1
        | ok ei =>
          wp_auto
          iapply HΦ
          iright
          iframe #
          ipureintro; rfl
    · ihave #Hce1' := Hce1
      iunfold cliStreamErr at Hce1'
      icases Hce1' with ⟨%Hne, -⟩
      cases err1 with
      | nil => exact absurd rfl Hne.1
      | ok ei =>
        wp_auto
        iapply HΦ
        iright
        iframe #
        ipureintro; rfl
  · ihave #Herr' := Herr
    iunfold cliStreamErr at Herr'
    icases Herr' with ⟨%Hne, -⟩
    subst Hcs
    cases err with
    | nil => exact absurd rfl Hne.1
    | ok ei =>
      wp_auto
      iapply HΦ
      iright
      iframe #
      ipureintro; rfl

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
