/- Lean-first (no Rocq counterpart).

# `svc.(*driverClient).Bidi`'s proof

As etcd's `watchClient.Watch`: `NewStream` with `Driver_ServiceDesc.Streams[2]` (`drvDescs`), the stream
wrapped (`cliBidiStreamIs_of_raw`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Bidi
public import Spec.google_golang_org.grpc.StaticMethod
public import Spec.google_golang_org.grpc.ClientConn__NewStream
public import Proof.google_golang_org.grpc.NewStreamNoIc
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

theorem driverClient.Bidi.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_NewStream : grpc.ClientConn.NewStream.spec (GF := GF) (hG := hG))
    (wp_Send : grpc.GenericClientStream.Send.spec (GF := GF) (hG := hG))
    (wp_Recv : grpc.GenericClientStream.Recv.spec (GF := GF) (hG := hG))
    (wp_CloseSend : grpc.GenericClientStream.CloseSend.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericClientStream.Context.spec (GF := GF) (hG := hG)) :
    driverClient.Bidi.spec (GF := GF) (hG := hG) := by
  intro dc conn addrs d Up Spec ctx cd om
  wp_start as ⟨#Hcc, #Hconn, #Hopts, %hnone, #Hstr, #Hctx, #Hom⟩
  ihave #Hsvc : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  ihave #Hd := drvDescs_of_init $$ Hsvc
  icases Hd with ⟨%mds, %sds, #Hdesc, %Hms⟩
  obtain ⟨-, hs⟩ := Hms
  iunfold go_etcd_io.etcd.cache.v3.pbDescIs at Hdesc
  icases Hdesc with ⟨%msl, %ssl, -, -, -, -, #HSs, #Hssl, -⟩
  have hlen : sds.length = 3 := by
    have := congrArg List.length hs
    simpa using this
  obtain ⟨sd0, hsd0n⟩ : ∃ sd0, sds[2]? = some sd0 :=
    ⟨sds[2]'(by omega), by simp⟩
  have hsd0 : sds[((2 : Nat) : Int).toNat]? = some sd0 := hsd0n
  have hmem : (sd0.StreamName', (#sd0.Handler' : val), sd0.ServerStreams', sd0.ClientStreams') =
      (sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams',
        sd.ClientStreams')))[2]'(by simp; omega) := by
    have he : sds[2]'(by omega) = sd0 := by
      have h := hsd0n
      rw [List.getElem?_eq_getElem (by omega)] at h
      exact Option.some.inj h
    rw [List.getElem_map, he]
  have hmem2 := hmem.trans (List.getElem_of_eq hs _)
  have h1 : sd0.ClientStreams' = true := (congrArg (fun p => p.2.2.2) hmem2).trans rfl
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
  ihave %Hdl := ownSlice_len ssl _ sds $$ Hssl
  have hb : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z ssl.len := by
    constructor
    · word
    · have := Hdl.1; word
  wp_auto
  simp only [hb, and_self, ↓reduceIte]
  ihave ⟨#Hd0, -⟩ := ownSlice_elem_acc ((2 : Nat) : Int) sd0 ssl _ sds (by omega) hsd0 $$ Hssl
  wp_auto
  wp_bind (App (App (App (App (Val _) _) _) _) _)
  ihave #Hok3 : iprop(streamCallOptsOk (GF := GF) ([sm] ++ [])) $$ []
  · unfold streamCallOptsOk
    simp only [List.append_nil]
    iapply BigSepL.bigSepL_singleton.2
    unfold streamCallOptOk
    ileft
    iexact Hsm
  have hNS := grpc.ClientConn.NewStreamNoIc_of wp_NewStream conn addrs [] anyRes d
    go!"/grpcdriver.Driver/Bidi" strmTT strmTT strmTT_reqReg
    strmTT_repReg Up Spec ctx cd om
  iapply (hNS _ copts ([sm] ++ []) iprop(True))
  · isplitr
    · iframe #
    isplitr
    · iframe #
    isplitr
    · iframe #
    isplitr
    · ipureintro; exact hnone
    isplitr
    · ipureintro; trivial
    isplitr
    · itrivial
    iframe #
    iexists _
    simp only [show sint.Z (W64 2) = ((2 : Nat) : Int) from rfl]
    iframe Hd0
    ipureintro; exact Or.inl h1
  inext
  iintro %cs %err ⟨-, Hres⟩
  wp_auto
  icases Hres with (⟨%Herr, %γ, %Dn, %cd', #Hcs, HSt, HRt, #HSpec⟩ | ⟨%Hcs, #Herr⟩)
  · subst Herr
    try wp_auto
    wp_alloc p as Hp
    iStructNamed Hp
    ipersist ClientStream
    have hReq : (strmT (GF := GF)).ty = wrapperspb.StringValue.ty := rfl
    have hI : IntoValTyped (GF := GF) wrapperspb.StringValue
        (strmT (GF := GF)).ty := hReq ▸ inferInstance
    have hT : TypeRepr (strmT (GF := GF)).ty wrapperspb.StringValue :=
      hReq ▸ inferInstance
    have hw := cliBidiStreamIs_of_raw (GF := GF) (Req := (strmT (GF := GF)))
      (Rep := (strmT (GF := GF))) wrapperspb.StringValue wrapperspb.StringValue
      wp_Send wp_Recv wp_CloseSend wp_Context p cs γ Up
      (fun a md => iprop(⌜a ∈ addrs⌝ ∗ streamAttemptMd conn (fun om om' => om' = om) om md)) Dn cd'
      anyRes (streamErrShape d)
    rw [hReq] at hw
    ihave #Hw := hw $$ [ClientStream]
    · iframe #
      iintro !> %l Hl
      simp only [strmT, pbStringValueS]
      iexists _
      iexact Hl
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists γ, Dn, cd'
    iframe Hw HSt HRt HSpec
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
