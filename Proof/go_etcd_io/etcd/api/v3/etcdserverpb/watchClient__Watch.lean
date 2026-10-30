/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/watchClient__Watch.lean` (unit W-W).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.watchClient__Watch
public import Spec.google_golang_org.grpc.StaticMethod
public import Spec.google_golang_org.grpc.ClientConn__NewStream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem watchClient.Watch.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_NewStream : grpc.ClientConn.NewStream.spec (GF := GF) (hG := hG))
    (wp_Send : grpc.GenericClientStream.Send.spec (GF := GF) (hG := hG))
    (wp_Recv : grpc.GenericClientStream.Recv.spec (GF := GF) (hG := hG))
    (wp_CloseSend : grpc.GenericClientStream.CloseSend.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericClientStream.Context.spec (GF := GF) (hG := hG)) :
    watchClient.Watch.spec (GF := GF) (hG := hG) := by
  intro wc conn addrs ics Up Spec ctx cd opts vs
  wp_start as ⟨#Hstub, #Hconn, #Hstr, #Hdesc, #Hctx, #Hopts, #Hok⟩
  wp_auto
  wp_apply wp_StaticMethod as %sm ⟨#Hsm, %Hsms⟩
  wp_apply wp_slice_literal (V := GoInterface) [sm]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, Hcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hopts] as %copts ⟨Hco, Hcocap, -⟩
  ipersist Hco
  ihave #Hs1 := callOptsOk_singleton sm $$ Hsm
  ihave #Hok2 := callOptsOk_app [sm] vs $$ [Hs1 Hok]
  · iframe #
  iunfold v3rpc.watchDescOk at Hdesc
  icases Hdesc with ⟨%dsl, %sds, #Hdsl, #Hsds, %Hlen⟩
  iunfold v3rpc.watchStubAt at Hstub
  wp_auto
  ihave %Hdl := ownSlice_len dsl _ sds $$ Hsds
  obtain ⟨sd0, hsd0⟩ : ∃ sd0, sds[(0 : Int).toNat]? = some sd0 := by
    cases sds with
    | nil => simp at Hlen
    | cons x _ => exact ⟨x, rfl⟩
  have hcs : sd0.ClientStreams' = true := Hlen.2 sd0 hsd0
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z dsl.len := by
    constructor
    · word
    · have := Hdl.1; word
  simp only [hb, and_self, ↓reduceIte]
  ihave ⟨#Hd0, -⟩ := ownSlice_elem_acc (0 : Int) sd0 dsl _ sds (by omega) hsd0 $$ Hsds
  wp_auto
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  wp_bind (App (App (App (App (Val _) _) _) _) _)
  ihave #Hok3 := streamCallOptsOk_of ([sm] ++ vs) $$ Hok2
  iapply (wp_NewStream conn addrs ics go!"/etcdserverpb.Watch/Watch" v3rpc.pbWatchRequest
    v3rpc.pbWatchResponse Up Spec ctx cd _ copts ([sm] ++ vs))
  · iframe #
    iexists _
    simp only [show sint.Z (W64 0) = 0 from rfl]
    iframe Hd0
    ipureintro; exact hcs
  inext
  iintro %cs %err Hres
  wp_auto
  icases Hres with (⟨%Herr, %a, %γ, %Dn, %cd', %md, %Ha, #Hcs, HSt, HRt, HSpec⟩ | ⟨%Hcs, #Herr⟩)
  · subst Herr
    iapply wp_fupd
    wp_auto
    iStructNamed «$r0»
    ipersist ClientStream
    ihave #Hw := cliBidiStreamIs_of_raw (GF := GF) (Req := v3rpc.pbWatchRequest)
      (Rep := v3rpc.pbWatchResponse) etcdserverpb.WatchRequest etcdserverpb.WatchResponse
      wp_Send wp_Recv wp_CloseSend wp_Context «$r0_ptr» cs γ (Up a) Dn cd' $$ [ClientStream]
    · iframe #
      iintro !> %l Hl
      iexists _
      iexact Hl
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists a, γ, Dn, cd', md
    iframe
    isplitr
    · ipureintro; exact Ha
    iexact Hw
  · ihave #Herr' := Herr
    iunfold cliStreamErr at Herr'
    icases Herr' with ⟨%Hne, -, -⟩
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

end EtcdGrove
end Perennial
