/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/leaseClient__LeaseKeepAlive.lean` (item 1, the client
lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.leaseClient__LeaseKeepAlive
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

theorem leaseClient.LeaseKeepAlive.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_NewStream : grpc.ClientConn.NewStream.spec (GF := GF) (hG := hG))
    (wp_Send : grpc.GenericClientStream.Send.spec (GF := GF) (hG := hG))
    (wp_Recv : grpc.GenericClientStream.Recv.spec (GF := GF) (hG := hG))
    (wp_CloseSend : grpc.GenericClientStream.CloseSend.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericClientStream.Context.spec (GF := GF) (hG := hG)) :
    leaseClient.LeaseKeepAlive.spec (GF := GF) (hG := hG) := by
  intro wc conn addr ctx cd opts vs
  wp_start as ⟨#Hstub, #Hconn, #Hstr0, #Hdesc, #Hctx, #Hopts, #Hok⟩
  iunfold isEtcdConn at Hconn
  icases Hconn with ⟨%ic, #Hgc, -⟩
  iunfold leaseKAStreamOk at Hstr0
  icases Hstr0 with ⟨%Spec, #Hstr⟩
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
  ihave #Hs1' := streamCallOptsOk_of [sm] $$ Hs1
  ihave #Hok2 := streamCallOptsOk_app [sm] vs $$ [Hs1' Hok]
  · iframe #
  iunfold leaseDescOk at Hdesc
  icases Hdesc with ⟨%dsl, %sds, #Hdsl, #Hsds, %Hlen⟩
  iunfold leaseStubAt at Hstub
  wp_auto
  ihave %Hdl := ownSlice_len dsl _ sds $$ Hsds
  obtain ⟨sd0, hsd0⟩ : ∃ sd0, sds[(0 : Int).toNat]? = some sd0 := by
    cases sds with
    | nil => simp at Hlen
    | cons x _ => exact ⟨x, rfl⟩
  have hcs : sd0.ClientStreams' = true := by
    cases sds with
    | nil => simp at Hlen
    | cons x _ =>
      simp at hsd0 Hlen
      subst hsd0; exact Hlen.1
  have hlen1 : 0 < sds.length := by
    cases sds with
    | nil => simp at Hlen
    | cons _ _ => simp
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z dsl.len := by
    constructor
    · word
    · have := Hdl.1; word
  simp only [hb, _root_.and_self, ↓reduceIte]
  ihave ⟨#Hd0, -⟩ := ownSlice_elem_acc (0 : Int) sd0 dsl _ sds (by omega) hsd0 $$ Hsds
  wp_auto
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  wp_bind (App (App (App (App (Val _) _) _) _) _)
  -- (D32) the one-address case
  iapply (wp_NewStream conn [addr] [ic] go!"/etcdserverpb.Lease/LeaseKeepAlive"
    pbLeaseKeepAliveRequest pbLeaseKeepAliveResponse (fun _ _ _ => iprop(True)) (fun _ _ => Spec)
    ctx cd _ copts ([sm] ++ vs))
  · iframe #
    iexists _
    simp only [show sint.Z (W64 0) = 0 from rfl]
    iframe Hd0
    ipureintro; exact hcs
  inext
  iintro %cs %err Hres
  wp_auto
  icases Hres with (⟨%Herr, %a, %γ, %Dn, %cd', %md, -, #Hcs, HSt, HRt, HSpec⟩ | ⟨%Hcs, #Herr⟩)
  · subst Herr
    iapply wp_fupd
    wp_auto
    iStructNamed «$r0»
    ipersist ClientStream
    ihave #Hw := cliBidiStreamIs_of_raw (GF := GF) (Req := pbLeaseKeepAliveRequest)
      (Rep := pbLeaseKeepAliveResponse) etcdserverpb.LeaseKeepAliveRequest etcdserverpb.LeaseKeepAliveResponse
      wp_Send wp_Recv wp_CloseSend wp_Context «$r0_ptr» cs γ (fun _ _ => iprop(True)) Dn cd' $$ [ClientStream]
    · iframe #
      iintro !> %l Hl
      iexists _
      iexact Hl
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists γ, Dn, cd'
    iframe
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
