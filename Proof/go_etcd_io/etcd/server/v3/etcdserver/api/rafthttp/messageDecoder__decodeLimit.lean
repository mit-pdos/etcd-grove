/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/messageDecoder__decodeLimit.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder__decodeLimit
public import Spec.google_golang_org.protobuf.proto.UnmarshalPb
public import Spec.encoding.binary.ReadUint64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.messageDecoder.decodeLimit.wp_proof
    (wp_ReadUint64 : binary.ReadUint64.spec (GF := GF) (hG := hG))
    (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    rafthttp.messageDecoder.decodeLimit.spec (GF := GF) (hG := hG) := by
  intro dec r Rd B rs numBytes hnum
  wp_start as ⟨#Hr, #Hrf, HRd⟩
  iunfold readFullAt at Hrf
  wp_auto
  wp_apply (encoding.binary.wp_load_struct_nofields (V := encoding.binary.bigEndian)
    (globalAddr encoding.binary.BigEndian))
  iintro -
  wp_auto
  ihave Hbr := wp_ReadUint64 r l_ptr _ iprop(Rd rs)
    (fun ys _ _ => iprop(Rd (rs ++ ys) ∗ □ B (rs ++ ys))) $$ []
  · iintro !> %sl %xs !> %Φ ⟨Hsl, %Hxs, HRd⟩ HΦ
    wp_apply Hrf $$ %sl %xs %rs [$Hsl $HRd] as %n %err ⟨%ys, Hsl, HRd, #HB, %Hys⟩
    iapply HΦ
    iexists ys
    iframe Hsl HRd HB
    ipureintro
    exact ⟨by omega, fun h => by have := Hys.2.2 h; omega⟩
  wp_apply Hbr $$ [$HRd $l] as %err ⟨%ys, %n, ⟨HRd, #HB⟩, Hl⟩
  icases Hl with (⟨%Hok, Hl⟩ | ⟨%Herr, %x', Hl⟩)
  · obtain ⟨rfl, hlen⟩ := Hok
    wp_auto
    wp_if_destruct
    · ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      icases Hei with ⟨%e, #He⟩
      wp_auto
      iapply HΦ
      iexists _
      iframe HRd
      iintro %h
      cases h
    · wp_apply wp_slice_make2 (V := w8) $$ [] as %buf ⟨Hbuf, -⟩
      · ipureintro; word
      (try wp_auto)
      wp_apply Hrf $$ %buf %(List.replicate (sint.nat (beToU64 ys)) (zero_val w8)) %(rs ++ ys)
        [$Hbuf $HRd] as %n2 %err2 ⟨%ys2, Hbuf, HRd, #HB2, %Hys2⟩
      cases err2 with
      | ok ei =>
        wp_auto
        iapply HΦ
        iexists _
        iframe HRd
        iintro %h
        cases h
      | nil =>
        have hl2 : ys2.length = sint.nat (beToU64 ys) := by simpa using Hys2.2.2 rfl
        have hd : List.drop ys2.length (List.replicate (sint.nat (beToU64 ys)) (zero_val w8)) = [] := by
          simp [hl2]
        rw [hd, List.append_nil]
        wp_auto
        have wpU := wp_Unmarshal pbMessage buf ys2 (DFrac.own 1) m_ptr
        simp only [pbMessage_ty, pbMessage_blank, pbMessage_dec, pbMessage_wire] at wpU
        wp_apply wpU $$ [$Hbuf $m] as %err3 ⟨Hbuf, Hdec⟩
        (try wp_auto)
        iapply HΦ
        iexists _
        iframe HRd
        iintro %Hnil
        ihave ⟨%st, Hm, %Hw⟩ := Hdec $$ %Hnil
        iexists ys2, st
        iframe Hm HB2
        ipureintro
        have hys : u64Be (beToU64 ys) = ys := by
          unfold u64Be beToU64
          rw [leToU64_le _ (by simp [hlen]), List.reverse_reverse]
        have hW : W64 (ys2.length : Int) = beToU64 ys := by
          rw [hl2]; word
        refine ⟨?_, ?_, Hw⟩
        · simp only [msgFrame, hW, hys, List.append_assoc]
        · rw [hl2]; word
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      iexists _
      iframe HRd
      iintro %h
      cases h

end proof

end EtcdGrove
end Perennial
