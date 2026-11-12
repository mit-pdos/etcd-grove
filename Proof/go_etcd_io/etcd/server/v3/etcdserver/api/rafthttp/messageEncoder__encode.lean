/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/messageEncoder__encode.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageEncoder__encode
public import Spec.google_golang_org.protobuf.proto.SizePb
public import Spec.encoding.binary.WriteUint64
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.messageEncoder.encode.wp_proof
    (wp_Size : proto.SizePb.spec (GF := GF) (hG := hG))
    (wp_WriteUint64 : binary.WriteUint64.spec (GF := GF) (hG := hG))
    (wp_MustMarshalMessage : pbutil.MustMarshalMessage.spec (GF := GF) (hG := hG)) :
    rafthttp.messageEncoder.encode.spec (GF := GF) (hG := hG) := by
  intro enc wi ml st Wr A h nf hm
  have wpS := wp_Size pbMessage ml st
  simp only [pbMessage_ty, pbMessage_ro] at wpS
  wp_start as ⟨#Hw, #Hwr, HWr, #Hm, #HA⟩
  iunfold writerAtF at Hwr
  wp_auto
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave %Hbe := bigEndian_ne_null $$ Hbin
  wp_apply (encoding.binary.wp_load_struct_nofields (V := encoding.binary.bigEndian)
    (globalAddr encoding.binary.BigEndian) Hbe)
  iintro -
  wp_auto
  wp_apply wpS $$ [$Hm] as %n ⟨%Hn, %Hwire⟩
  have Hw0 := Hwire hm
  simp only [pbMessage_wire] at Hw0
  have hlen : (pbEnc raftpb.Message.ty ml).length < 2 ^ 63 := by word
  have hn : n = W64 (pbEnc raftpb.Message.ty ml).length := by word
  subst hn
  have Hw0' : MsgWireOk st (pbEnc raftpb.Message.ty ml) ∧
      (pbEnc raftpb.Message.ty ml).length < 2 ^ 63 := ⟨Hw0, hlen⟩
  ihave ⟨#HA1, #HA2⟩ := HA $$ %(pbEnc raftpb.Message.ty ml) %Hw0'
  ihave Hbw := wp_WriteUint64 wi (W64 (pbEnc raftpb.Message.ty ml).length) iprop(Wr h)
    (fun n' err => iprop(∃ k : Nat,
      Wr (h ++ (u64Be (W64 (pbEnc raftpb.Message.ty ml).length)).take k) ∗
      ⌜sint.Z n' = k ∧ k ≤ 8 ∧ (err = GoInterface.nil → k = 8)⌝ ∗ http.errStrOk err ∗
      ⌜nf = true → err = GoInterface.nil⌝)) $$ []
  · iintro !> %sl !> %Φ ⟨Hsl, HWr⟩ HΦ
    wp_apply Hwr $$ %sl %(DFrac.own 1) %(u64Be (W64 (pbEnc raftpb.Message.ty ml).length)) %h
      [$Hsl $HWr $HA1] as %n' %err ⟨%k, Hsl, HWr, %Hk, #Herr, %Hnf⟩
    iapply HΦ
    iexists k
    iframe
    iframe #
    ipureintro
    simp only [u64Be_length] at Hk
    exact ⟨Hk, Hnf⟩
  wp_apply Hbw $$ [$HWr] as %err ⟨%n', %k, HWr, %Hk, #Herr, %Hnf⟩
  cases err with
  | ok ei =>
    wp_auto
    iapply HΦ
    isplitr
    · first | iapply http.errStrOk_nil | iassumption
    isplitr
    · ipureintro; exact Hnf
    iexists _
    iframe HWr
    iintro %Hnil
    cases Hnil
  | nil =>
    have hk : k = 8 := Hk.2.2 rfl
    wp_auto
    subst hk
    rw [List.take_of_length_le (by simp [u64Be_length])] at *
    have wpM := wp_MustMarshalMessage pbMessage ml st hm
    simp only [pbMessage_ty, pbMessage_ro, pbMessage_wire] at wpM
    wp_apply wpM $$ [$Hm] as %d ⟨Hd, Hcap, -⟩
    (try wp_auto)
    ihave #HA3 : □ A ((h ++ u64Be (W64 (pbEnc raftpb.Message.ty ml).length)) ++
        pbEnc raftpb.Message.ty ml) $$ []
    · iunfold msgFrame at HA2
      rw [List.append_assoc]; imodintro; iexact HA2
    wp_apply Hwr $$ %d %(DFrac.own 1) %(pbEnc raftpb.Message.ty ml)
      %(h ++ u64Be (W64 (pbEnc raftpb.Message.ty ml).length)) [$Hd $HWr $HA3]
      as %n2 %err2 ⟨%k2, Hd, HWr, %Hk2, #Herr, %Hnf2⟩
    (try wp_auto)
    iapply HΦ
    isplitr
    · first | iapply http.errStrOk_nil | iassumption
    isplitr
    · ipureintro; exact Hnf2
    iexists _
    iframe HWr
    iintro %Hnil
    iexists (pbEnc raftpb.Message.ty ml)
    ipureintro
    refine ⟨Hw0, hlen, ?_⟩
    rw [List.take_of_length_le (by rw [Hk2.2.2 Hnil]; exact Nat.le_refl _)]
    simp [msgFrame]

end proof

end EtcdGrove
end Perennial
