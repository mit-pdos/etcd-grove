/-
The probe's client node (`harness/netprobe/netprobe.go`): `check`, `Ping`, `ClientMain`.
-/
module

public import Harness.Proof.dsverify_lab.harness.netprobe.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace dsverify_lab.harness.netprobe

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : netprobe.Assumptions] [model_sem : net.model.Assumptions]

set_option goose.wp.extras true

/-- `check(msg, got)` does not panic when `got` is a prefix of `msg`. -/
theorem wp_check (ms gs : GoSlice) (m g : List w8) (dq1 dq2 : DFrac) (hp : g <+: m) :
    {{ (ms ↦*{dq1} m ∗ gs ↦*{dq2} g : IProp GF) }}
      (App (App (Val (@! check)) (Val #ms)) (Val #gs))
    {{ RET #(); True }} := by
  wp_start as ⟨Hm, Hg⟩
  ihave %Hml := ownSlice_len _ _ _ $$ Hm
  ihave %Hgl := ownSlice_len _ _ _ $$ Hg
  have hle := hp.length_le
  wp_auto
  wp_if_destruct
  · exfalso; word
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z gs.len⌝ :
      IProp GF) $$ [i]
  · iexists W64 0; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hjg : (sint.Z j).toNat < g.length := by
      rw [Hgl.1]; show (sint.Z j).toNat < (sint.Z gs.len).toNat; omega
    have hjm : (sint.Z j).toNat < m.length := by omega
    have hb1 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z gs.len := ⟨Hj.1, Hif⟩
    have hb2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ms.len := ⟨Hj.1, by word⟩
    rw [ite_eq_left hb1]
    wp_apply wp_load_slice_index gs (sint.Z j) g _ (g[(sint.Z j).toNat]) Hj.1 $$ [$Hg] as Hg
    · ipureintro; simp
    rw [ite_eq_left hb2]
    wp_apply wp_load_slice_index ms (sint.Z j) m _ (m[(sint.Z j).toNat]) Hj.1 $$ [$Hm] as Hm
    · ipureintro; simp
    have heq : g[(sint.Z j).toNat] = m[(sint.Z j).toNat] := by
      obtain ⟨t, rfl⟩ := hp
      simp [List.getElem_append_left hjg]
    rw [heq]
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    ipureintro; clear hjg hjm heq; word
  · iapply HΦ; itrivial

/-- An early return of `Ping`: nothing received. -/
theorem ping_nil (ms : GoSlice) (dq : DFrac) :
    (ms ↦*{dq} msg : IProp GF) ⊢ ∃ g : List w8, slice.nil ↦* g ∗ ⌜g <+: msg⌝ ∗ ms ↦*{dq} msg := by
  iintro Hm; iexists []; iframe Hm; isplitl; · iapply ownSlice_nil
  ipureintro; exact List.nil_prefix

/-- `Ping(a, msg)`, for an address whose protocols are `echoProto`: it returns a prefix of `msg`
(all of it, part of it, or nothing). -/
theorem wp_Ping (a : GoString) (ms : GoSlice) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe ∗
        addrProto a echoProto echoProto ∗ ms ↦*{dq} msg }}
      (App (App (Val (@! Ping)) (Val #a)) (Val #ms))
    {{ (gs : GoSlice), RET #gs; ∃ g : List w8, gs ↦* g ∗ ⌜g <+: msg⌝ ∗ ms ↦*{dq} msg }} := by
  wp_start as ⟨#Hpr, Hm⟩
  ihave #Hnet := net_init_of_pkg $$ Hpkg
  wp_auto
  wp_apply net.DialTimeout.wp_proof a _ echoProto echoProto $$ [$Hnet $Hpr] as %cv %err Hres
  unfold net.newConnResult
  icases Hres with (⟨%c, %cid, %Hcv, #Hc, ⟨Hsend, Hrecv⟩, -⟩ | ⟨%i, %Hcv, -⟩) <;>
    obtain ⟨rfl, rfl⟩ := Hcv
  rotate_left
  · wp_auto; iapply HΦ; iapply ping_nil $$ Hm
  wp_auto
  wp_apply time.wp_Now as %t -
  wp_apply time.Time.wp_Add t _ as %t1 -
  wp_apply net.TCPConn.SetWriteDeadline.wp_proof c cid false t1 $$ [$Hnet $Hc] as %err -
  rcases err with ei | _
  · wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid false $$ [$Hnet $Hc] as %err2 -
    iapply HΦ; iapply ping_nil $$ Hm
  wp_auto
  ihave #Hp0 : (□ echoProto (GF := GF) cid ([] ++ msg) : IProp GF) $$ []
  · iintro !>; unfold echoProto; ipureintro; exact List.prefix_refl _
  wp_apply net.TCPConn.Write.wp_proof c cid false ms msg dq echoProto [] $$ [$Hnet $Hc $Hsend $Hp0 $Hm]
    as %nw %err ⟨%k, %code, %Hk, Hm, Hsend, -⟩
  rcases err with ei | _
  · wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid false $$ [$Hnet $Hc] as %err2 -
    iapply HΦ; iapply ping_nil $$ Hm
  wp_auto
  wp_apply time.wp_Now as %t2 -
  wp_apply time.Time.wp_Add t2 _ as %t3 -
  wp_apply net.TCPConn.SetReadDeadline.wp_proof c cid false t3 $$ [$Hnet $Hc] as %err -
  rcases err with ei | _
  · wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid false $$ [$Hnet $Hc] as %err2 -
    iapply HΦ; iapply ping_nil $$ Hm
  ihave %Hml := ownSlice_len _ _ _ $$ Hm
  wp_auto
  wp_apply (wp_slice_make3 (V := w8) (W64 0) ms.len (by constructor <;> word)) as %gs0 ⟨Hg, Hgcap, -⟩
  wp_apply (wp_slice_make2 (V := w8) (W64 64)) as %bs0 ⟨Hb, -⟩
  · ipureintro; decide
  ihave HI : (∃ (gsl : GoSlice) (g bs : List w8),
      "got" ∷ got_ptr ↦ gsl ∗ "Hg" ∷ gsl ↦* g ∗ "Hgcap" ∷ ownSliceCap w8 gsl (DFrac.own 1) ∗
      "Hrecv" ∷ recvTok cid false echoProto g ∗ "%Hgp" ∷ ⌜g <+: msg⌝ ∗
      "Hb" ∷ bs0 ↦* bs : IProp GF) $$ [got Hg Hgcap Hrecv Hb]
  · iexists gs0, [], _
    iframe
    ipureintro; exact List.nil_prefix
  wp_for HI
  wp_if_destruct
  · wp_apply net.TCPConn.Read.wp_proof c cid false bs0 bs echoProto g $$ [$Hnet $Hc $Hrecv $Hb]
      as %n %err ⟨%data, %code2, %Hd, Hb, Hrecv, -⟩
    ihave ⟨Hrecv, #Hp⟩ := recvTok_proto_closed echoProto_closed $$ Hrecv
    unfold echoProto; icases Hp with %Hgp'
    obtain ⟨rfl, -⟩ := Hd
    ihave ⟨%hb, Hpre, Hback⟩ := ownSlice_take_acc bs0 _ data _ $$ Hb
    rw [ite_eq_left hb.1]
    wp_auto
    wp_apply wp_slice_append (V := w8) gsl g _ data (DFrac.own 1) $$ [$Hg $Hgcap $Hpre]
      as %gs' ⟨Hg, Hgcap, Hpre⟩
    ihave Hb := Hback $$ Hpre
    rcases err with ei | _
    · wp_auto
      wp_for_post
      wp_apply net.TCPConn.Close.wp_proof c cid false $$ [$Hnet $Hc] as %err2 -
      iapply HΦ
      iexists g ++ data
      iframe
      ipureintro; exact Hgp'
    · wp_auto
      wp_for_post
      iframe
      iexists gs', g ++ data, _
      iframe
      ipureintro; exact Hgp'
  wp_apply net.TCPConn.Close.wp_proof c cid false $$ [$Hnet $Hc] as %err2 -
  iapply HΦ
  iexists g
  iframe
  ipureintro; exact Hgp

/-- The client node's program: with the protocols of the server's address, it does not panic
(its `check` passes). -/
theorem wp_ClientMain :
    {{ isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe ∗
        addrProto serverAddr echoProto echoProto }}
      (App (Val (@! ClientMain)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as #Hpr
  wp_apply wp_string_to_bytes as %ms ⟨Hm, -⟩
  wp_apply wp_Ping serverAddr ms (DFrac.own 1) $$ [$Hpkg $Hpr $Hm] as %gs ⟨%g, Hg, %Hgp, Hm⟩
  wp_apply wp_check ms gs msg g (DFrac.own 1) (DFrac.own 1) Hgp $$ [$Hm $Hg]
  iapply HΦ; itrivial

end proofs

end dsverify_lab.harness.netprobe

end Perennial
