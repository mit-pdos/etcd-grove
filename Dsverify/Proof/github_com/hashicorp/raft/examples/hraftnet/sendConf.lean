/-
`hraftnet.sendConf`'s proof (vr's `wp_sendConf`, `vsrnet/ConfDefs.lean`, on one byte): `Dial`, the byte
of the drawn size written (`confProto`), one byte read back, `Close`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.sendConf

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

theorem sendConf.wp_proof (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    sendConf.spec (GF := GF) := by
  intro γc a n hn
  wp_start as ⟨#Hpr, #Hf⟩
  ihave ⟨%eof, %ueof, %ed, %Hev, #Heof, #Hue, #Hed⟩ := errs_init $$ Hpkg
  ihave %Hok := addrTok_ok a $$ [Hpr]
  · iapply addrProto_tok $$ Hpr
  wp_auto
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp a iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (confProto γc) ackProto [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
    as %cv %err (⟨%Herr, %cn, #Hc, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au a (confProto γc) ackProto $$ Hpr
  rotate_left
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  unfold net.isConn
  icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
  subst Hct
  iunfold connEnd at Hend
  icases Hend with ⟨Hs, Hrv⟩
  ihave #Hconn := sendTok_connIs cn false _ _ $$ Hs
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (n : Int)]
  wp_auto
  isplitl []
  · ipureintro
    have : n < 256 := by unfold N0Ok at hn; omega
    have h : (W8 (uint.Z (W64 (n : Int))) : w8) = W8 (n : Int) := by word
    rw [h]
  iintro %bsl ⟨Hb, -⟩
  wp_auto
  ihave #Hp0 : (□ confProto (GF := GF) γc cn ([] ++ [W8 (n : Int)])) $$ []
  · iintro !>
    unfold confProto
    iexists n
    iframe Hf
    ipureintro; exact ⟨List.prefix_refl _, hn⟩
  wp_apply wp_Write t cn false a la ra _ [W8 (n : Int)] _ ed
      (writeP (Gg := hG.goose_globalGS) cn false (confProto γc) [])
      $$ [Hb Hs] as %nw %werr ⟨%w, %res, Hs, Hb, %Hw, #HE⟩
  · iframe Hca Hb Hed
    isplitl [Hs]
    · iapply writeP_init $$ Hs
    · iapply write_acc cn false (confProto γc) [] _ $$ Hp0
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
  cases res with
  | some k =>
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_apply wp_closeConn wp_Close t cn false a la ra $$ [] as %e -
    · iframe Hca Hconn
    iapply HΦ; itrivial
  | none =>
  have := Hne.1 rfl
  subst this
  wp_auto
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hrd := net.conn_readerOk wp_Read t cn false a la ra eof ed ackProto $$ [$Hio $Hca $Heof $Hed]
  iunfold net.connIface at Hrd
  ihave Hrv := recvTok_L $$ Hrv
  ihave Hs2 := slice_array a_ptr 1 _ (by decide) $$ a
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 1 - W64 0) = W64 1 from rfl,
    show (zero_val (GoArray w8 1)).arr = [W8 0] from rfl]
  wp_apply io.wp_ReadFull ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩ (fun _ m => 0 < m)
      (recvTokL (Gg := hG.goose_globalGS) cn false ackProto) (net.connReadE eof la ra ed) []
      (slice.mk a_ptr (W64 1) (W64 1)) [W8 0] eof ueof
      $$ [Hrv Hs2] as %n2 %err2 ⟨%ys, %Hys, Hs2, Hrv, #Hres⟩
  · iframe Hrd Heof Hue Hrv Hs2; ipureintro; intro _ hl; simp only [List.length_cons, List.length_nil] at hl ⊢; omega
  iunfold io.readFullRes at Hres
  icases Hres with (%Hl | ⟨%e, %He, -⟩)
  rotate_left
  · have herr : err2 ≠ GoInterface.nil := by
      obtain ⟨-, hne, h1, h2⟩ := He
      by_cases hc : e = eof ∧ ys ≠ []
      · rw [h1 hc]; exact Hev.2
      · rw [h2 hc]; exact hne
    cases err2 with
    | nil => exact absurd rfl herr
    | ok i =>
    wp_auto
    wp_apply wp_closeConn wp_Close t cn false a la ra $$ [] as %e2 -
    · iframe Hca Hconn
    iapply HΦ; itrivial
  obtain ⟨hl, rfl⟩ := Hl
  obtain ⟨b2, rfl⟩ : ∃ b2, ys = [b2] := by
    match ys, hl with
    | [b2], _ => exact ⟨b2, rfl⟩
  rw [show List.drop [b2].length [W8 0] = [] from rfl, List.append_nil]
  wp_auto
  rw [show arrayIndexRef w8 (sint.Z (W64 0)) a_ptr =
    sliceIndexRef w8 (sint.Z (W64 0)) (slice.mk a_ptr (W64 1) (W64 1)) from rfl]
  wp_apply wp_load_slice_index _ _ [b2] _ b2 (by decide) $$ [$Hs2] as Hs2
  · ipureintro; rfl
  wp_if_destruct <;>
  · wp_apply wp_closeConn wp_Close t cn false a la ra $$ [] as %e2 -
    · iframe Hca Hconn
    iapply HΦ; itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
